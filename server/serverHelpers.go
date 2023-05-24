package main

import (
	"crypto/rand"
	"io"
	"log"
	"net"
	"shufflemessage/mycrypto"
	"time"

	"golang.org/x/crypto/nacl/box"
)

const blockSize = 128
const clientTestNum = 10
const serverTestNum = 5

var q = mycrypto.Order.Bytes()

//some utility functions used by the servers
func checkProof(db, beaversA, beaversB, beaversC []byte, conns []net.Conn, myNum int, leader bool) (bool, time.Duration) {
    // db: [m], [M], [b], id, a, z1, z2
    startTime := time.Now()
    numServers := len(conns)
    com := mycrypto.ComHash(db[:blockSize*5])
    coms := broadcastAndReceiveFromAll(com, conns, myNum)
    hash := mycrypto.Hash(coms)
    ch := mycrypto.AesPRG(blockSize, hash)
    if !mycrypto.CheckFirstProof(db[blockSize*3:], ch) {
        elapsedTime := time.Since(startTime)
        return false, elapsedTime
    }

    size := blockSize*(2*numServers-1)
    m := db[:blockSize]
    M := db[blockSize:blockSize*2]

    // check m^q = 1
    mq := getShareOfExp(m, q, beaversA[:size], beaversB[:size], 
                        beaversC[:size], conns, myNum, leader)
    mqShares := broadcastAndReceiveFromAll(mq, conns, myNum)
    if !mycrypto.CheckSharesAreOne(1, numServers, mqShares) {
        elapsedTime := time.Since(startTime)
        return false, elapsedTime
    }

    // check M^q = 1
    Mq := getShareOfExp(M, q, beaversA[size:size*2], beaversB[size:size*2], 
                        beaversC[size:size*2], conns, myNum, leader)
    MqShares := broadcastAndReceiveFromAll(Mq, conns, myNum)
    if !mycrypto.CheckSharesAreOne(1, numServers, MqShares) {
        elapsedTime := time.Since(startTime)
        return false, elapsedTime
    }

    // check m^z1 g3^z2 = M^ch b
    z1 := db[blockSize*5:blockSize*6]
    z2 := db[blockSize*6:blockSize*7]
    mz1 := getShareOfExp(m, z1, beaversA[size*2:size*3], beaversB[size*2:size*3], 
                        beaversC[size*2:size*3], conns, myNum, leader)
    mycrypto.MulScalarExp(mz1, mycrypto.G3, z2)

    bShare := db[blockSize*2:blockSize*3]
    Mch := getShareOfExp(M, ch, beaversA[size*3:size*4], beaversB[size*3:size*4], 
                        beaversC[size*3:size*4], conns, myNum, leader)
    data := make([]byte, blockSize*2)
    copy(data[:blockSize], Mch)
    copy(data[blockSize:blockSize*2], bShare)
    MchbShare := getProductShare(myNum, numServers, beaversA[size*4:], 
                beaversB[size*4:], beaversC[size*4:], data, conns, leader)
    
    mycrypto.AddOrSub(MchbShare, mz1, false)
    shares := broadcastAndReceiveFromAll(MchbShare, conns, myNum)
    elapsedTime := time.Since(startTime)
    if !mycrypto.CheckSharesAreZero(1, numServers, shares) {
        return false, elapsedTime
    }
    return true, elapsedTime
}

func getShareOfExp(baseShare, exponent, beaversA, beaversB, beaversC []byte, conns []net.Conn, myNum int, leader bool) []byte {
    numServers := len(conns)
    expShares := mycrypto.GenExpNegShares(numServers, exponent)
    allExpShares := sendAndReceiveFromAll(expShares, conns, myNum)
    var product []byte
    r := make([]byte, blockSize*2)

    // compute r = \prod r_i
    copy(r[:blockSize], allExpShares[:blockSize])
    for i:=1; i < numServers; i++ {
        copy(r[blockSize:blockSize*2], allExpShares[blockSize*2*i:blockSize*(2*i+1)])
        startIndex := blockSize*(i-1)
        endIndex := blockSize*i
        product = getProductShare(myNum, numServers, beaversA[startIndex:endIndex], 
                    beaversB[startIndex:endIndex], beaversC[startIndex:endIndex], r, conns, leader)
        copy(r[:blockSize], product)
    }
    
    // compute r*m
    copy(r[blockSize:blockSize*2], baseShare)
    startIndex := blockSize*(numServers-1)
    endIndex := blockSize*numServers
    mrShare := getProductShare(myNum, numServers, beaversA[startIndex:endIndex], 
                beaversB[startIndex:endIndex], beaversC[startIndex:endIndex], r, conns, leader)
    
    // compute r^(-e) = \prod r_i^(-e)
    rexp := make([]byte, blockSize*2)
    copy(rexp[:blockSize], allExpShares[blockSize:blockSize*2])
    for i:=1; i < numServers; i++ {
        startIndex := blockSize*(numServers+i-1)
        endIndex := blockSize*(numServers+i)
        copy(rexp[blockSize:blockSize*2], allExpShares[blockSize*(2*i+1):blockSize*(2*i+2)])
        product = getProductShare(myNum, numServers, beaversA[startIndex:endIndex], 
                    beaversB[startIndex:endIndex], beaversC[startIndex:endIndex], rexp, conns, leader)
        copy(rexp[:blockSize], product)
    }

    // return (mr)^e[r^(-e)]
    mrShares := broadcastAndReceiveFromAll(mrShare, conns, myNum)
    mr := mergeFlattenedDBs(mrShares, numServers, blockSize)
    mycrypto.MulScalarExp(product, mr, exponent)
    
    return product
}

func myClientSim(msgType int, pubKeys []*[32]byte, withProof bool) ([]byte, time.Duration) {
    startTime := time.Now()
    numServers := len(pubKeys)
    id, secret := mycrypto.GenerateID()
    msg := mycrypto.MakeFullMsg(msgType, secret)

    msgShares := mycrypto.Share(numServers, msg)

    msgToSend := msgShares[0]

    var bShares [][]byte
    var proof []byte
    if withProof {
        bShares, proof = mycrypto.MakeProof(msgShares, msg, id, secret)
        msgToSend = append(msgToSend, bShares[0]...)
        msgToSend = append(msgToSend, id...)
        msgToSend = append(msgToSend, proof...)
    }

    for i:= 1; i < numServers; i++ {
        msgOthers := msgShares[i]
        if withProof {
            msgOthers = append(msgOthers, bShares[i]...)
            msgOthers = append(msgOthers, id...)
            msgOthers = append(msgOthers, proof...)
        }
        //SealAnonymous appends its output to msgToSend
        boxedMessage, err := box.SealAnonymous(nil, msgOthers, pubKeys[i], rand.Reader)
        if err != nil {
            panic(err)
        }
        msgToSend = append(msgToSend, boxedMessage...)
    }

    elapsedTime := time.Since(startTime)
    
    return msgToSend, elapsedTime
}

func leaderReceivingProof(msgType int, db []byte, conns []net.Conn, pubKeys []*[32]byte) time.Duration {
    //client connection receiving phase
    numServers := len(conns)
    
    // [m], [M], [b], id, a, z1, z2
    shareLength := blockSize * 7
    boxedShareLength := (shareLength + box.AnonymousOverhead)

    //handle connections from client, pass on boxes
    clientTransmission, clientTime := myClientSim(msgType, pubKeys, true)
                
    //handle the message sent for this server
    copy(db[:shareLength], clientTransmission[:shareLength])
    
    //pass on the boxes to the other servers, send the index they should be placed in too
    for i := 1; i < numServers; i++ {
        //send client message
        start := shareLength + (i-1)*boxedShareLength
        end := shareLength + i*boxedShareLength
        writeToConn(conns[i], clientTransmission[start:end])
    }
    return clientTime
}

func otherReceivingProof(db []byte, conns []net.Conn, myPubKey, mySecKey *[32]byte) {
    
    shareLength := blockSize * 7
    boxedShareLength := (shareLength + box.AnonymousOverhead)

    clientBox := readFromConn(conns[0], boxedShareLength)
                
    clientMessage, ok := box.OpenAnonymous(nil, clientBox, myPubKey, mySecKey)
    if !ok {
        panic("decryption not ok!!")
    }
    
    //store in db
    copy(db[:shareLength], clientMessage[:])
}

func leaderReceivingPhase(db [][]byte, setupConns [][]net.Conn, batchSize int, pubKeys []*[32]byte) {
    //client connection receiving phase
    numServers := len(setupConns)
    
    // only send m and M in performance experiment
    shareLength := blockSize * 2
    boxedShareLength := (shareLength + box.AnonymousOverhead)

    //generate preliminary permutation
    seed := make([]byte, 16)
    _,err := rand.Read(seed)
    if err != nil {
        log.Println("couldn't generate seed")
        panic(err)
    }
    rand.Read(seed)
    prelimPerm := mycrypto.GenPerm(batchSize, seed)
    //NOTE: the preliminary permutation is effectively "for free" to evaluate 
    //because the server just copies the client messages into their permuted indices directly
    
    
    numThreads, chunkSize := mycrypto.PickNumThreads(batchSize)
    //numThreads = 1
    //chunkSize = batchSize
    blocker := make(chan int)
    
    for i:=0; i < numThreads; i++ {
        startIndex := i*chunkSize
        endIndex := (i+1)*chunkSize
        go func(startI, endI, threadNum int) {
            //for performance measurement we'll only implement the case where all client messages are good
            //we'll just panic later if a blind mac verification fails
                        
            for msgCount := startI; msgCount < endI; msgCount++ {
                //handle connections from client, pass on boxes
                clientTransmission, _ := myClientSim(msgCount%26, pubKeys, false)
                
                //handle the message sent for this server
                copy(db[prelimPerm[msgCount]][0:shareLength], clientTransmission[0:shareLength])
                
                //pass on the boxes to the other servers, send the index they should be placed in too
                for i := 1; i < numServers; i++ {
                    
                    //send prelimPerm[msgCount]
                    writeToConn(setupConns[i][threadNum], intToByte(prelimPerm[msgCount]))
                    
                    //send client message
                    start := shareLength + (i-1)*boxedShareLength
                    end := shareLength + i*boxedShareLength
                    writeToConn(setupConns[i][threadNum], clientTransmission[start:end])
                }
            }
            blocker <- 1
        }(startIndex, endIndex, i)
    }
    
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
}

func otherReceivingPhase(db [][]byte, setupConns [][]net.Conn, numServers, batchSize int, myPubKey, mySecKey *[32]byte) {

    shareLength := blockSize * 2
    boxedShareLength := (shareLength + box.AnonymousOverhead)
    numThreads, chunkSize := mycrypto.PickNumThreads(batchSize)
    //numThreads = 1
    //chunkSize = batchSize
    
    blocker:= make(chan int)
    
    for i:=0; i < numThreads; i++ {
        startIndex := i*chunkSize
        endIndex := (i+1)*chunkSize
        go func(startI, endI, threadIndex int) {
            //client connection receiving phase
            for msgCount := startI; msgCount < endI; msgCount++ {
                
                //read permuted index from leader
                prelimPermIndex := byteToInt(readFromConn(setupConns[0][threadIndex], 4))
                
                //read client box from leader, unbox
                clientBox := readFromConn(setupConns[0][threadIndex], boxedShareLength)
                
                clientMessage, ok := box.OpenAnonymous(nil, clientBox, myPubKey, mySecKey)
                if !ok {
                    panic("decryption not ok!!")
                }
                
                //store in db
                copy(db[prelimPermIndex][0:shareLength], clientMessage[:])
            }
            
            blocker <- 1
        }(startIndex, endIndex, i)
    }
    
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
}

func readFromConn(conn net.Conn, bytes int) []byte {
    buffer := make([]byte, bytes)
    for count := 0; count < bytes; {
        n, err := conn.Read(buffer[count:])
        //log.Println(count)
        //log.Println(bytes)
        count += n
        if err != nil && err != io.EOF && count != bytes {
            log.Println(n)
            panic(err)
        }
    }
    return buffer
}

func writeToConn(conn net.Conn, msg []byte) {
    n, err := conn.Write(msg)
    if err != nil {
        log.Println(n)
        panic(err)
    }
}

func intToByte(myInt int) (retBytes []byte){
    retBytes = make([]byte, 4)
    retBytes[3] = byte((myInt >> 24) & 0xff)
    retBytes[2] = byte((myInt >> 16) & 0xff)
    retBytes[1] = byte((myInt >> 8) & 0xff)
    retBytes[0] = byte(myInt & 0xff)
    return
}

func byteToInt(myBytes []byte) (x int) {
    x = int(myBytes[3]) << 24 + int(myBytes[2]) << 16 + int(myBytes[1]) << 8 + int(myBytes[0])
    return
}

//flatten the db
func flatten(db [][]byte, flatDB []byte){
    rowLen := len(db[0])
    for i:= 0; i < len(db); i++ {
        copy(flatDB[i*rowLen:(i+1)*rowLen], db[i])
    }
}

func unflatten(db [][]byte, flatDB []byte) {
    rowLen := len(db[0])
    for i:=0; i < len(db); i++ {
        db[i] = flatDB[i*rowLen:(i+1)*rowLen]
    }
}

//merge the concatenation of flattened DBs into one DB
//by taking the elementwise sum of all the DBs
func mergeFlattenedDBs(flatDBs []byte, numServers, dbSize int) []byte {
    if dbSize % blockSize != 0 || len(flatDBs) != numServers*dbSize {
        panic("something is wrong with the MergeFlattenedDBs parameters")
    }
    
    dbs := make([][]byte, numServers)
    
    for i := 0; i < numServers; i++ {
        dbs[i] = flatDBs[i*dbSize:(i+1)*dbSize]
    }
    
    return mycrypto.Merge(dbs)
}

func broadcastAndReceiveFromAll(msg []byte, conns []net.Conn, myNum int) []byte {
    blocker := make(chan int)
    numServers := len(conns)
    contentLenPerServer := len(msg)
    content := make([]byte, contentLenPerServer*numServers)
        
    //for servers with lower number, read then write
    for i:=0; i < myNum; i++ {
        go func(data, outputLocation []byte, conn net.Conn) {
            bytesToRead := len(data)
            copy(outputLocation, readFromConn(conn, bytesToRead))
            writeToConn(conn, data)
            blocker <- 1
        }(msg, content[i*contentLenPerServer:(i+1)*contentLenPerServer], conns[i])
    }
    
    //for servers with higher number, write then read
    for i:= myNum+1; i < numServers; i++ {
        go func(data, outputLocation []byte, conn net.Conn) {
            bytesToRead := len(data)
            writeToConn(conn, data)
            copy(outputLocation, readFromConn(conn, bytesToRead))
            blocker <- 1
        }(msg, content[i*contentLenPerServer:(i+1)*contentLenPerServer], conns[i])
    }
    
    //"receive" from self
    copy(content[contentLenPerServer*myNum:contentLenPerServer*(myNum+1)], msg[:])
    
    for i := 1; i < numServers; i++ {
        <- blocker
    }
    
    return content
}

func sendAndReceiveFromAll(msg [][]byte, conns []net.Conn, myNum int) []byte {
    blocker := make(chan int)
    numServers := len(conns)
    contentLenPerServer := len(msg[0])
    content := make([]byte, contentLenPerServer*numServers)
        
    //for servers with lower number, read then write
    for i:=0; i < myNum; i++ {
        go func(data, outputLocation []byte, conn net.Conn) {
            bytesToRead := len(data)
            copy(outputLocation, readFromConn(conn, bytesToRead))
            writeToConn(conn, data)
            blocker <- 1
        }(msg[i], content[i*contentLenPerServer:(i+1)*contentLenPerServer], conns[i])
    }
    
    //for servers with higher number, write then read
    for i:= myNum+1; i < numServers; i++ {
        go func(data, outputLocation []byte, conn net.Conn) {
            bytesToRead := len(data)
            writeToConn(conn, data)
            copy(outputLocation, readFromConn(conn, bytesToRead))
            blocker <- 1
        }(msg[i], content[i*contentLenPerServer:(i+1)*contentLenPerServer], conns[i])
    }
    
    //"receive" from self
    copy(content[contentLenPerServer*myNum:contentLenPerServer*(myNum+1)], msg[myNum][:])
    
    for i := 1; i < numServers; i++ {
        <- blocker
    }
    
    return content
}

func getProductShare(serverNum, numServers int, beaversA, beaversB, beaversC, db []byte, conns []net.Conn, leader bool) [] byte {
    maskedStuff := mycrypto.GetMaskedStuff(1, 1, serverNum, beaversA, beaversB, db)
    maskedShares := broadcastAndReceiveFromAll(maskedStuff, conns, serverNum)
    mergedMaskedShares := mergeFlattenedDBs(maskedShares, numServers, len(maskedStuff))
    macDiffShares := mycrypto.BeaverProduct(1, 1, beaversC, mergedMaskedShares, db, leader)
    return macDiffShares
}
