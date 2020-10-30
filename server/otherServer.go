package main

import (
    "log"
    "crypto/tls"
    //"net"
    //"os"
    //"time"
    //"unsafe"
    //"io"
    //"crypto/rand"
    "golang.org/x/crypto/nacl/box"
    //"sync/atomic"
    "strings"
    "strconv"
    
    "shufflemessage/mycrypto" //my crypto in crypto.go, the rest generated by Goff https://github.com/ConsenSys/goff
)

func server(numServers, msgBlocks, batchSize, myNum int, leaderAddr string) {
    
    
    //using a deterministic source of randomness for testing 
    //this is just for testing so the different parties share a key
    //in reality the public keys of the servers/auditors should be known 
    //ahead of time and those would be used
    pubKeys := make([]*[32]byte, numServers)
    
    var err error
    var mySecKey *[32]byte
    var auxSharedKey [32]byte

    auxPubKey, _, err := box.GenerateKey(strings.NewReader(strings.Repeat("a", 10000)))
    if err != nil {
        log.Println(err)
        return
    }
    
    for i := 0; i < numServers; i++ {
        
        if i == myNum {
            pubKeys[i], mySecKey, err = box.GenerateKey(strings.NewReader(strings.Repeat(strconv.Itoa(i),10000)))
            if err != nil {
                log.Println(err)
                return
            }
        } else {
            pubKeys[i], _, err = box.GenerateKey(strings.NewReader(strings.Repeat(strconv.Itoa(i),10000)))
            if err != nil {
                log.Println(err)
                return
            }
        }

    }
    
    box.Precompute(&auxSharedKey, auxPubKey, mySecKey)
 
    conf := &tls.Config{
         InsecureSkipVerify: true,
    }
    
    //connect to server
    conn, err := tls.Dial("tcp", leaderAddr, conf)
    if err != nil {
        log.Println(err)
        return 
    }
    defer conn.Close()
    
    //some relevant values
    //48 is for mac key share, mac, encryption key, 16 bytes each
    shareLength := 48 + 16*msgBlocks
    boxedShareLength := (shareLength + box.AnonymousOverhead)
    //server share is longer because there needs to be space for a share of _each_ mac key share
    serverShareLength := 16*msgBlocks + 32 + numServers * 16
    blocksPerRow :=  msgBlocks + numServers + 2 //2 is for the mac and enc key, numServers for the mac key shares
    numBeavers := batchSize * (msgBlocks + 1) // +1 is for the encryption key which is included in the mac
    dbSize := blocksPerRow*batchSize*16
    //bigbox has nonce, beavers, perm, delta, abs, and box encryption overhead
    bigBoxSize := 24 + numBeavers*48 + 4*batchSize + dbSize + 2*(numServers-1)*dbSize + box.Overhead
    
    //data structure for holding batch of messages
    //each entry will be of length serverShareLength
    db := make([][]byte, batchSize)
    for i:= 0; i < batchSize; i++ {
        db[i] = make([]byte, serverShareLength)
    }

    var nonce [24]byte

    //main server loop below
    for {
        //client connection receiving phase
        for msgCount := 0; msgCount < batchSize; msgCount++ {
            
            //read permuted index from leader
            prelimPermIndex := byteToInt(readFromConn(conn, 4))
            
            //read client box from leader, unbox
            clientBox := readFromConn(conn, boxedShareLength)
            
            clientMessage, ok := box.OpenAnonymous(nil, clientBox, pubKeys[myNum], mySecKey)
            if !ok {
                panic("decryption not ok!!")
            }
            
            //expand seeds, store in db
            copy(db[prelimPermIndex][0:16*numServers], 
                mycrypto.ExpandKeyShares(myNum, numServers, clientMessage[0:16]))
            copy(db[prelimPermIndex][16*numServers:], clientMessage[16:shareLength])

        }
        
        //processing phase

        //unbox and read the beaver triples/share translation info
        messageBox := readFromConn(conn, bigBoxSize)
        
        copy(nonce[:], messageBox[:24])
        
        contents,ok := box.OpenAfterPrecomputation(nil, messageBox[24:], &nonce, &auxSharedKey)
        if !ok {
            panic("error in decryption")
        }
                
        beavers := contents[:numBeavers*48]
        piBytes := contents[numBeavers*48:numBeavers*48+batchSize*4]
        pi := make([]int, 0)
        for i:=0; i < batchSize; i++ {
            pi = append(pi, byteToInt(piBytes[4*i:4*(i+1)]))
        }
        delta := contents[numBeavers*48+batchSize*4:numBeavers*48+batchSize*4+dbSize]
        abs := make([][]byte, numServers)
        startIndex := numBeavers*48+batchSize*4+dbSize
        for i:=0; i < numServers; i++ {
            if i != myNum {
                abs[i] = contents[startIndex:startIndex+2*dbSize]
                startIndex+=2*dbSize
            }
        }
        
        //TODO: blind MAC verification, 
        
        //TODO: shuffle
        
        //TODO commit, reveal, mac verify, decrypt
        //TODO do this one first after finishing the leader
        //then test the whole thing by making them all print the output DBs they got
        //make sure they're all the same and all have the messages intact
        //also temporarily vary the messages to see that the different messages come through
        
    }
}
