package main

import (
    "log"
    "crypto/tls"
    "net"
    "time"
    "golang.org/x/crypto/nacl/box"
    "strconv"
    "strings"
    "runtime"
    
    "shufflemessage/mycrypto" 
)

func aux (numServers, msgBlocks, batchSize int, addrs []string) {
    
    log.Println("This is the auxiliary server")
    
    //using a deterministic source of randomness for testing 
    //this is just for testing so the different parties share a key
    //in reality the public keys of the servers/auditors should be known 
    //ahead of time and those would be used
    pubKeys := make([]*[32]byte, numServers)
    sharedKeys := make([][32]byte, numServers)
    
    var err error;
    
    _, mySecKey, err := box.GenerateKey(strings.NewReader(strings.Repeat("a", 10000)))
    if err != nil {
        log.Println(err)
        return
    }
    
    for i := 0; i < numServers; i++ {
    	pubKeys[i], _, err = box.GenerateKey(strings.NewReader(strings.Repeat(strconv.Itoa(i),10000)))
    	if err != nil {
        	log.Println(err)
        	return
    	}
    	
    	box.Precompute(&sharedKeys[i], pubKeys[i], mySecKey)
    }
 
    conf := &tls.Config{
         InsecureSkipVerify: true,
    }
    
    //connect to each server 
    //holds connections to the shuffle servers
    conns := make([]net.Conn, numServers)
    
    for i:=0; i < numServers; i++ {
        //connect to each server
        conns[i], err = tls.Dial("tcp", addrs[i], conf)
        if err != nil {
            log.Println(err)
            return
        }
        defer conns[i].Close()
        readFromConn(conns[i], 4)
        writeToConn(conns[i], intToByte(1))
    }

    
    blocksPerRow :=  msgBlocks + numServers + 2 //2 is for the mac and enc key, numServers for the mac key shares
        
    numBeavers := batchSize * (msgBlocks + 1) // +1 is for the encryption key which is included in the mac
    
    totalBatches := 0
    var totalTime time.Duration
    var beaverTotalTime time.Duration
    blocker := make(chan int)
    
    for testCount:=0; testCount < 10; testCount++{
        runtime.GC()
        log.Println("ready")
        //leader requests triples and translations
        readFromConn(conns[0], 4)
        log.Println("received request")
            
        startTime := time.Now()
        
        //generate the preprocessed information for all the parties

        beavers := mycrypto.GenBeavers(numBeavers, numServers)
        
        //send servers their beaver stuff
        //no need for blocking since that next steps don't depend on this and there is blocking at the end
        for i:=0; i < numServers; i++ {
            go func(myBeavers []byte, serverNum int) {
                writeToConn(conns[serverNum], myBeavers)
            }(beavers[i], i)
        }
        
        beaverElapsedTime := time.Since(startTime)
        
        perms, aInitial, aAtPermTime, bFinal, sAtPermTime, deltas := mycrypto.GenShareTrans(batchSize, blocksPerRow, numServers)

        //send servers their share translation stuff
        for i:= 0; i < numServers; i++ {
            go func(myPerm, myAInitial, myAAtPermTime, myBFinal, mySAtPermTime, myDelta []byte,  serverNum int) {
                writeToConn(conns[serverNum], myPerm)
                writeToConn(conns[serverNum], myDelta)
                
                if serverNum != 0 {
                    writeToConn(conns[serverNum], myAInitial)
                    writeToConn(conns[serverNum], mySAtPermTime)
                }
                
                if serverNum != numServers - 1 {
                    writeToConn(conns[serverNum], myBFinal)
                    writeToConn(conns[serverNum], myAAtPermTime)
                }
                
                blocker <- 1
                return
            } (perms[i], aInitial[i], aAtPermTime[i], bFinal[i], sAtPermTime[i], deltas[i], i)
        }
        
        for i:=0; i < numServers; i++ {
            <- blocker
        }
        
        elapsedTime := time.Since(startTime)
        totalTime += elapsedTime
        beaverTotalTime += beaverElapsedTime
        totalBatches++
        log.Printf("preprocessing data prepared in %s\n", elapsedTime)
        log.Printf("beaver generation time only: %s, average: %s\n", beaverElapsedTime, beaverTotalTime/time.Duration(totalBatches))
        log.Printf("%d batches prepared so far, average time %s\n\n", totalBatches, totalTime/time.Duration(totalBatches))
    }
}
