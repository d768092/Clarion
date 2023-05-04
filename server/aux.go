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
    "fmt"
    
    "shufflemessage/mycrypto" 
)

func aux (numServers int, batchSizeParams []int, addrs []string) {
    
    numParams := len(batchSizeParams)
    
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
    
    // client test
    var beaverTotalTime time.Duration
    for i:=0; i < clientTestNum; i++ {
        startTime := time.Now()

        numBeavers := 4*(2*numServers-1) + 1
        beaverBlocker := make(chan int)
        blocker := make(chan int)
        seeds := make([][]byte, numServers)
        for i:=0; i < numServers; i++ {
            go func(index int) {
                seeds[index] = readFromConn(conns[index], 32)
                blocker <- 1
            }(i)
        }
        
        for i:=0; i < numServers; i++ {
            <- blocker
        }

        beavers := mycrypto.GenBeavers(numBeavers, 0, seeds)
        //send servers their beaver stuff
        for i:=0; i < numServers; i++ {
            go func(myBeavers []byte, serverNum int) {
                writeToConn(conns[serverNum], myBeavers)
                beaverBlocker <- 1
            }(beavers[i], i)
        }

        for i:=0; i < numServers; i++ {
            <- beaverBlocker
        }

        beaverElapsedTime := time.Since(startTime)
        beaverTotalTime += beaverElapsedTime

        if i == clientTestNum - 1 {
            fmt.Printf("Beaver generation time: %s\n", beaverTotalTime/time.Duration(clientTestNum))
        }
    }
    
    for evalNum := 0; evalNum < numParams; evalNum++ {
        batchSize := batchSizeParams[evalNum]
        
        log.Printf("numServers %d\n", numServers)
        log.Printf("batchSize %d\n", batchSize)
        
        blocksPerRow :=  2
        
        
        totalBatches := 0
        var totalTime time.Duration
        
        blocker := make(chan int)
        deltaBlocker := make(chan int)
        
        seeds := make([][]byte, numServers)
        
        for testCount:=0; testCount < serverTestNum; testCount++{
            runtime.GC()
            log.Println("ready")
            
            for i:=0; i < numServers; i++ {
                go func(index int) {
                    seeds[index] = readFromConn(conns[index], 64)
                    blocker <- 1
                }(i)
            }
            
            for i:=0; i < numServers; i++ {
                <- blocker
            }
            
            log.Println("received requests")
                
            startTime := time.Now()
            
            //get the last delta
            delta := mycrypto.GenShareTrans(batchSize, blocksPerRow, seeds)
            
            //send the last server delta
            go func(){
                writeToConn(conns[numServers - 1], delta)
                deltaBlocker <- 1
            }()

            <- deltaBlocker
            elapsedTime := time.Since(startTime)
            totalTime += elapsedTime
            
            totalBatches++
            
            if testCount == 4 {
                fmt.Printf("%d servers, %d msgs per batch, %d byte messages\n", numServers, batchSize, 127)
                fmt.Printf("preprocessing data prepared in %s\n", elapsedTime)
                fmt.Printf("%d batches prepared, average time %s\n\n", totalBatches, totalTime/time.Duration(totalBatches))
                
                log.Printf("%d batches prepared, average time %s\n\n", totalBatches, totalTime/time.Duration(totalBatches))
            }
        }
    }
}
