package mycrypto

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/sha256"
	"log"
    "math/big"

	//"golang.org/x/crypto/nacl/box"
	//"strings"
	"bytes"

	"shufflemessage/modp"
)

const blockSize = 16 // Change to 128 later?

// find the group generator where
// 1) g^((p-1)/2) = 1 (mod p)
// 2) the discrete log between them are non-trivial
// g1, g2, g3 should be modified later

const g1 = 31
const g2 = 32
const g3 = 33

var g1Element = modp.Element{
    g1,
    0,
}

var g2Element = modp.Element{
    g2,
    0,
}

var g3Element = modp.Element{
    g3,
    0,
}

var q, _ = new(big.Int).SetString("170141183460469231731687303715884105648", 10)

// return id, (s1, s2)
func GenerateID() ([]byte, []byte) {
    secret := make([]byte, blockSize * 2)

    s1, err := rand.Int(rand.Reader, q)
    if err != nil {
        log.Println("Couldn't generate secret")
        panic(err)
    }
    s2, err := rand.Int(rand.Reader, q)
    if err != nil {
        log.Println("Couldn't generate secret")
        panic(err)
    }
    var id, temp modp.Element
    id.Exp(g1Element, s1)
    temp.Exp(g2Element, s2)
    id.Mul(&id, &temp)

    copy(secret[:blockSize], s1.Bytes())
    copy(secret[blockSize:blockSize * 2], s2.Bytes())
    return id.Bytes(), secret
}

//return a message
func MakeMsg(msgType int) []byte {
    m := make([]byte, blockSize)
    for i := 0; i < blockSize; i++ {
        m[i] = byte(97 + msgType) //ascii 'a' is 97
    }
    
    return m
}

//return a message and the backdoor
func MakeFullMsg(msgType int, secret []byte) []byte {
    ret := make([]byte, blockSize * 2)
    
    m := make([]byte, blockSize)
    for i := 0; i < blockSize; i++ {
        m[i] = byte(97 + msgType) //ascii 'a' is 97
    }

    // generate the backdoor
    s1 := new(big.Int).SetBytes(secret[:blockSize])
    s2 := new(big.Int).SetBytes(secret[blockSize:])
    var mElement, M, temp modp.Element
    mElement.SetBytes(m)
    M.Exp(mElement, s1)
    temp.Exp(g3Element, s2)
    M.Mul(&M, &temp)

    copy(ret[:blockSize], m)
    copy(ret[blockSize:blockSize*2], M.Bytes())
    
    return ret
}


// return the proof: bshare, (a, z1, z2)
func MakeProof(msgShares [][]byte, msg, id, secret []byte) ([][] byte, []byte) {
    numServers := len(msgShares)

    // return (a, z1, z2)
    ret := make([]byte, blockSize * 3)

    // generate the secrets and the backdoor
    r1, err := rand.Int(rand.Reader, q)
    if err != nil {
        log.Println("Couldn't generate secret")
        panic(err)
    }
    r2, err := rand.Int(rand.Reader, q)
    if err != nil {
        log.Println("Couldn't generate secret")
        panic(err)
    }

    var a, b, mElement, temp modp.Element
    a.Exp(g1Element, r1)
    temp.Exp(g2Element, r2)
    a.Mul(&a, &temp)
    mElement.SetBytes(msg[:blockSize])
    b.Exp(mElement, r1)
    temp.Exp(g3Element, r2)
    b.Mul(&b, &temp)
    bShares := Share(numServers, b.Bytes())

    coms := make([]byte, numServers*32)
    for i := 0; i < numServers; i++ {
        data := msgShares[i]
        data = append(data, bShares[i]...)
        data = append(data, id...)
        data = append(data, a.Bytes()...)
        startIndex := 32 * i
        endIndex := 32 * (i+1)
        copy(coms[startIndex:endIndex], comHash(data))
    }
    hash := Hash(coms)
    ch := new(big.Int).SetBytes(hash)
    ch.Mod(ch, q)
    // The way of generating ch should be changes if blockSize > 32

    s1 := new(big.Int).SetBytes(secret[:blockSize])
    s2 := new(big.Int).SetBytes(secret[blockSize:])
    var z1, z2 big.Int
    z1.Mul(ch, s1)
    z1.Add(&z1, r1)
    z2.Mul(ch, s2)
    z2.Add(&z2, r2)

    copy(ret[:blockSize], a.Bytes())
    copy(ret[blockSize:blockSize*2], z1.Bytes())
    copy(ret[blockSize*2:blockSize*3], z2.Bytes())

    return bShares, ret
}

// data should be m_i | M_i | b | id | a
func comHash(data []byte) []byte {
    hash := sha256.Sum256(data)
    return hash[:]
}

//return a message, the backdoor, and the proof
/*func MakeFullMsgAndProof(msgType int) []byte {
    blockSize := 16
    ret := make([]byte, blockSize * 7)

    // generate the secrets and id
    s1, err := rand.Int(rand.Reader, q)
    if err != nil {
        log.Println("Couldn't generate secret")
        panic(err)
    }
    s2, err := rand.Int(rand.Reader, q)
    if err != nil {
        log.Println("Couldn't generate secret")
        panic(err)
    }
    var id, temp modp.Element
    id.Exp(g1Element, s1)
    temp.Exp(g2Element, s2)
    id.Mul(&id, &temp)
    
    //make up a message to encrypt, set empty iv
    m := make([]byte, blockSize)
    for i := 0; i < blockSize; i++ {
        m[i] = byte(97 + msgType) //ascii 'a' is 97
    }

    var mElement, M modp.Element
    mElement.SetBytes(m)
    M.Exp(mElement, s1)
    temp.Exp(g3Element, s2)
    M.Mul(&M, &temp)
    
    copy(ret[:blockSize], m)
    copy(ret[blockSize:blockSize*2], M.Bytes())
    copy(ret[blockSize*2:blockSize*3], id.Bytes())
    
    return ret
}*/

//expand a seed using aes in CTR mode
func AesPRG(msgLen int, seed []byte) []byte {
    
    ct := make([]byte, msgLen)
    c, err := aes.NewCipher(seed)
    if err != nil {
        log.Println("Couldn't inititate new cipher")
        panic(err)
    }
    
    //our biggest DBs will fortunately have lengths that still fit in ints
    numThreads, chunkSize := PickNumThreads(msgLen)
    
    if msgLen < 2000 {//no need to split it up for small messages
        numThreads = 1
        chunkSize = msgLen
    }
    
    empty := make([]byte, chunkSize)
    blocker := make(chan int)
    for i:=0; i < numThreads; i++ {
        startIndex := i*chunkSize;
        endIndex := (i+1)*chunkSize
        go func(start, end int) {
            iv := make([]byte, 16)
            copy(iv[0:4], intToByte(start))
            ctr := cipher.NewCTR(c, iv)
            ctr.XORKeyStream(ct[start:end], empty)
            blocker <- 1
        }(startIndex, endIndex)
    }
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
    
    return ct
}

//expand a key seed share to a vector of zeros with the seed in the correct place
/*func ExpandKeyShares(myServerNum, numServers int, keySeedShare []byte) []byte {
    expansion := make([]byte, 16*numServers)
    copy(expansion[16*myServerNum:16*(myServerNum+1)], keySeedShare)
    return expansion
}*/

//splits a message into additive shares mod a prime
func Share(numShares int, msg []byte) [][]byte {
    shares := make([][]byte, numShares)
    shares[0] = make([]byte, len(msg))
    
    numBlocks := len(msg)/blockSize
    if len(msg) % blockSize != 0 {
        panic("message being shared has length not a multiple of blockSize")
    }
        
    var lastShare []*modp.Element

    //make lastShare hold msg in Element form
    for i:= 0; i < numBlocks; i++ {
        var temp modp.Element
        lastShare = append(lastShare, temp.SetBytes(msg[blockSize*i:blockSize*(i+1)]))
    }
    
    
    for i:= 1; i < numShares; i++ {
                
        //make the share random
        shares[i] = make([]byte, len(msg))
        _,err := rand.Read(shares[i])
        if err != nil {
            log.Println("couldn't generate randomness for sharing")
            panic(err)
        }
        
        //change every block into an Element
        //subtract from the last share
        for j:=0; j < numBlocks; j++ {
            var temp modp.Element
            lastShare[j].Sub(lastShare[j], temp.SetBytes(shares[i][blockSize*j:blockSize*(j+1)]))
        }
    }
    
    //set the zeroth share to be lastShare in byte form
    for i:=0; i < numBlocks; i++ {
        copy(shares[0][blockSize*i:blockSize*(i+1)], lastShare[i].Bytes())
    }
    
    return shares
}

//combine additive shares to recover message
func Merge(shares [][]byte) []byte{

    numShares := len(shares)
    numBlocks := len(shares[0])/blockSize
    if len(shares[0]) % blockSize != 0 {
        panic("messages being merged have length not a multiple of blockSize")
    }
    
    var elements []*modp.Element

    //make array of elements that holds the first share
    for j:=0; j < numBlocks; j++ {
        var temp modp.Element
        elements = append(elements, temp.SetBytes(shares[0][blockSize*j:blockSize*(j+1)]))
    }
    
    numThreads, chunkSize := PickNumThreads(numBlocks)
    blocker := make(chan int)
    
    //add in the corresponding elements from subsequent shares
    for i:=1; i < numShares; i++ {
        if len(shares[i]) != len(shares[0]) {
            panic("messages being merged have different lengths")
        }
        
        for t := 0; t<numThreads; t++ {
            startIndex := t*chunkSize
            endIndex := (t+1)*chunkSize
            go func(startJ, endJ int) {
                var temp modp.Element
                for j:=startJ; j < endJ; j++ {
                    temp.SetBytes(shares[i][blockSize*j:blockSize*(j+1)])
                    elements[j].Add(elements[j], &temp)
                }
                blocker <- 1
            }(startIndex, endIndex)
        }
        
        for j:=0; j < numThreads; j++ {
            <- blocker
        }
    }
    
    //convert the whole thing to []byte
    output := make([]byte, 0)
    for j:=0; j < numBlocks; j++ {
        output = append(output, elements[j].Bytes()...)
    }
    
    return output
}

func PickNumThreads(size int) (int,int) {
    numThreads := 16
    if size % 16 != 0 {
        //log.Println("using batchSize divisible by 16 will give better performance")
        if size % 8 == 0 {
            numThreads = 8
        } else if size % 4 == 0 {
            numThreads = 4
        } else if size % 2 == 0 {
            numThreads = 2
        } else {
            numThreads = 1
        }
        //log.Printf("using %d threads\n", numThreads)
    }
    //_ = numThreads
    //return 1, size
    return numThreads, size/numThreads
}

func AddOrSub(a, b []byte, add bool) {
    numBlocks := len(a)/16
    
    numThreads,chunkSize := PickNumThreads(numBlocks)
    
    blocker := make(chan int)
    
    for j:=0; j < numThreads; j++ {
        startIndex := j*chunkSize
        endIndex := (j+1)*chunkSize
        go func(startI, endI int) {
            var eltA, eltB modp.Element
            for i :=startI; i < endI; i++ {
                eltA.SetBytes(a[16*i:16*(i+1)])
                eltB.SetBytes(b[16*i:16*(i+1)])
                
                if add {
                    eltA.Add(&eltA, &eltB)
                } else {
                    eltA.Sub(&eltA, &eltB)
                }
                
                copy(a[16*i:16*(i+1)], eltA.Bytes())
            }
            blocker <- 1
        }(startIndex, endIndex)
    }
    
    for i:= 0; i < numThreads; i++ {
        <- blocker
    }
}

//we often do 2 add/subtract ops in a row. This should save some format converting
func DoubleAddOrSub(a, b, c []byte, add1, add2 bool) {
    numBlocks := len(a)/16
    
    numThreads,chunkSize := PickNumThreads(numBlocks)
    
    blocker := make(chan int)
    
    for j:=0; j < numThreads; j++ {
        startIndex := j*chunkSize
        endIndex := (j+1)*chunkSize
        go func(startI, endI int) {
            var eltA, eltB, eltC modp.Element
            for i :=startI; i < endI; i++ {
                eltA.SetBytes(a[16*i:16*(i+1)])
                eltB.SetBytes(b[16*i:16*(i+1)])
                eltC.SetBytes(c[16*i:16*(i+1)])
                
                if add1 {
                    eltA.Add(&eltA, &eltB)
                } else {
                    eltA.Sub(&eltA, &eltB)
                }
                
                if add2 {
                    eltA.Add(&eltA, &eltC)
                } else {
                    eltA.Sub(&eltA, &eltC)
                }
                
                copy(a[16*i:16*(i+1)], eltA.Bytes())
            }
            blocker <- 1
        }(startIndex, endIndex)
    }
    
    for i:= 0; i < numThreads; i++ {
        <- blocker
    }
}

//generate a permutation of the numbers [0, n)
func GenPerm(n int, seed []byte) []int {
    perm := make([]int, n)
    randomness := AesPRG(4*n, seed)
    
    for i:=1; i < n; i++ {
        j := byteToInt(randomness[4*i:4*(i+1)]) % (i+1)
        perm[i] = perm[j]
        perm[j] = i
    }
    return perm
}

func byteToInt(myBytes []byte) (x int) {
    x = int(myBytes[3]) << 24 + int(myBytes[2]) << 16 + int(myBytes[1]) << 8 + int(myBytes[0])
    return
}

func intToByte(myInt int) (retBytes []byte){
    retBytes = make([]byte, 4)
    retBytes[3] = byte((myInt >> 24) & 0xff)
    retBytes[2] = byte((myInt >> 16) & 0xff)
    retBytes[1] = byte((myInt >> 8) & 0xff)
    retBytes[0] = byte(myInt & 0xff)
    return
}

//generate beaver triples
//outputs are [][]byte slices for each server that contain [a]||[b]||[c] (in beaverDB)
func GenBeavers(numBeavers, seedIndex int, seeds [][]byte) [][]byte {
    
    numServers := len(seeds)
    beaversC := make([]byte, numBeavers*16)
    beaversA := make([][]byte, numServers)
    beaversB := make([][]byte, numServers)

    
    numThreads, chunkSize := PickNumThreads(numBeavers)
    blocker := make(chan int)
    
    //expand a and b shares
    for i:=0; i < numServers; i++ {
        go func(index int) {
            beaversA[index] = AesPRG(16*numBeavers, seeds[index][seedIndex:seedIndex+16])
            blocker <- 1
        }(i)
        go func(index int) {
            beaversB[index] = AesPRG(16*numBeavers, seeds[index][seedIndex+16:seedIndex+32])
            blocker <- 1
        }(i)
    }
    
    for i:=0; i < 2*numServers; i++ {
        <- blocker
    }
    
    //merge a and b shares
    beaversAMerged := Merge(beaversA)
    beaversBMerged := Merge(beaversB)
    
    //compute c
    for j:=0;j<numThreads; j++ {
        startIndex := j*chunkSize
        endIndex := (j+1)*chunkSize
        go func(startI, endI int) {
            //generate triples a,b,c s.t. a*b=c
            var eltA, eltB, eltC modp.Element
            for i:= startI; i < endI; i++ {
                eltA.SetBytes(beaversAMerged[i*16:(i+1)*16])
                eltB.SetBytes(beaversBMerged[i*16:(i+1)*16])
                eltC.Mul(&eltA, &eltB)
                copy(beaversC[16*i:16*(i+1)], eltC.Bytes())
            }
            blocker <- 1
        }(startIndex, endIndex)
    }
    
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
    
    //share the beaver triples
    return Share(numServers, beaversC)
}

/*func TestGenBeavers() bool {
    numBeavers := 3
    numServers := 2
    
    seeds := make([][]byte, numServers)
    for i:=0; i < numServers; i++ {
        seeds[i] = make([]byte, 96)
        _,err := rand.Read(seeds[i])
        if err != nil {
            panic(err)
        }
    }
    beaversAShares := make([][]byte, numServers)
    beaversBShares := make([][]byte, numServers)
    for i:=0; i < numServers; i++ {
        beaversAShares[i] = AesPRG(48, seeds[i][48:64])
        beaversBShares[i] = AesPRG(48, seeds[i][64:80])
    }
    
    beaversA := Merge(beaversAShares)
    beaversB := Merge(beaversBShares)
    beaversC := Merge(GenBeavers(numBeavers, 48, seeds))
    
    var a, b, c, prod modp.Element
    for i:=0; i < numBeavers; i++ {
        startBeaver := i*16
        a.SetBytes(beaversA[startBeaver:startBeaver+16])
        b.SetBytes(beaversB[startBeaver:startBeaver+16])
        c.SetBytes(beaversC[startBeaver:startBeaver+16])
        prod.Mul(&a, &b)
        prod.Sub(&prod,&c)
        if !prod.IsZero() {
            log.Println(i)
            return false
        }
    }
    
    return true
}*/

//generate permutations and share translations
//returns:
//a permutation for each server 
// a Delta for each server
// initial masks a for each server
// masks a for each server after they permute
// an output b for each server from the last permutation
// a value s that preprocesses input shares for each server's permutation
func GenShareTrans(batchSize, blocksPerRow int, seeds [][]byte) []byte {
    
    numServers := len(seeds)
    perms := make([][]int, numServers)
    aInitial := make([][]byte, numServers)
    aAtPermTime := make([][]byte, numServers)
    bFinal := make([][]byte, numServers)

    //length of db
    dbSize := batchSize*blocksPerRow*16
    
    blocker := make(chan int)
    
    //expand all the seeds
    for serverNum := 0; serverNum < numServers; serverNum++ {
        go func(serverNum int) {
            perms[serverNum] = GenPerm(batchSize, seeds[serverNum][80:96])
            blocker <- 1
        }(serverNum)
        go func(serverNum int) {
            if serverNum > 0 {
                aInitial[serverNum] = AesPRG(dbSize, seeds[serverNum][0:16])
            }
            blocker <- 1
        }(serverNum)
        go func(serverNum int) {
            if serverNum != numServers - 1 {
                bFinal[serverNum] = AesPRG(dbSize, seeds[serverNum][16:32])
            }
            blocker <- 1
        }(serverNum)
        go func(serverNum int) {
            if serverNum != numServers - 1 {
                aAtPermTime[serverNum] = AesPRG(dbSize, seeds[serverNum][32:48])
            }
            blocker <- 1
        }(serverNum)
    }
    
    //wait to finish expansion
    for i:=0; i < 4*numServers; i++ {
        <- blocker
    }
    
    aInitSum := make([]byte, dbSize)
    bFinalSum := make([]byte, dbSize)
    
    //get sums for initial and final parts
    for i:=0; i < numServers; i++ {
        if i != 0 {
            AddOrSub(aInitSum, aInitial[i], true)
        }
        
        if i != numServers - 1 {
            AddOrSub(bFinalSum, bFinal[i], true)
        }
    }

    delta := make([]byte, dbSize)
    temp := aInitSum
    //now just need to compute the very last delta
    for i:=0; i < numServers; i++ {
        if i != numServers - 1 {
            temp = PermuteDB(temp, perms[i])
            AddOrSub(temp, aAtPermTime[i], true)
        } else { // i == numServers -1
            temp = PermuteDB(temp, perms[i])
            //here we actually compute the last delta
            DoubleAddOrSub(delta, temp, bFinalSum, false, false)
        }
    }

    return delta
}


/*func TestGenShareTrans() bool {
    
    batchSize := 100
    blocksPerRow := 64
    numServers := 2
    
    //batchSize 10, blocks per row 5, numServers 2
    perms, aInitial, aAtPermTime, bFinal, sAtPermTime, deltas := GenShareTrans(batchSize, blocksPerRow, numServers)
    
    pis := make([][]int, numServers)
    pis[0] = make([]int, 0)
    pis[1] = make([]int, 0)
    for i:=0; i < batchSize; i++ {
        pis[0] = append(pis[0], byteToInt(perms[0][4*i:4*(i+1)]))
        pis[1] = append(pis[1], byteToInt(perms[1][4*i:4*(i+1)]))

    }
    //log.Println(pis[0])
    //log.Println(pis[1])

    flatDB := make([]byte, batchSize*blocksPerRow*16)
    
    //make aInitial values negative
    AddOrSub(flatDB, aInitial[1], false)
    
    flatDB = PermuteDB(flatDB, pis[0])
    
    AddOrSub(flatDB, deltas[0], true)
    
    AddOrSub(flatDB, aAtPermTime[0], false)
    
    //server 1 starts here
    AddOrSub(flatDB, sAtPermTime[1], true)
    
    flatDB = PermuteDB(flatDB, pis[1])
        
    AddOrSub(flatDB, deltas[1], true)
    
    AddOrSub(flatDB, bFinal[0], true)
    
    zero := make([]byte, batchSize*blocksPerRow*16)
    
    return bytes.Equal(flatDB, zero)
}*/


func PermuteDB(flatDB []byte, pi []int) []byte{
    rowLen := len(flatDB)/len(pi)

    permutedDB := make([]byte, len(flatDB))
    

    //permute
    for i:= 0; i < len(pi); i++ {
        copy(permutedDB[i*rowLen:(i+1)*rowLen], flatDB[pi[i]*rowLen:(pi[i]+1)*rowLen])
    }
    
    return permutedDB
}

//hash an already flattened db
func Hash(flatDB []byte) []byte {
    
    numThreads, chunkSize := PickNumThreads(len(flatDB))
    subHashes := make([]byte, numThreads*32)
    blocker := make(chan int)
    
    for i:=0; i < numThreads; i++ {
        startIndex := i*chunkSize
        endIndex := (i+1)*chunkSize
        go func(index, start, end int) {
            subHash := sha256.Sum256(flatDB[start:end])
            copy(subHashes[index*32:(index+1)*32], subHash[:])
            blocker <- 1
        }(i, startIndex, endIndex)
    }
    
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
    
    hash := sha256.Sum256(subHashes)
    return hash[:]
}

//ended up not helping, so I won't use this
//hash only through the first message block of each row
func HashOnlyBeginning(flatDB []byte, batchSize, msgBlocks, blocksPerRow int) []byte {
    numThreads, chunkSize := PickNumThreads(batchSize)
    subHashes := make([]byte, numThreads*32)
    blocker := make(chan int)
    
    for i:=0; i < numThreads; i++ {
        startIndex := i*chunkSize
        endIndex := (i+1)*chunkSize
        go func(index, start, end int) {
            partLen := (blocksPerRow - msgBlocks)*16
            partsToHash := make([]byte, chunkSize*partLen)
            for j:=0; j < chunkSize; j++ {
                dbIndex := start*blocksPerRow*16 + j*blocksPerRow*16
                copy(partsToHash[j*partLen:(j+1)*partLen], flatDB[dbIndex:dbIndex+partLen])
            }
            subHash := sha256.Sum256(partsToHash)
            copy(subHashes[index*32:(index+1)*32], subHash[:])
            blocker <- 1
        }(i, startIndex, endIndex)
    }
    
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
    
    hash := sha256.Sum256(subHashes)
    return hash[:]
}

//check hashes of many flat DBs
func CheckHashes(hashes, dbs []byte, dbLen, myNum int) bool {
    
    resChan := make(chan bool)
    res := true
    
    for i:=0; i < len(hashes)/32; i++ {
        if i == myNum {
            continue
        }
        go func(index int) {
            hash := Hash(dbs[dbLen*index:dbLen*(index+1)])
            if bytes.Equal(hashes[32*index:32*(index+1)], hash[:]) {
                resChan <- true
            } else {
                resChan <- false
            }
        }(i)
    }
    
    for i:=1; i < len(hashes)/32; i++ {
        res = res && <- resChan
    }
    return res
}

//check that shares sum to zero
func CheckSharesAreZero(batchSize, numServers int, shares []byte) bool {
    
    numThreads, chunkSize := PickNumThreads(batchSize)
    res := true;
    resChan := make(chan bool)
    
    for t:=0; t < numThreads; t++ {
        startIndex := t*chunkSize
        endIndex := (t+1)*chunkSize
        go func(startI, endI int) {
            var hopefullyZero, anotherShare modp.Element
            innerRes := true
            for i:=startI; i < endI; i++ {
                hopefullyZero.SetBytes(shares[16*i:16*(i+1)])
                for j:=1; j < numServers; j++ {
                    index := j*16*batchSize + 16*i
                    anotherShare.SetBytes(shares[index:index+16])
                    hopefullyZero.Add(&anotherShare, &hopefullyZero)
                }
                if !hopefullyZero.IsZero() {
                    innerRes = false
                }
            }
            resChan <- innerRes
        }(startIndex, endIndex)
    }
    
    for i:=0; i < numThreads; i++ {
        res = res && <- resChan
    }
    
    return res;
}

func TestCheckSharesAreZero() bool {
    batchSize := 5
    numServers := 2
    
    zeroVals := make([]byte, 16*batchSize)
    
    shares := Share(numServers, zeroVals)

    flatShares := make([]byte, 0)
    for i:=0; i < len(shares); i++ {
        flatShares = append(flatShares, shares[i]...)
    }
    
    return CheckSharesAreZero(batchSize, numServers, flatShares)
}

func BeaverProduct(msgBlocks, batchSize int, beaversC, mergedMaskedShares []byte,  db [][]byte, leader, aggregate bool) []byte {

    keyBlocks := msgBlocks
    
    //locally compute product shares and share of mac, subtract from share of given tag
    macDiffShares := make([]byte, 0)
    blocker := make(chan int)
    numThreads, chunkSize := PickNumThreads(batchSize)
    if aggregate {
        macDiffShares = make([]byte, 16*numThreads)
    } else {
        macDiffShares = make([]byte, 16*batchSize)
    }
    
    for t:=0; t < numThreads; t++ {
        startIndex := t*chunkSize
        endIndex := (t+1)*chunkSize
        go func(start, end, threadIndex int) {
            var aggregateRunningSum modp.Element
            for i:=start; i < end; i++ {
                var maskedKey, myKeyShare, maskedMsg, myMsgShare, givenTag, temp modp.Element
                var runningSum, beaverProductShare modp.Element
                for j:=0; j < keyBlocks; j++ {
                    //do a beaver multiplication here
                    keyShareIndex := 16*msgBlocks + 16*j
                    myKeyShare.SetBytes(db[i][keyShareIndex:keyShareIndex+16])
                    myMsgShare.SetBytes(db[i][16*j:16*(j+1)])
                    keyIndex := i*16*keyBlocks + 16*j
                    msgIndex := len(mergedMaskedShares)/2 + keyIndex
                    maskedKey.SetBytes(mergedMaskedShares[keyIndex:keyIndex+16])
                    maskedMsg.SetBytes(mergedMaskedShares[msgIndex:msgIndex+16])
                    
                    if leader {
                        beaverProductShare.Mul(&maskedKey, &maskedMsg)
                    } else {
                        beaverProductShare.SetZero()
                    }
                    maskedKey.Mul(&maskedKey, &myMsgShare) //this now holds a product, not a masked key
                    maskedMsg.Mul(&maskedMsg, &myKeyShare) //this now holds a product, not a masked msg
                    beaverProductShare.Sub(&maskedKey, &beaverProductShare)
                    beaverProductShare.Add(&beaverProductShare, &maskedMsg)
                    beaverIndex := 16*keyBlocks*i + 16*j
                    temp.SetBytes(beaversC[beaverIndex:beaverIndex+16])
                    beaverProductShare.Add(&beaverProductShare, &temp)
                    
                    runningSum.Add(&runningSum, &beaverProductShare)
                }
                
                givenTag.SetBytes(db[i][msgBlocks*16:msgBlocks*16 + 16])
                runningSum.Sub(&runningSum, &givenTag)
                
                if aggregate {
                    aggregateRunningSum.Add(&aggregateRunningSum, &runningSum)
                } else {
                    copy(macDiffShares[16*i:16*(i+1)], runningSum.Bytes())
                }
            }
            if aggregate {
                copy(macDiffShares[16*threadIndex:16*(threadIndex+1)], aggregateRunningSum.Bytes())
            }
            blocker <- 1
        }(startIndex, endIndex, t)
    }
    
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
    
    return macDiffShares
}

//get all the masked stuff together for the blind mac verification
func GetMaskedStuff(batchSize, msgBlocks, myNum int, beaversA, beaversB []byte, db [][]byte) []byte {
    
    keyBlocks := msgBlocks
    
    maskedMsgShares := make([]byte, 16*batchSize*keyBlocks)
    
    maskedExpandedKeyShares := make([]byte, 16*batchSize*keyBlocks)
    
    numThreads, chunkSize := PickNumThreads(batchSize)
    blocker := make(chan int)
    
    for t:= 0; t < numThreads; t++ {
        startIndex := chunkSize*t
        endIndex := chunkSize*(t+1)
        go func(startI, endI int) {
            var value, mask modp.Element
            for i:=startI; i < endI; i++ {
                for j:=0; j < keyBlocks; j++ {
                    //mask the key component
                    keyShareIndex := 16*msgBlocks + 16*j
                    value.SetBytes(db[i][keyShareIndex:keyShareIndex+16])
                    beaverIndex := 16*keyBlocks*i + 16*j
                    mask.SetBytes(beaversA[beaverIndex:beaverIndex+16])
                    value.Sub(&value, &mask)
                    index := 16*keyBlocks*i + 16*j
                    copy(maskedExpandedKeyShares[index:index+16], value.Bytes())
                    
                    //mask the message component
                    value.SetBytes(db[i][16*j:16*(j+1)])
                    mask.SetBytes(beaversB[beaverIndex:beaverIndex+16])
                    value.Sub(&value,&mask)
                    copy(maskedMsgShares[index:index+16], value.Bytes())
                }
            }
            blocker <- 1
        }(startIndex, endIndex)
    }
    
    for i:=0; i < numThreads; i++ {
        <- blocker
    }
    
    maskedStuff := append(maskedExpandedKeyShares, maskedMsgShares...)
    return maskedStuff
}
