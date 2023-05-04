package mycrypto

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/sha256"
	"log"
	"math/big"

	"shufflemessage/modp"
)

const blockSize = 128

// p = 2**1017 + 422487
// q = 2**1016 + 211243
// accept messages up to 1016 bits (127 bytes)

var q, _ = new(big.Int).SetString("702223880805592151456759840151962786569522257399338504974336254522393264865238137237142489540654437582500444843247630303354647534431314931612685275935445798350655833690880801860555545317367555154113605281582053784524026102900245630757473088050106395169337932361665227499793929447186391815763110662594836779", 10)

// find the group generator where
// 1) g^((p-1)/2) = 1 (mod p)
// 2) the discrete log between them are non-trivial
// g1, g2, g3 should be randomly chosen in real application

const g1 = 2
const g2 = 3
const g3 = 5

var g1Element = modp.Element{
    g1,
}

var g2Element = modp.Element{
    g2,
}

var g3Element = modp.Element{
    g3,
}

var Order = q
var G3 = g3Element.Bytes()

func ElementString(m []byte) string {
    var temp modp.Element
    temp.SetBytes(m)
    return temp.String()
}

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

    copyBigInt(secret, blockSize, s1)
    copyBigInt(secret, blockSize*2, s2)
    return id.Bytes(), secret
}

//return a message
func MakeMsg(msgType int) []byte {
    m := make([]byte, blockSize)
    for i := 1; i < blockSize; i++ {
        m[i] = byte(97 + msgType) //ascii 'a' is 97
    }
    
    return m
}

//return a message and the backdoor
func MakeFullMsg(msgType int, secret []byte) []byte {
    ret := make([]byte, blockSize * 2)
    
    m := make([]byte, blockSize)
    for i := 1; i < blockSize; i++ {
        m[i] = byte(97 + msgType) //ascii 'a' is 97
    }

    // generate the backdoor
    s1 := new(big.Int).SetBytes(secret[:blockSize])
    s2 := new(big.Int).SetBytes(secret[blockSize:])
    var mElement, M, temp modp.Element
    mElement.SetBytes(m)
    M.Exp(mElement, q)
    // log.Print(M.ToRegular())
    temp = modp.One()
    if !M.Equal(&temp) {
        mElement.Neg(&mElement)
    }
    // M.Exp(mElement, q)
    // log.Print(M.ToRegular())
    M.Exp(mElement, s1)
    temp.Exp(g3Element, s2)
    M.Mul(&M, &temp)

    copy(ret[:blockSize], mElement.Bytes())
    copy(ret[blockSize:blockSize*2], M.Bytes())
    
    return ret
}

func CheckMsgSecret(message, secret []byte) bool {
    var mElement, MElement, temp modp.Element
    mElement.SetBytes(message[:blockSize])
    MElement.SetBytes(message[blockSize:])
    s1 := new(big.Int).SetBytes(secret[:blockSize])
    s2 := new(big.Int).SetBytes(secret[blockSize:])
    mElement.Exp(mElement, s1)
    temp.Exp(g3Element, s2)
    temp.Mul(&mElement, &temp)
    return temp.Equal(&MElement)
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
        copy(coms[startIndex:endIndex], ComHash(data))
    }
    hash := Hash(coms)
    ch := new(big.Int).SetBytes(AesPRG(blockSize, hash))
    ch.Mod(ch, q)

    s1 := new(big.Int).SetBytes(secret[:blockSize])
    s2 := new(big.Int).SetBytes(secret[blockSize:])
    z1, z2 := big.NewInt(0), big.NewInt(0)
    z1.Mul(ch, s1)
    z1.Add(z1, r1)
    z1.Mod(z1, q)
    z2.Mul(ch, s2)
    z2.Add(z2, r2)
    z2.Mod(z2, q)

    copy(ret[:blockSize], a.Bytes())
    copyBigInt(ret, blockSize*2, z1)
    copyBigInt(ret, blockSize*3, z2)

    temp.Exp(g1Element, z1)
    temp.Exp(g2Element, z2)
    return bShares, ret
}

// data should be m_i | M_i | b | id | a
func ComHash(data []byte) []byte {
    hash := sha256.Sum256(data)
    return hash[:]
}

// data should be id | a | z1 | z2
func CheckFirstProof(data, ch []byte) bool {
    z1 := new(big.Int).SetBytes(data[blockSize*2:blockSize*3])
    z2 := new(big.Int).SetBytes(data[blockSize*3:blockSize*4])
    chNum := new(big.Int).SetBytes(ch)
    var id, a, lhs, rhs, temp modp.Element
    id.SetBytes(data[:blockSize])
    a.SetBytes(data[blockSize:blockSize*2])
    lhs.Exp(g1Element, z1)
    temp.Exp(g2Element, z2)
    lhs.Mul(&lhs, &temp)
    rhs.Exp(id, chNum)
    rhs.Mul(&rhs, &a)
    if lhs.Equal(&rhs) {
        return true
    } else {
        return false
    }
}

func GenExpNegShares(numServers int, exponent []byte) [][]byte {
    var r modp.Element
    r.SetRandom()
    rShares := Share(numServers, r.Bytes())
    exp := new(big.Int).SetBytes(exponent)
    order := big.NewInt(0)
    order.Mul(q, big.NewInt(2))
    exp.Mod(exp, order)
    exp.Sub(order, exp)
    r.Exp(r, exp)
    
    rExpShares := Share(numServers, r.Bytes())
    for i:=0; i < numServers; i++ {
        rShares[i] = append(rShares[i], rExpShares[i]...)
    }
    return rShares
}

// return (base^exponent)<a>
func MulScalarExp(a, base, exponent []byte) {
    var scalar modp.Element
    scalar.SetBytes(base)
    exp := new(big.Int).SetBytes(exponent)
    scalar.Exp(scalar, exp)

    numBlocks := len(a)/blockSize
    
    numThreads,chunkSize := PickNumThreads(numBlocks)
    
    blocker := make(chan int)
    
    for j:=0; j < numThreads; j++ {
        startIndex := j*chunkSize
        endIndex := (j+1)*chunkSize
        go func(startI, endI int) {
            var eltA modp.Element
            for i :=startI; i < endI; i++ {
                eltA.SetBytes(a[blockSize*i:blockSize*(i+1)])
                eltA.Mul(&eltA, &scalar)
                copy(a[blockSize*i:blockSize*(i+1)], eltA.Bytes())
            }
            blocker <- 1
        }(startIndex, endIndex)
    }
    
    for i:= 0; i < numThreads; i++ {
        <- blocker
    }
}

/*func TestExp() bool {
    numServers := 2
    numBeavers := 3
    var m, rC, rexpC, mrC, mexpC, temp modp.Element
    m.SetRandom()
    mShares := Share(numServers, m.Bytes())
    
    z1, _ := rand.Int(rand.Reader, q)
    exp := make([]byte, blockSize)
    copyBigInt(exp, blockSize, z1)

    r := make([][]byte, numServers)
    rexp := make([][]byte, numServers)
    mr := make([][]byte, numServers)
    for i:=0; i<numServers; i++ {
        r[i] = make([]byte, blockSize*2)
        rexp[i] = make([]byte, blockSize*2)
        mr[i] = make([]byte, blockSize*2)
    }
    for i:=0; i<2; i++ {
        shares := GenExpNegShares(numServers, exp)
        for j:=0; j<numServers; j++ {
            copy(r[j][blockSize*i:blockSize*(i+1)], shares[j][:blockSize])
            copy(rexp[j][blockSize*i:blockSize*(i+1)], shares[j][blockSize:])
        }
    }

    seeds := make([][]byte, numServers)
    beaversAs := make([][]byte, numServers)
    beaversBs := make([][]byte, numServers)
    for i:=0; i<numServers; i++ {
        seeds[i] = make([]byte, 32)
        rand.Read(seeds[i][:])
        beaversAs[i] = AesPRG(numBeavers*blockSize, seeds[i][:16])
        beaversBs[i] = AesPRG(numBeavers*blockSize, seeds[i][16:32])
    }
    beaversCs := GenBeavers(numBeavers, 0, seeds)

    maskStuffs := make([][]byte, numServers)
    for i:=0; i<numServers; i++ {
        maskStuffs[i] = GetMaskedStuff(i, beaversAs[i][:blockSize], beaversBs[i][:blockSize], r[i])
    }
    mergedMaskedShares := Merge(maskStuffs)

    productShares := make([][]byte, numServers)
    for i:=0; i<numServers; i++ {
        leader := (i==0)
        productShares[i] = BeaverProduct(beaversCs[i][:blockSize], mergedMaskedShares, r[i], leader)
    }
    rComputed := Merge(productShares)
    rC.SetBytes(rComputed)
    log.Printf("r = %s\n", rC.String())
    temp.Exp(rC, z1)
    log.Printf("r^z1 = %s\n", temp.String())

    for i:=0; i<numServers; i++ {
        copy(mr[i][:blockSize], productShares[i])
        copy(mr[i][blockSize:blockSize*2], mShares[i])
    }

    for i:=0; i<numServers; i++ {
        maskStuffs[i] = GetMaskedStuff(i, beaversAs[i][blockSize*2:blockSize*3], beaversBs[i][blockSize*2:blockSize*3], mr[i])
    }
    mergedMaskedShares = Merge(maskStuffs)

    for i:=0; i<numServers; i++ {
        leader := (i==0)
        productShares[i] = BeaverProduct(beaversCs[i][blockSize*2:blockSize*3], mergedMaskedShares, mr[i], leader)
    }

    mrComputed := Merge(productShares)
    mrC.SetBytes(mrComputed)
    log.Printf("mr = %s\n", mrC.String())
    temp.Exp(mrC, z1)
    log.Printf("(mr)^z1 = %s\n", temp.String())

    for i:=0; i<numServers; i++ {
        maskStuffs[i] = GetMaskedStuff(i, beaversAs[i][blockSize:blockSize*2], beaversBs[i][blockSize:blockSize*2], rexp[i])
    }
    mergedMaskedShares = Merge(maskStuffs)
    
    for i:=0; i<numServers; i++ {
        leader := (i==0)
        productShares[i] = BeaverProduct(beaversCs[i][blockSize:blockSize*2], mergedMaskedShares, rexp[i], leader)
    }
    
    rexpComputed := Merge(productShares)
    rexpC.SetBytes(rexpComputed)
    log.Printf("r^{-z1} = %s\n", rexpC.String())

    for i:=0; i<numServers; i++ {
        log.Printf("[r^{-z1}]_%d = %s\n", i, ElementString(productShares[i]))
        MulScalarExp(productShares[i], mrComputed, z1.Bytes())
        log.Printf("(mr)^z1[r^{-z1}]_%d = %s\n", i, ElementString(productShares[i]))
    }
    mexpComputed := Merge(productShares)
    mexpC.SetBytes(mexpComputed)
    log.Printf("m^{z1} = %s\n", mexpC.String())

    temp.Exp(mrC, z1)
    log.Printf("mr^{z1} = %s\n", temp.String())
    temp.Mul(&temp, &rexpC)
    log.Printf("mr^{z1}r^{-z1} = m^z1 = %s\n", temp.String())
    m.Exp(m, z1)
    return mexpC.Equal(&m)
}*/

func copyBigInt(db []byte, baseIndex int, number *big.Int) {
    numBytes := number.Bytes()
    length := len(numBytes)
    copy(db[baseIndex - length:baseIndex], numBytes)
}

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
    // return 1, size
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
    
    return numThreads, size/numThreads
}

func AddOrSub(a, b []byte, add bool) {
    numBlocks := len(a)/blockSize
    
    numThreads,chunkSize := PickNumThreads(numBlocks)
    
    blocker := make(chan int)
    
    for j:=0; j < numThreads; j++ {
        startIndex := j*chunkSize
        endIndex := (j+1)*chunkSize
        go func(startI, endI int) {
            var eltA, eltB modp.Element
            for i :=startI; i < endI; i++ {
                eltA.SetBytes(a[blockSize*i:blockSize*(i+1)])
                eltB.SetBytes(b[blockSize*i:blockSize*(i+1)])
                
                if add {
                    eltA.Add(&eltA, &eltB)
                } else {
                    eltA.Sub(&eltA, &eltB)
                }
                
                copy(a[blockSize*i:blockSize*(i+1)], eltA.Bytes())
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
    numBlocks := len(a)/blockSize
    
    numThreads,chunkSize := PickNumThreads(numBlocks)
    
    blocker := make(chan int)
    
    for j:=0; j < numThreads; j++ {
        startIndex := j*chunkSize
        endIndex := (j+1)*chunkSize
        go func(startI, endI int) {
            var eltA, eltB, eltC modp.Element
            for i :=startI; i < endI; i++ {
                eltA.SetBytes(a[blockSize*i:blockSize*(i+1)])
                eltB.SetBytes(b[blockSize*i:blockSize*(i+1)])
                eltC.SetBytes(c[blockSize*i:blockSize*(i+1)])
                
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
                
                copy(a[blockSize*i:blockSize*(i+1)], eltA.Bytes())
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
    beaversC := make([]byte, numBeavers*blockSize)
    beaversA := make([][]byte, numServers)
    beaversB := make([][]byte, numServers)

    
    numThreads, chunkSize := PickNumThreads(numBeavers)
    blocker := make(chan int)
    
    //expand a and b shares
    for i:=0; i < numServers; i++ {
        go func(index int) {
            beaversA[index] = AesPRG(blockSize*numBeavers, seeds[index][seedIndex:seedIndex+16])
            blocker <- 1
        }(i)
        go func(index int) {
            beaversB[index] = AesPRG(blockSize*numBeavers, seeds[index][seedIndex+16:seedIndex+32])
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
                eltA.SetBytes(beaversAMerged[i*blockSize:(i+1)*blockSize])
                eltB.SetBytes(beaversBMerged[i*blockSize:(i+1)*blockSize])
                eltC.Mul(&eltA, &eltB)
                copy(beaversC[blockSize*i:blockSize*(i+1)], eltC.Bytes())
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
    dbSize := batchSize*blocksPerRow*blockSize
    
    blocker := make(chan int)
    
    //expand all the seeds
    for serverNum := 0; serverNum < numServers; serverNum++ {
        go func(serverNum int) {
            perms[serverNum] = GenPerm(batchSize, seeds[serverNum][0:16])
            blocker <- 1
        }(serverNum)
        go func(serverNum int) {
            if serverNum > 0 {
                aInitial[serverNum] = AesPRG(dbSize, seeds[serverNum][16:32])
            }
            blocker <- 1
        }(serverNum)
        go func(serverNum int) {
            if serverNum != numServers - 1 {
                bFinal[serverNum] = AesPRG(dbSize, seeds[serverNum][32:48])
            }
            blocker <- 1
        }(serverNum)
        go func(serverNum int) {
            if serverNum != numServers - 1 {
                aAtPermTime[serverNum] = AesPRG(dbSize, seeds[serverNum][48:64])
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
                hopefullyZero.SetBytes(shares[blockSize*i:blockSize*(i+1)])
                for j:=1; j < numServers; j++ {
                    index := j*blockSize*batchSize + blockSize*i
                    anotherShare.SetBytes(shares[index:index+blockSize])
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

/*func TestCheckSharesAreZero() bool {
    batchSize := 5
    numServers := 2
    
    zeroVals := make([]byte, 16*batchSize)
    
    shares := Share(numServers, zeroVals)

    flatShares := make([]byte, 0)
    for i:=0; i < len(shares); i++ {
        flatShares = append(flatShares, shares[i]...)
    }
    
    return CheckSharesAreZero(batchSize, numServers, flatShares)
}*/

func CheckSharesAreOne(batchSize, numServers int, shares []byte) bool {
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
                hopefullyZero.SetBytes(shares[blockSize*i:blockSize*(i+1)])
                // log.Print(hopefullyZero)
                // log.Print(hopefullyZero.ToRegular())
                for j:=1; j < numServers; j++ {
                    index := j*blockSize*batchSize + blockSize*i
                    anotherShare.SetBytes(shares[index:index+blockSize])
                    hopefullyZero.Add(&anotherShare, &hopefullyZero)
                }
                // log.Print(hopefullyZero)
                // log.Print(hopefullyZero.ToRegular())
                one := modp.One()
                if !hopefullyZero.Equal(&one) {
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

func BeaverProduct(beaversC, mergedMaskedShares, db []byte, leader bool) []byte {
    var maskedKey, myKeyShare, maskedMsg, myMsgShare, temp, beaverProductShare modp.Element
    
    macDiffShares := make([]byte, blockSize)
    myKeyShare.SetBytes(db[blockSize:blockSize*2])
    myMsgShare.SetBytes(db[:blockSize])
    maskedKey.SetBytes(mergedMaskedShares[:blockSize])
    maskedMsg.SetBytes(mergedMaskedShares[blockSize:blockSize*2])

    if leader {
        beaverProductShare.Mul(&maskedKey, &maskedMsg)
    } else {
        beaverProductShare.SetZero()
    }
    maskedKey.Mul(&maskedKey, &myMsgShare) //this now holds a product, not a masked key
    maskedMsg.Mul(&maskedMsg, &myKeyShare) //this now holds a product, not a masked msg
    beaverProductShare.Sub(&maskedKey, &beaverProductShare)
    beaverProductShare.Add(&beaverProductShare, &maskedMsg)
    temp.SetBytes(beaversC[:blockSize])
    beaverProductShare.Add(&beaverProductShare, &temp)

    copy(macDiffShares[:blockSize], beaverProductShare.Bytes())
    return macDiffShares
}

//get the masked stuff
func GetMaskedStuff(myNum int, beaversA, beaversB, db []byte) []byte {
    var value, mask modp.Element
    
    maskedMsgShares := make([]byte, blockSize)
    maskedExpandedKeyShares := make([]byte, blockSize)

    //mask the key component
    value.SetBytes(db[blockSize:blockSize*2])
    mask.SetBytes(beaversA[:blockSize])
    value.Sub(&value, &mask)
    copy(maskedExpandedKeyShares[:blockSize], value.Bytes())
    
    //mask the message component
    value.SetBytes(db[:blockSize])
    mask.SetBytes(beaversB[:blockSize])
    value.Sub(&value,&mask)
    copy(maskedMsgShares[:blockSize], value.Bytes())

    maskedStuff := append(maskedExpandedKeyShares, maskedMsgShares...)
    return maskedStuff
}
