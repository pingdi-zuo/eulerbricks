// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_PRIMITIVES_BLOCK_H
#define BITCOIN_PRIMITIVES_BLOCK_H

#include "primitives/transaction.h"
#include "serialize.h"
#include "uint256.h"
#include <boost/multiprecision/cpp_int.hpp>

/** Nodes collect new transactions into a block, hash them into a hash tree,
 * and scan through nonce values to make the block's hash satisfy proof-of-work
 * requirements.  When they solve the proof-of-work, they broadcast the block
 * to everyone and the block is added to the block chain.  The first transaction
 * in the block is a special one that creates a new coin owned by the creator
 * of the block.
 */
class my_cpp_int {
public:
	boost::multiprecision::cpp_int n;
    my_cpp_int()
    {
		n = 0;
    }
    my_cpp_int(int n1)
    {
		n = n1;
    }
    my_cpp_int(int64_t n1)
    {
		n = n1;
    }
    my_cpp_int(uint8_t n1)
    {
		n = n1;
    }
    my_cpp_int(uint16_t n1)
    {
		n = n1;
    }
    my_cpp_int(uint32_t n1)
    {
		n = n1;
    }
    my_cpp_int(uint64_t n1)
    {
		n = n1;
    }
    my_cpp_int(boost::multiprecision::cpp_int n1)
    {
		n = n1;
    }

    friend inline bool operator==(const my_cpp_int& a, const my_cpp_int& b) { return a.n == b.n; }
    friend inline bool operator!=(const my_cpp_int& a, const my_cpp_int& b) { return a.n != b.n; }
    friend inline bool operator<(const my_cpp_int& a, const my_cpp_int& b) { return a.n < b.n; }
    friend inline bool operator>(const my_cpp_int& a, const my_cpp_int& b) { return a.n > b.n; }

	my_cpp_int& operator=(const my_cpp_int &r) {
		(*this).n = r.n;
		return *this;
	}
	my_cpp_int& operator=(uint8_t &r) {
		(*this).n = r;
		return *this;
	}
	my_cpp_int& operator=(uint16_t &r) {
		(*this).n = r;
		return *this;
	}
	my_cpp_int& operator=(uint32_t &r) {
		(*this).n = r;
		return *this;
	}
	my_cpp_int& operator=(uint64_t &r) {
		(*this).n = r;
		return *this;
	}
	my_cpp_int& operator=(const boost::multiprecision::cpp_int &r) {
		(*this).n = r;
		return *this;
	}
	
	operator boost::multiprecision::cpp_int() {return n;}

    template<typename Stream>
    void Serialize(Stream& s) const {
		s << n.str();
    }

    template<typename Stream>
    void Unserialize(Stream& s) {
		std::string s1;
		s >> s1;
		n.assign(s1);
    }

	/*
    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action, int nType, int nVersion) {
        READWRITE(this->n);
	}
	*/
};

class CBlockHeader
{
public:
    // header
    int32_t nVersion;
    uint256 hashPrevBlock;
    uint256 hashMerkleRoot;
    uint32_t nTime;
    uint32_t nBits;
    uint32_t nNonce;
    my_cpp_int nA;
    my_cpp_int nB;
    my_cpp_int nC;
    my_cpp_int nD;
    my_cpp_int nE;
    my_cpp_int nF;
    my_cpp_int nG;

    CBlockHeader()
    {
        SetNull();
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITE(this->nVersion);
        READWRITE(hashPrevBlock);
        READWRITE(hashMerkleRoot);
        READWRITE(nTime);
        READWRITE(nBits);
        READWRITE(nNonce);
        READWRITE(nA);
        READWRITE(nB);
        READWRITE(nC);
        READWRITE(nD);
        READWRITE(nE);
        READWRITE(nF);
        READWRITE(nG);
    }

    void SetNull()
    {
        nVersion = 0;
        hashPrevBlock.SetNull();
        hashMerkleRoot.SetNull();
        nTime = 0;
        nBits = 0;
        nNonce = 0;
        nA.n = 0;
        nB.n = 0;
        nC.n = 0;
        nD.n = 0;
        nE.n = 0;
        nF.n = 0;
        nG.n = 0;
    }

    bool IsNull() const
    {
        return (nA.n * nB.n * nC.n == 0 ||
            !((nA.n * nA.n + nB.n * nB.n == nD.n * nD.n) && 
            (nB.n * nB.n + nC.n * nC.n == nE.n * nE.n) && 
            (nC.n * nC.n + nA.n * nA.n == nF.n * nF.n)));
    }

    uint256 GetHash() const;

    int64_t GetBlockTime() const
    {
        return (int64_t)nTime;
    }

    CBlockHeader& operator=(const CBlockHeader &b) {
		nVersion = b.nVersion;
		hashPrevBlock.SetHex(b.hashPrevBlock.GetHex());
		hashMerkleRoot.SetHex(b.hashMerkleRoot.GetHex());
		nTime = b.nTime;
		nBits = b.nBits;
		nNonce = b.nNonce;
		nA = b.nA;
		nB = b.nB;
		nC = b.nC;
		nD = b.nD;
		nE = b.nE;
		nF = b.nF;
		nG = b.nG;
        return *this;
    }
};


class CBlock : public CBlockHeader
{
public:
    // network and disk
    std::vector<CTransactionRef> vtx;

    // memory only
    mutable bool fChecked;

    CBlock()
    {
        SetNull();
    }

    CBlock(const CBlockHeader &header)
    {
        SetNull();
        *((CBlockHeader*)this) = header;
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        READWRITE(*(CBlockHeader*)this);
        READWRITE(vtx);
    }

    void SetNull()
    {
        CBlockHeader::SetNull();
        vtx.clear();
        fChecked = false;
    }

    CBlockHeader GetBlockHeader() const
    {
        CBlockHeader block;
        block.nVersion       = nVersion;
        block.hashPrevBlock  = hashPrevBlock;
        block.hashMerkleRoot = hashMerkleRoot;
        block.nTime          = nTime;
        block.nBits          = nBits;
        block.nNonce         = nNonce;
        block.nA         = nA;
        block.nB         = nB;
        block.nC         = nC;
        block.nD         = nD;
        block.nE         = nE;
        block.nF         = nF;
        block.nG         = nG;
        return block;
    }

    std::string ToString() const;
};

/** Describes a place in the block chain to another node such that if the
 * other node doesn't have the same branch, it can find a recent common trunk.
 * The further back it is, the further before the fork it may be.
 */
struct CBlockLocator
{
    std::vector<uint256> vHave;

    CBlockLocator() {}

    CBlockLocator(const std::vector<uint256>& vHaveIn)
    {
        vHave = vHaveIn;
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream& s, Operation ser_action) {
        int nVersion = s.GetVersion();
        if (!(s.GetType() & SER_GETHASH))
            READWRITE(nVersion);
        READWRITE(vHave);
    }

    void SetNull()
    {
        vHave.clear();
    }

    bool IsNull() const
    {
        return vHave.empty();
    }
};

/** Compute the consensus-critical block weight (see BIP 141). */
int64_t GetBlockWeight(const CBlock& tx);

#endif // BITCOIN_PRIMITIVES_BLOCK_H
