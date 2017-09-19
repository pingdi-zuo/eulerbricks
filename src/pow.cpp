// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "pow.h"

#include "arith_uint256.h"
#include "chain.h"
#include "primitives/block.h"
#include "uint256.h"

unsigned int GetNextWorkRequired(const CBlockIndex* pindexLast, const CBlockHeader *pblock, const Consensus::Params& params)
{
    unsigned int nProofOfWorkLimit = UintToArith256(params.powLimit).GetCompact();
    return nProofOfWorkLimit;

	/*

    // Genesis block
    if (pindexLast == NULL || pindexLast->nHeight <= 1)
        return nProofOfWorkLimit;

    // Only change once per difficulty adjustment interval
    if ((pindexLast->nHeight+1) % params.DifficultyAdjustmentInterval() != 0)
    {
        if (params.fPowAllowMinDifficultyBlocks)
        {
            // Special difficulty rule for testnet:
            // If the new block's timestamp is more than 2* 10 minutes
            // then allow mining of a min-difficulty block.
            if (pblock->GetBlockTime() > pindexLast->GetBlockTime() + params.nPowTargetSpacing*2)
                return nProofOfWorkLimit;
            else
            {
                // Return the last non-special-min-difficulty-rules-block
                const CBlockIndex* pindex = pindexLast;
                while (pindex->pprev && pindex->nHeight % params.DifficultyAdjustmentInterval() != 0 && pindex->nBits == nProofOfWorkLimit)
                    pindex = pindex->pprev;
                return pindex->nBits;
            }
        }
        return pindexLast->nBits;
    }

    // Go back by what we want to be 14 days worth of blocks
    int nHeightFirst = pindexLast->nHeight - (params.DifficultyAdjustmentInterval()-1);
    assert(nHeightFirst >= 0);
    const CBlockIndex* pindexFirst = pindexLast->GetAncestor(nHeightFirst);
    assert(pindexFirst);

    return CalculateNextWorkRequired(pindexLast, pindexFirst->GetBlockTime(), params);
	*/
}

unsigned int CalculateNextWorkRequired(const CBlockIndex* pindexLast, int64_t nFirstBlockTime, const Consensus::Params& params)
{
    unsigned int nProofOfWorkLimit = UintToArith256(params.powLimit).GetCompact();
    return nProofOfWorkLimit;
	
	/*
    if (params.fPowNoRetargeting)
        return pindexLast->nBits;

    // Limit adjustment step
    int64_t nActualTimespan = pindexLast->GetBlockTime() - nFirstBlockTime;
    if (nActualTimespan < params.nPowTargetTimespan/4)
        nActualTimespan = params.nPowTargetTimespan/4;
    if (nActualTimespan > params.nPowTargetTimespan*4)
        nActualTimespan = params.nPowTargetTimespan*4;

    // Retarget
    const arith_uint256 bnPowLimit = UintToArith256(params.powLimit);
    arith_uint256 bnNew;
    bnNew.SetCompact(pindexLast->nBits);
    bnNew *= nActualTimespan;
    bnNew /= params.nPowTargetTimespan;

    if (bnNew > bnPowLimit)
        bnNew = bnPowLimit;

    return bnNew.GetCompact();
	*/
}

bool CheckProofOfWorkHash(uint256 hash, /* unsigned int nBits, */ const Consensus::Params& params)
{
    arith_uint256 nProofOfWorkLimit = UintToArith256(params.powLimit);
    if (UintToArith256(hash) > nProofOfWorkLimit)
        return false;

    return true;

	/*
    bool fNegative;
    bool fOverflow;
    arith_uint256 bnTarget;

    bnTarget.SetCompact(nBits, &fNegative, &fOverflow);

    // Check range
    if (fNegative || bnTarget == 0 || fOverflow || bnTarget > UintToArith256(params.powLimit))
        return false;

    // Check proof of work matches claimed amount
    if (UintToArith256(hash) > bnTarget)
        return false;

    return true;
	*/
}

int mod2(int a, int b) {
    int c = b % a;
    if (c == 0) 
        return a;
    else
        return mod2(c, a);
}

int mod3(int a, int b, int c) {
    return mod2(mod2(a, b), c);
}

uint64_t mod2(uint64_t a, uint64_t b) {
    uint64_t c = b % a;
    if (c == 0) 
        return a;
    else
        return mod2(c, a);
}

uint64_t mod3(uint64_t a, uint64_t b, uint64_t c) {
    return mod2(mod2(a, b), c);
}

boost::multiprecision::uint1024_t mod2(boost::multiprecision::uint1024_t a, boost::multiprecision::uint1024_t b) {
    boost::multiprecision::uint1024_t c = b % a;
    if (c == 0) 
        return a;
    else
        return mod2(c, a);
}

boost::multiprecision::uint1024_t mod3(boost::multiprecision::uint1024_t a, boost::multiprecision::uint1024_t b, boost::multiprecision::uint1024_t c) {
    return mod2(mod2(a, b), c);
}

boost::multiprecision::cpp_int mod2(boost::multiprecision::cpp_int a, boost::multiprecision::cpp_int b) {
    boost::multiprecision::cpp_int c = b % a;
    if (c == 0) 
        return a;
    else
        return mod2(c, a);
}

boost::multiprecision::cpp_int mod3(boost::multiprecision::cpp_int a, boost::multiprecision::cpp_int b, boost::multiprecision::cpp_int c) {
    return mod2(mod2(a, b), c);
}

int CheckProofOfWork(const CBlockHeader& block, const Consensus::Params& params)
{
	if (!CheckProofOfWorkHash(block.GetHash(), params))
		return 0;

	return CheckProofOfWork(block);
}

int CheckProofOfWork(const CBlockHeader& block)
{
    if (block.nA > block.nB || block.nB > block.nC || block.nA > block.nC)
        return 0;

    if (!(block.nA.n == 0 && block.nB.n == 0 && block.nC.n == 0)) {
        if (block.nA.n * block.nB.n * block.nC.n == 0)
			return 0;

        if (mod3(block.nA.n, block.nB.n, block.nC.n) > 1)
            return 0;
    } else if (block.hashPrevBlock == uint256S("0000000000000000000000000000000000000000000000000000000000000000") && block.GetHash() == uint256S("000000d888b136a4e59e86a3cd70c550968e686e9214c43ce4d2397a47d087f7)")) {
		return 1;
	}

    if ((block.nA.n * block.nA.n + block.nB.n * block.nB.n == block.nD.n * block.nD.n) && 
        (block.nB.n * block.nB.n + block.nC.n * block.nC.n == block.nE.n * block.nE.n) && 
        (block.nC.n * block.nC.n + block.nA.n * block.nA.n == block.nF.n * block.nF.n)) {
        // find perfect brick?
        if ((block.nA.n * block.nA.n + block.nB.n * block.nB.n + block.nC.n * block.nC.n == block.nG.n * block.nG.n)) {
            return 1000000;
        }
        return 1;
    } else {
        return 0;
    }
}
