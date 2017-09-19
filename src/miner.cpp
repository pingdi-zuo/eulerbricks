// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "miner.h"

#include "amount.h"
#include "chain.h"
#include "chainparams.h"
#include "coins.h"
#include "consensus/consensus.h"
#include "consensus/tx_verify.h"
#include "consensus/merkle.h"
#include "consensus/validation.h"
#include "hash.h"
#include "validation.h"
#include "net.h"
#include "policy/feerate.h"
#include "policy/policy.h"
#include "pow.h"
#include "primitives/transaction.h"
#include "script/standard.h"
#include "timedata.h"
#include "txmempool.h"
#include "util.h"
#include "utilmoneystr.h"
#include "validationinterface.h"
#include "base58.h"
#include "wallet/wallet.h"
#include "wallet/walletdb.h"

#include <algorithm>
#include <queue>
#include <utility>

//////////////////////////////////////////////////////////////////////////////
//
// BitcoinMiner
//

//
// Unconfirmed transactions in the memory pool often depend on other
// transactions in the memory pool. When we select transactions from the
// pool, we select by highest fee rate of a transaction combined with all
// its ancestors.

uint64_t nLastBlockTx = 0;
uint64_t nLastBlockSize = 0;
uint64_t nLastBlockWeight = 0;

int64_t UpdateTime(CBlockHeader* pblock, const Consensus::Params& consensusParams, const CBlockIndex* pindexPrev)
{
    int64_t nOldTime = pblock->nTime;
    int64_t nNewTime = std::max(pindexPrev->GetMedianTimePast()+1, GetAdjustedTime());

    if (nOldTime < nNewTime)
        pblock->nTime = nNewTime;

    // Updating time can change work required on testnet:
    if (consensusParams.fPowAllowMinDifficultyBlocks)
        pblock->nBits = GetNextWorkRequired(pindexPrev, pblock, consensusParams);

    return nNewTime - nOldTime;
}

BlockAssembler::Options::Options() {
    blockMinFeeRate = CFeeRate(DEFAULT_BLOCK_MIN_TX_FEE);
    nBlockMaxWeight = DEFAULT_BLOCK_MAX_WEIGHT;
    nBlockMaxSize = DEFAULT_BLOCK_MAX_SIZE;
}

BlockAssembler::BlockAssembler(const CChainParams& params, const Options& options) : chainparams(params)
{
    blockMinFeeRate = options.blockMinFeeRate;
    // Limit weight to between 4K and MAX_BLOCK_WEIGHT-4K for sanity:
    nBlockMaxWeight = std::max<size_t>(4000, std::min<size_t>(MAX_BLOCK_WEIGHT - 4000, options.nBlockMaxWeight));
    // Limit size to between 1K and MAX_BLOCK_SERIALIZED_SIZE-1K for sanity:
    nBlockMaxSize = std::max<size_t>(1000, std::min<size_t>(MAX_BLOCK_SERIALIZED_SIZE - 1000, options.nBlockMaxSize));
    // Whether we need to account for byte usage (in addition to weight usage)
    fNeedSizeAccounting = (nBlockMaxSize < MAX_BLOCK_SERIALIZED_SIZE - 1000);
}

static BlockAssembler::Options DefaultOptions(const CChainParams& params)
{
    // Block resource limits
    // If neither -blockmaxsize or -blockmaxweight is given, limit to DEFAULT_BLOCK_MAX_*
    // If only one is given, only restrict the specified resource.
    // If both are given, restrict both.
    BlockAssembler::Options options;
    options.nBlockMaxWeight = DEFAULT_BLOCK_MAX_WEIGHT;
    options.nBlockMaxSize = DEFAULT_BLOCK_MAX_SIZE;
    bool fWeightSet = false;
    if (IsArgSet("-blockmaxweight")) {
        options.nBlockMaxWeight = GetArg("-blockmaxweight", DEFAULT_BLOCK_MAX_WEIGHT);
        options.nBlockMaxSize = MAX_BLOCK_SERIALIZED_SIZE;
        fWeightSet = true;
    }
    if (IsArgSet("-blockmaxsize")) {
        options.nBlockMaxSize = GetArg("-blockmaxsize", DEFAULT_BLOCK_MAX_SIZE);
        if (!fWeightSet) {
            options.nBlockMaxWeight = options.nBlockMaxSize * WITNESS_SCALE_FACTOR;
        }
    }
    if (IsArgSet("-blockmintxfee")) {
        CAmount n = 0;
        ParseMoney(GetArg("-blockmintxfee", ""), n);
        options.blockMinFeeRate = CFeeRate(n);
    } else {
        options.blockMinFeeRate = CFeeRate(DEFAULT_BLOCK_MIN_TX_FEE);
    }
    return options;
}

BlockAssembler::BlockAssembler(const CChainParams& params) : BlockAssembler(params, DefaultOptions(params)) {}

void BlockAssembler::resetBlock()
{
    inBlock.clear();

    // Reserve space for coinbase tx
    nBlockSize = 1000;
    nBlockWeight = 4000;
    nBlockSigOpsCost = 400;
    fIncludeWitness = false;

    // These counters do not include coinbase tx
    nBlockTx = 0;
    nFees = 0;
}


std::unique_ptr<CBlockTemplate> BlockAssembler::CreateNewBlock(const CScript& scriptPubKeyIn, bool fMineWitnessTx)
{
    int64_t nTimeStart = GetTimeMicros();

    resetBlock();

    pblocktemplate.reset(new CBlockTemplate());

    if(!pblocktemplate.get())
        return nullptr;
    pblock = &pblocktemplate->block; // pointer for convenience

    // Add dummy coinbase tx as first transaction
    pblock->vtx.emplace_back();
    pblocktemplate->vTxFees.push_back(-1); // updated at end
    pblocktemplate->vTxSigOpsCost.push_back(-1); // updated at end

    LOCK2(cs_main, mempool.cs);
    CBlockIndex* pindexPrev = chainActive.Tip();
    nHeight = pindexPrev->nHeight + 1;

    pblock->nVersion = ComputeBlockVersion(pindexPrev, chainparams.GetConsensus());
    // -regtest only: allow overriding block.nVersion with
    // -blockversion=N to test forking scenarios
    if (chainparams.MineBlocksOnDemand())
        pblock->nVersion = GetArg("-blockversion", pblock->nVersion);

    pblock->nTime = GetAdjustedTime();
    const int64_t nMedianTimePast = pindexPrev->GetMedianTimePast();

    nLockTimeCutoff = (STANDARD_LOCKTIME_VERIFY_FLAGS & LOCKTIME_MEDIAN_TIME_PAST)
                       ? nMedianTimePast
                       : pblock->GetBlockTime();

    // Decide whether to include witness transactions
    // This is only needed in case the witness softfork activation is reverted
    // (which would require a very deep reorganization) or when
    // -promiscuousmempoolflags is used.
    // TODO: replace this with a call to main to assess validity of a mempool
    // transaction (which in most cases can be a no-op).
    fIncludeWitness = IsWitnessEnabled(pindexPrev, chainparams.GetConsensus()) && fMineWitnessTx;

    int nPackagesSelected = 0;
    int nDescendantsUpdated = 0;
    addPackageTxs(nPackagesSelected, nDescendantsUpdated);

    int64_t nTime1 = GetTimeMicros();

    nLastBlockTx = nBlockTx;
    nLastBlockSize = nBlockSize;
    nLastBlockWeight = nBlockWeight;

    // Create coinbase transaction.
    CMutableTransaction coinbaseTx;
    coinbaseTx.vin.resize(1);
    coinbaseTx.vin[0].prevout.SetNull();
    coinbaseTx.vout.resize(1);
    coinbaseTx.vout[0].scriptPubKey = scriptPubKeyIn;
    coinbaseTx.vout[0].nValue = nFees + GetBlockSubsidy(nHeight, chainparams.GetConsensus());
    coinbaseTx.vin[0].scriptSig = CScript() << nHeight << OP_0;
    pblock->vtx[0] = MakeTransactionRef(std::move(coinbaseTx));
    pblocktemplate->vchCoinbaseCommitment = GenerateCoinbaseCommitment(*pblock, pindexPrev, chainparams.GetConsensus());
    pblocktemplate->vTxFees[0] = -nFees;

    uint64_t nSerializeSize = GetSerializeSize(*pblock, SER_NETWORK, PROTOCOL_VERSION);
    LogPrintf("CreateNewBlock(): total size: %u block weight: %u txs: %u fees: %ld sigops %d\n", nSerializeSize, GetBlockWeight(*pblock), nBlockTx, nFees, nBlockSigOpsCost);

    // Fill in header
    pblock->hashPrevBlock  = pindexPrev->GetBlockHash();
    UpdateTime(pblock, chainparams.GetConsensus(), pindexPrev);
    pblock->nBits          = GetNextWorkRequired(pindexPrev, pblock, chainparams.GetConsensus());
    pblock->nNonce         = 0;
    pblocktemplate->vTxSigOpsCost[0] = WITNESS_SCALE_FACTOR * GetLegacySigOpCount(*pblock->vtx[0]);

    CValidationState state;
    if (!TestBlockValidity(state, chainparams, *pblock, pindexPrev, false, false)) {
        throw std::runtime_error(strprintf("%s: TestBlockValidity failed: %s", __func__, FormatStateMessage(state)));
    }
    int64_t nTime2 = GetTimeMicros();

    LogPrint(BCLog::BENCH, "CreateNewBlock() packages: %.2fms (%d packages, %d updated descendants), validity: %.2fms (total %.2fms)\n", 0.001 * (nTime1 - nTimeStart), nPackagesSelected, nDescendantsUpdated, 0.001 * (nTime2 - nTime1), 0.001 * (nTime2 - nTimeStart));

    return std::move(pblocktemplate);
}

void BlockAssembler::onlyUnconfirmed(CTxMemPool::setEntries& testSet)
{
    for (CTxMemPool::setEntries::iterator iit = testSet.begin(); iit != testSet.end(); ) {
        // Only test txs not already in the block
        if (inBlock.count(*iit)) {
            testSet.erase(iit++);
        }
        else {
            iit++;
        }
    }
}

bool BlockAssembler::TestPackage(uint64_t packageSize, int64_t packageSigOpsCost)
{
    // TODO: switch to weight-based accounting for packages instead of vsize-based accounting.
    if (nBlockWeight + WITNESS_SCALE_FACTOR * packageSize >= nBlockMaxWeight)
        return false;
    if (nBlockSigOpsCost + packageSigOpsCost >= MAX_BLOCK_SIGOPS_COST)
        return false;
    return true;
}

// Perform transaction-level checks before adding to block:
// - transaction finality (locktime)
// - premature witness (in case segwit transactions are added to mempool before
//   segwit activation)
// - serialized size (in case -blockmaxsize is in use)
bool BlockAssembler::TestPackageTransactions(const CTxMemPool::setEntries& package)
{
    uint64_t nPotentialBlockSize = nBlockSize; // only used with fNeedSizeAccounting
    BOOST_FOREACH (const CTxMemPool::txiter it, package) {
        if (!IsFinalTx(it->GetTx(), nHeight, nLockTimeCutoff))
            return false;
        if (!fIncludeWitness && it->GetTx().HasWitness())
            return false;
        if (fNeedSizeAccounting) {
            uint64_t nTxSize = ::GetSerializeSize(it->GetTx(), SER_NETWORK, PROTOCOL_VERSION);
            if (nPotentialBlockSize + nTxSize >= nBlockMaxSize) {
                return false;
            }
            nPotentialBlockSize += nTxSize;
        }
    }
    return true;
}

void BlockAssembler::AddToBlock(CTxMemPool::txiter iter)
{
    pblock->vtx.emplace_back(iter->GetSharedTx());
    pblocktemplate->vTxFees.push_back(iter->GetFee());
    pblocktemplate->vTxSigOpsCost.push_back(iter->GetSigOpCost());
    if (fNeedSizeAccounting) {
        nBlockSize += ::GetSerializeSize(iter->GetTx(), SER_NETWORK, PROTOCOL_VERSION);
    }
    nBlockWeight += iter->GetTxWeight();
    ++nBlockTx;
    nBlockSigOpsCost += iter->GetSigOpCost();
    nFees += iter->GetFee();
    inBlock.insert(iter);

    bool fPrintPriority = GetBoolArg("-printpriority", DEFAULT_PRINTPRIORITY);
    if (fPrintPriority) {
        LogPrintf("fee %s txid %s\n",
                  CFeeRate(iter->GetModifiedFee(), iter->GetTxSize()).ToString(),
                  iter->GetTx().GetHash().ToString());
    }
}

int BlockAssembler::UpdatePackagesForAdded(const CTxMemPool::setEntries& alreadyAdded,
        indexed_modified_transaction_set &mapModifiedTx)
{
    int nDescendantsUpdated = 0;
    BOOST_FOREACH(const CTxMemPool::txiter it, alreadyAdded) {
        CTxMemPool::setEntries descendants;
        mempool.CalculateDescendants(it, descendants);
        // Insert all descendants (not yet in block) into the modified set
        BOOST_FOREACH(CTxMemPool::txiter desc, descendants) {
            if (alreadyAdded.count(desc))
                continue;
            ++nDescendantsUpdated;
            modtxiter mit = mapModifiedTx.find(desc);
            if (mit == mapModifiedTx.end()) {
                CTxMemPoolModifiedEntry modEntry(desc);
                modEntry.nSizeWithAncestors -= it->GetTxSize();
                modEntry.nModFeesWithAncestors -= it->GetModifiedFee();
                modEntry.nSigOpCostWithAncestors -= it->GetSigOpCost();
                mapModifiedTx.insert(modEntry);
            } else {
                mapModifiedTx.modify(mit, update_for_parent_inclusion(it));
            }
        }
    }
    return nDescendantsUpdated;
}

// Skip entries in mapTx that are already in a block or are present
// in mapModifiedTx (which implies that the mapTx ancestor state is
// stale due to ancestor inclusion in the block)
// Also skip transactions that we've already failed to add. This can happen if
// we consider a transaction in mapModifiedTx and it fails: we can then
// potentially consider it again while walking mapTx.  It's currently
// guaranteed to fail again, but as a belt-and-suspenders check we put it in
// failedTx and avoid re-evaluation, since the re-evaluation would be using
// cached size/sigops/fee values that are not actually correct.
bool BlockAssembler::SkipMapTxEntry(CTxMemPool::txiter it, indexed_modified_transaction_set &mapModifiedTx, CTxMemPool::setEntries &failedTx)
{
    assert (it != mempool.mapTx.end());
    return mapModifiedTx.count(it) || inBlock.count(it) || failedTx.count(it);
}

void BlockAssembler::SortForBlock(const CTxMemPool::setEntries& package, CTxMemPool::txiter entry, std::vector<CTxMemPool::txiter>& sortedEntries)
{
    // Sort package by ancestor count
    // If a transaction A depends on transaction B, then A's ancestor count
    // must be greater than B's.  So this is sufficient to validly order the
    // transactions for block inclusion.
    sortedEntries.clear();
    sortedEntries.insert(sortedEntries.begin(), package.begin(), package.end());
    std::sort(sortedEntries.begin(), sortedEntries.end(), CompareTxIterByAncestorCount());
}

// This transaction selection algorithm orders the mempool based
// on feerate of a transaction including all unconfirmed ancestors.
// Since we don't remove transactions from the mempool as we select them
// for block inclusion, we need an alternate method of updating the feerate
// of a transaction with its not-yet-selected ancestors as we go.
// This is accomplished by walking the in-mempool descendants of selected
// transactions and storing a temporary modified state in mapModifiedTxs.
// Each time through the loop, we compare the best transaction in
// mapModifiedTxs with the next transaction in the mempool to decide what
// transaction package to work on next.
void BlockAssembler::addPackageTxs(int &nPackagesSelected, int &nDescendantsUpdated)
{
    // mapModifiedTx will store sorted packages after they are modified
    // because some of their txs are already in the block
    indexed_modified_transaction_set mapModifiedTx;
    // Keep track of entries that failed inclusion, to avoid duplicate work
    CTxMemPool::setEntries failedTx;

    // Start by adding all descendants of previously added txs to mapModifiedTx
    // and modifying them for their already included ancestors
    UpdatePackagesForAdded(inBlock, mapModifiedTx);

    CTxMemPool::indexed_transaction_set::index<ancestor_score>::type::iterator mi = mempool.mapTx.get<ancestor_score>().begin();
    CTxMemPool::txiter iter;

    // Limit the number of attempts to add transactions to the block when it is
    // close to full; this is just a simple heuristic to finish quickly if the
    // mempool has a lot of entries.
    const int64_t MAX_CONSECUTIVE_FAILURES = 1000;
    int64_t nConsecutiveFailed = 0;

    while (mi != mempool.mapTx.get<ancestor_score>().end() || !mapModifiedTx.empty())
    {
        // First try to find a new transaction in mapTx to evaluate.
        if (mi != mempool.mapTx.get<ancestor_score>().end() &&
                SkipMapTxEntry(mempool.mapTx.project<0>(mi), mapModifiedTx, failedTx)) {
            ++mi;
            continue;
        }

        // Now that mi is not stale, determine which transaction to evaluate:
        // the next entry from mapTx, or the best from mapModifiedTx?
        bool fUsingModified = false;

        modtxscoreiter modit = mapModifiedTx.get<ancestor_score>().begin();
        if (mi == mempool.mapTx.get<ancestor_score>().end()) {
            // We're out of entries in mapTx; use the entry from mapModifiedTx
            iter = modit->iter;
            fUsingModified = true;
        } else {
            // Try to compare the mapTx entry to the mapModifiedTx entry
            iter = mempool.mapTx.project<0>(mi);
            if (modit != mapModifiedTx.get<ancestor_score>().end() &&
                    CompareModifiedEntry()(*modit, CTxMemPoolModifiedEntry(iter))) {
                // The best entry in mapModifiedTx has higher score
                // than the one from mapTx.
                // Switch which transaction (package) to consider
                iter = modit->iter;
                fUsingModified = true;
            } else {
                // Either no entry in mapModifiedTx, or it's worse than mapTx.
                // Increment mi for the next loop iteration.
                ++mi;
            }
        }

        // We skip mapTx entries that are inBlock, and mapModifiedTx shouldn't
        // contain anything that is inBlock.
        assert(!inBlock.count(iter));

        uint64_t packageSize = iter->GetSizeWithAncestors();
        CAmount packageFees = iter->GetModFeesWithAncestors();
        int64_t packageSigOpsCost = iter->GetSigOpCostWithAncestors();
        if (fUsingModified) {
            packageSize = modit->nSizeWithAncestors;
            packageFees = modit->nModFeesWithAncestors;
            packageSigOpsCost = modit->nSigOpCostWithAncestors;
        }

        if (packageFees < blockMinFeeRate.GetFee(packageSize)) {
            // Everything else we might consider has a lower fee rate
            return;
        }

        if (!TestPackage(packageSize, packageSigOpsCost)) {
            if (fUsingModified) {
                // Since we always look at the best entry in mapModifiedTx,
                // we must erase failed entries so that we can consider the
                // next best entry on the next loop iteration
                mapModifiedTx.get<ancestor_score>().erase(modit);
                failedTx.insert(iter);
            }

            ++nConsecutiveFailed;

            if (nConsecutiveFailed > MAX_CONSECUTIVE_FAILURES && nBlockWeight >
                    nBlockMaxWeight - 4000) {
                // Give up if we're close to full and haven't succeeded in a while
                break;
            }
            continue;
        }

        CTxMemPool::setEntries ancestors;
        uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
        std::string dummy;
        mempool.CalculateMemPoolAncestors(*iter, ancestors, nNoLimit, nNoLimit, nNoLimit, nNoLimit, dummy, false);

        onlyUnconfirmed(ancestors);
        ancestors.insert(iter);

        // Test if all tx's are Final
        if (!TestPackageTransactions(ancestors)) {
            if (fUsingModified) {
                mapModifiedTx.get<ancestor_score>().erase(modit);
                failedTx.insert(iter);
            }
            continue;
        }

        // This transaction will make it in; reset the failed counter.
        nConsecutiveFailed = 0;

        // Package can be added. Sort the entries in a valid order.
        std::vector<CTxMemPool::txiter> sortedEntries;
        SortForBlock(ancestors, iter, sortedEntries);

        for (size_t i=0; i<sortedEntries.size(); ++i) {
            AddToBlock(sortedEntries[i]);
            // Erase from the modified set, if present
            mapModifiedTx.erase(sortedEntries[i]);
        }

        ++nPackagesSelected;

        // Update transactions that depend on each of these
        nDescendantsUpdated += UpdatePackagesForAdded(ancestors, mapModifiedTx);
    }
}

void IncrementExtraNonce(CBlock* pblock, const CBlockIndex* pindexPrev, unsigned int& nExtraNonce)
{
    // Update nExtraNonce
    static uint256 hashPrevBlock;
    if (hashPrevBlock != pblock->hashPrevBlock)
    {
        nExtraNonce = 0;
        hashPrevBlock = pblock->hashPrevBlock;
    }
    ++nExtraNonce;
    unsigned int nHeight = pindexPrev->nHeight+1; // Height first in coinbase required for block.version=2
    CMutableTransaction txCoinbase(*pblock->vtx[0]);
    txCoinbase.vin[0].scriptSig = (CScript() << nHeight << CScriptNum(nExtraNonce)) + COINBASE_FLAGS;
    assert(txCoinbase.vin[0].scriptSig.size() <= 100);

    pblock->vtx[0] = MakeTransactionRef(std::move(txCoinbase));
    pblock->hashMerkleRoot = BlockMerkleRoot(*pblock);
}


#define RowLimit  500032            //  This will allow searches for "odd X" up
                                    //  to (2 * RowLimit)^2 = 1 Trillion.
                                    //  (= 1.0E+12 ).

#define XoddPerBlock  50000         //  Can change this to alter memory used.
#define BlockSize 100000.0          //  If "XoddPerBlock" is changed, also
                                    //  change "BlockSize" to 2 times the above,
                                    //  but floating point. Note: If BlockSize
                                    //  is > 300,000, then "LastRow" calc in
                                    //  InitSys() will have to be changed.

void InitSys(CBlockHeader &block);                 //  they do are included in the functions.
void MakeDivs(void);
void MakeTriangles(void);
void AddEdge(double, double, double);
unsigned SearchEdges(CBlockHeader &block);
                                    //  All arrays are global. These 4 arrays
                                    //  are used by the sieve algorithm to
                                    //  generate the divisors for each odd X.
unsigned FirstCol[RowLimit];        //  Each member = the 1st col used in a row
unsigned ColHeads[XoddPerBlock];    //  Link list heads for "Xodd" divisors
unsigned Down[332000];              //  Ptrs to next node down for an Xodd list
double Divisor[332000];             //  Divisor for a node (D1,D2,etc.)
                                    //  For each trial "odd edge", the divisors
                                    //  are copied from the above to here.
double DivsList[2000] = {1.0};      //  List of divisors for an "Xodd".
                                    //  DivsList[0] must always be 1.0.
int MaxDivNodes;                    //  Used for range checking.

    //  Each of the 2nd sides for all possible right triangles is a candidate
    //  for the other two dimensions of the brick and the diagonal on the
    //  even surface of the brick. Information about them is stored in the
    //  following arrays.

    //  If the sum of the squares of any two edges (array members) is equal to
    //  the square of some other member, then the brick problem is solved. For
    //  all possible sums, a hashing system is used to speed up the search for
    //  this 3rd member.

double YforTrials[100000];          //  Candidates for edges.
long long unsigned YsqrLow[100000]; //  64 low bits of the above squared. Does
                                    //  not include the 4 trailing "0" bits.
unsigned HashLink[100000];          //  L.Lists for the above that share the same hash
unsigned HashHead[16384];           //  Start of above linked lists. Hash index is bits
                                    //  18 to 31 of YsqrLow.

char Databuff[80];                  //  Buffer for user input.

                                    //  Other global variables
double Xbase;                       //  Increments at "BlockSize" per iteration up to
                                    //  (2*RowLimit)^2
double Xodd;                        //  Odd side for brick - Try 1,3,5,7, etc.
double MaxD1;                       //  Upper limit for 1st divisor ( < cbrt(Xodd) )
unsigned NbrOfDiv;                  //  Nbr. of divisors for current "Xodd"
int MaxRow;                         //  Index of last member in FirstCol[] that
                                    //  will be used for current odd X.
int LastRow;                        //  Used to find MaxRow
int Div16, NotDiv16;                //  Ptrs. into "Y" candidate list ( YforTrials[] )
                                    //  Div16 indexes "Y" edges divisible by 16
                                    //  and works down from 24999.
                                    //  NotDiv16 indexes "Y" edges that are not divs.
                                    //  by 16 and works up from 25000.
int MaxNbrDiv = 1;                  //  Largest nbr. of divisors so far.
int MinDiv16 = 25000;               //  Lowest and highest indexes so far
int MaxNot16 = 24999;               //  in the "Y" candidate lists.
double XbaseStart;                  //  User can choose where to start the search
double XbaseEnd;                    //  Will stop at XbaseStart + 8,001,000,000
int ExtCount = 0;                   //  Count external solutions






//*****************************************************************************
//
//                                InitSys
//
//  This routine asks the user for the "Xodd" starting base and then
//  initializes the FirstCol[] array. For each row, (The actual trial divisor
//  is 2 * row + 1) FirstCol[] tells where to place the first node in the
//  sparse array for divisors of a number.
//
//*****************************************************************************

void InitSys(uint64_t t) {

  int i;
  double UpperLimit;
  double Idbl, gap;
  double InitCol;
  double Cols2skip, LastCol;


  UpperLimit = 4.0 * RowLimit * RowLimit;

  // puts("Computer program by Bill Butler\n");
  // puts("You may start the search for integer bricks from any Xodd base");
  // printf("up to %'.0f. The number you enter will be rounded down to the\n",
            // UpperLimit);
  // printf("first %'.0f below your entry.).\n", BlockSize);
  // puts("The program will end at 8.001 billion above your start point.");

  // puts("\nEnter a number for \"Xbase start\".");
  // gets(Databuff);
  // XbaseStart = atof(Databuff);
  XbaseStart = t;
  XbaseStart -= fmod(XbaseStart, BlockSize);
  XbaseEnd = XbaseStart + 8.001e+9;

  Xodd = XbaseStart - 1.0;              //  Initialize the odd side of the brick.
                                        //  Will count up by 2s from here.
  if (XbaseStart < 1.5e7)               //  LastRow is used to find the max row
    LastRow = 2000;                     //  ("MaxRow") that will be processed in
  else                                  //  the current Xbase iteration. If Xbase
    LastRow = sqrt(XbaseStart/4.0) + 20.0;
                                        //  is < 15 million, "MaxRow" will increase
                                        //  faster than the 20 increment in
                                        //  MakeDivisors(). Thus give it a
                                        //  headstart for low Xbase numbers.

  Cols2skip = XbaseStart/2.0;           //  Will Start to the right of this many
                                        //  cols
  LastCol = Cols2skip - 1.0;            //  Will use this if to right of other hits

    //  Calculations for the sieve algorithm.
    //  The content of FirstCol[] will be the calculated position for the following:
    //  Given: Candidates for "odd side" of brick = XbaseStart + 2*col + 1
    //  Given: A list of possible divisors = 2 * (index for FirstCol[]) + 3
    //  If the divisor is >= the sqrt of "odd side", then the
    //  first hit will be at the col for divisor^2. This will be at
    //  InitCol - Cols2skip (but use a limit to prevent numeric overflow)
    //  Else find the first number greater than "odd side" that generates an odd
    //  integer result when divided by the "divisor". The "Floor"
    //  calculation finds where this number will hit.

  for (i = 0; i < RowLimit; i++) {              //  Set up 1st col for all divisors
    Idbl = i;                                   //  Get floating point for calc.
    InitCol = 2.0*Idbl*Idbl + 6.0*Idbl + 4.0;   //  used for all divisors
    if (InitCol > Cols2skip)                    //  Limit is used to prevent unsigned
      FirstCol[i] = fmin((InitCol - Cols2skip), 4294967000.0);  //  int overflow
    else {
      gap = 2.0 * Idbl + 3.0;
      FirstCol[i] = gap * floor((LastCol + gap - InitCol)/gap) + InitCol - Cols2skip;
    }                                           //  The above calcs check OK as shown in
  }                                             //  "IntBrickFirstCol" Excel spreadsheet
                                                //  Calculate the upper limit
                                                //  for the first divisor
  MaxD1 = floor(cbrt(XbaseStart));              //  Get cube root for initial MaxD1
  if (fmod(MaxD1, 2.0) == 0.0)                  //  Make it an odd number.
    MaxD1 -= 1.0;
}




//*****************************************************************************
//
//                                Make Divisors
//
//  This routine generates all the divisors for the "XoddPerBlock" odd numbers
//  in the current block starting at the current "Xbase". The FirstCol[] array
//  contains a number giving the first col (corresponds to an odd X) that is
//  evenly divisible by the divisor for the row (Divisor equals 2*row + 3). The
//  next number that is evenly divisible is "gap" cols to the right where "gap"
//  is equal to the divisor. At each location, a node is created to save the
//  divisor. For each of the XoddPerBlock trial odd numbers in the current
//  block, a link list of trial divisors will be generated.
//
//*****************************************************************************

void MakeDivs(void) {
  int i, NodeIndx;
  unsigned col, gap;

  for (i = XoddPerBlock - 1; i >= 0; i--)
    ColHeads[i] = 0;                        //  Initialize col heads
                                            //  Skip rows that won't be used.
  for (i = LastRow; FirstCol[i] > XoddPerBlock; i--);

  MaxRow = i;
  if ((LastRow - i) < 20)                   //  Update starting point
    LastRow = i + 20;

  NodeIndx = 0;                             //  Counts nodes in sparse matrix.
  for (i = MaxRow; i >= 0; i--) {           //  Start with last row
    gap = i;                                //  Gap is equal to divisor for the
    gap <<= 1;                              //  row.
    gap += 3;
                                            //  Each node is a divisor for the
                                            //  particular column (= an odd X)
    for (col = FirstCol[i]; col < XoddPerBlock; col += gap) {
      NodeIndx++;                           //  Increment number of nodes
      Divisor[NodeIndx] = gap;              //  Will convert to double;
      Down[NodeIndx] = ColHeads[col];       //  Add to link list
      ColHeads[col] = NodeIndx;
    }                                       //  End of nodes for this row
    FirstCol[i] = col;                      //  Save col for next Xbase
  }                                         //  End of rows for this Xbase
  if (NodeIndx > MaxDivNodes)               //  Note: The value of MaxDivNodes
    MaxDivNodes = NodeIndx;                 //  is output in the status report.
}                                           //  End of make divisors routine




//*****************************************************************************
//
//                                Make Triangles
//
//  Given a list of divisors of X (List is in DivsList[]), this routine finds
//  divisor triplets (D1 * D2 * D3 = odd X), and then passes valid permutations
//  of each combination to routine AddEdge() where they are posted to the
//  search arrays. Any permutation such that the second number "D2" is larger
//  than the first "D1" will generate a valid right triangle.
//
//*****************************************************************************

void MakeTriangles(void) {

  double D1, D2, D3, remainder;
  int i, j;
                                        //  Loop control also gets 1st divs.
  for (i = 0; (D1 = DivsList[i]) <= MaxD1; i++) {
    remainder = Xodd/D1;                //  D2 * D3 must equal this
                                        //  Get divisors 2 and 3. Process
                                        //  loop for all divisors "D2" that
    j = i;                              //  are <= the sqrt(remainder)
    D3 = remainder/(D2=DivsList[j]);
    while (D2 <= D3) {
      if (D3 == floor(D3)) {            //  If division was exact,
        AddEdge(D1,D3,D2);              //  then add 1st combination
        if ( (D2>D1) && (D3>D2) ) {     //  to list. Also
          AddEdge(D1,D2,D3);            //  add others if
          AddEdge(D2,D3,D1);            //  permutations are OK.
        }
      }
      D3 = remainder/(D2 = DivsList[++j]);
    }                                   //  End while
  }                                     //  End "for i"
}                                       //  End MakeTriangles




//*****************************************************************************
//
//                                    Add Edge
//
//  The 3 numbers passed to this routine are known to be valid divisors for the
//  odd side of the brick. ( D1 * D2 * D3 = Xodd) The routine breaks them down
//  into components "p", "q", and "k"
//  (p - q) * (p + q) * k = Xodd
//  which are used to compute the "Y" side of a right triangle; which is thus a
//  candidate for an even edge of an integer brick.
//  2 * p * q * k = "Y" edge.
//  Each of of these edge candidates is added to a list for later processing.
//
//  Data in each node in the lists consists of trial edge "Y" which is stored
//  as a "double" variable, and the 64 low bits of Y^2. Note: The 4 lowest bits
//  of a pure Y^2 would be zeros, but they are shifted out to preserve as much
//  precision as possible. Within the 64 bits of YlowSqr, bits 18 to 31 will
//  be used as a hash index to facilitate later searches.
//
//  Also note: The trial edge "Y" may have more digits than the 15+ decimal
//  digit precision in a "double" variable. The full precision is not needed to
//  verify a solution. If a solution is found and the exact value of "Y" is too
//  big for precision in a "double" variable, it would be relatively easy to
//  modify the code to provide this higher precision.
//
//  Finally, the Y's are split into those that are evenly divisible by 16 and
//  those that are not. (Most will wind up in the 2nd group). To form a brick
//  with integer dimensions, at least one side must come from the divide by 16
//  group. Since no combination is possible if both sides are in the not div.
//  by 16 group, this splitting will speed up later searching.
//
//*****************************************************************************

void AddEdge(double D1,double D2, double D3) {
                                  //  Note: "D2" will be > "D1", and all three
                                  //  parameters will be odd integers < 1.0E12
  long long unsigned YlowSqr;
  unsigned YsqrHash;              //  Bits 18 to 31 of YlowSqr
  unsigned link, Yindex, Div16Test;
  double p, q;
  double Yedge;

  long long unsigned Puns, Quns, Kuns;    //  Used to construct YlowSqr

                                      //  In terms of magnitude, "p", "q", and "k"
                                      //  will be < 1.0E12 as long as Xodd < 1.0E12
                                      //  Solve: P - Q = D1, P + Q = D2 for P and Q
  p = (D1 + D2) / 2.0;                //  Add the above equations, and divide by 2.
  q = p - D1;                         //  Note that either p or q will be even

  Yedge = 2.0 * p * q * D3;           //  Note: Good for about 15 decimal digits.
                                      //  If higher precision is ever needed, put the
                                      //  calcs here. (Might be able to get by with
                                      //  "long double" instead "double" for Yedge.)
                                      //  Next, get 64 low bits of the above.
  Puns = p;                           //  Convert p, q, and k to 64 bit integers
  Quns = q;
  if (Puns & 1)                       //  Get rid of the trailing "0" bit that will
    Quns >>= 1;                       //  exist in either "P" or "Q"
  else
    Puns >>= 1;
  Kuns = D3;                          //  YlowSqr is just used for the look-up system
  YlowSqr = Puns * Quns * Kuns;       //  Thus don't need to multiply by 2. Any
                                      //  overflow in YlowSqr can be ignored as we
                                      //  only need the lowest 64 bits.
  YlowSqr *= YlowSqr;                 //  Square it.
  YsqrHash = YlowSqr;                 //  Gets lowest 32 bits.
  Div16Test = YsqrHash;               //  Will use to see if Yedge is divisible by 16
  YsqrHash >>= 18;                    //  Just use bits 18 to 31 for the hash index.

                                      //  Use hash and link list to see if
                                      //  "Y" is already in the table
  for (link = HashHead[YsqrHash]; link; link = HashLink[link]) {
    if (YlowSqr != YsqrLow[link])     //  Most non matches will
      continue;                       //  occur here.
    if (YforTrials[link] == Yedge)    //  Rarely needed.
      break;
  }
            //  Note: If "Yedge" is evenly divisible by 16, then it has at
            //  least 4 trailing binary zeroes. If Y/16 is an integer, then the
            //  expression
            //  "YlowSqr = Puns * Quns * Kuns;"    (before squaring)
            //  will have at least 2 trailing zeroes. (2 were shifted/omited)
            //  If Y/16 is even, then after squaring YlowSqr will have at
            //  least 4 trailing zeroes. If we "AND" this with "15"
            //  (Binary 1111), then the result will be true if and only if 16
            //  does not divide Y evenly.

  if (!link) {                        //  If not found then add new edge to list
    if (Div16Test & 15) Yindex = ++NotDiv16;    //  Loc. in Ylist is determined
    else Yindex = --Div16;            //  by divisibility by 16.

    YforTrials[Yindex] = Yedge;       //  Add y to candidate list
    YsqrLow[Yindex] = YlowSqr;        //  Ditto for 64 low bits of Y^2.
    HashLink[Yindex] = HashHead[YsqrHash];
    HashHead[YsqrHash] = Yindex;      //  Insert in link list
  }                                   //  End if not found
}                                     //  End AddEdge




//*****************************************************************************
//
//                               Search Edges
//
//  This routine tries all valid combinations in the trial Y edges list to see
//  if the sum of the squares of any two members matches any 3rd value in the
//  list. If a match is found, then the integer brick problem has been solved.
//
//  There may be many thousands of members in this list. All efforts have been
//  used to speed up this search. The hash look-up system avoids the inner loop
//  of what would otherwise look like:
//
//  For each member of the group
//    For each member of the group
//      Add the squares of these two numbers together
//      For each member of the group
//        See if the square of this third member matches the above sum
//          (If yes then output solution)
//      Repeat third loop
//    Repeat second loop
//  Repeat first loop
//
//*****************************************************************************

unsigned SearchEdges(CBlockHeader &block) {

  unsigned i, j;
  unsigned link, hash;
  long long unsigned y1LowBits, SumLowBits;
  double hypotenuse;                        //  Used for external solutions where
                                            //  Xodd is less than 5000
  unsigned found = 0;

  for (i = Div16; i < 25000; i++) {         //  A brick requires at least 1 member
    y1LowBits = YsqrLow[i];                 //  from this group.
    for (j = i + 1; j <= NotDiv16; j++) {
            //  If in early stages of the program, then output external
            //  solutions. The 5,000 can be arbitrarily increased, but will
            //  rapidly run into precision problems. Note that precision
            //  calculations are only applied to potential complete solutions
            //  that include the internal diagonal.
      if (Xodd < 500000000.0) {                  //  Compute hypotenuse of the two "Y"
        hypotenuse = hypot(YforTrials[i], YforTrials[j]);        //  sides.
        if (hypotenuse == round(hypotenuse)) {    //  Calcs involve the "even"
			ExtCount++;                             //  face of the brick.
			uint64_t a = (uint64_t)round(Xodd);
			uint64_t b = (uint64_t)round(YforTrials[i]);
			uint64_t c = (uint64_t)round(YforTrials[j]);
            if (a > b) {
                uint64_t t = a;
                a = b;
                b = t;
            }
            if (b > c) {
                uint64_t t = b;
                b = c;
                c = t;
            }
            if (a > b) {
                uint64_t t = a;
                a = b;
                b = t;
            }
			uint64_t d = (uint64_t)round(sqrt(a * a + b * b));
			uint64_t e = (uint64_t)round(sqrt(b * b + c * c));
			uint64_t f = (uint64_t)round(sqrt(c * c + a * a));
			uint64_t g = (uint64_t)round(sqrt(a * a + b * b + c * c));

			block.nA.n = a;
			block.nB.n = b;
			block.nC.n = c;
			block.nD.n = d;
			block.nE.n = e;
			block.nF.n = f;
			block.nG.n = g;
			if (a * a + b * b == d * d && b * b + c * c == e * e && c * c + a * a == f * f) {
			  LogPrintf("External sol. Nbr. %d at  X = %'.0f   Y = %'.0f   Z = %'.0f\n",
					ExtCount, Xodd, YforTrials[i], YforTrials[j]);
				if (CheckProofOfWork(block) > 0 && !chainActive.ContainsABC(block)) {
					found = 1;
					break;
				}
			}
        }
      }                                    //  End of "If in early stages"

                //  If the sum of any two trial Yedge^2 entrees is equal to
                //  some other entry in the table, then a solution to the
                //  integer brick problem may have been found. Get this sum
                //  and then search the list to see if there is a match.

      SumLowBits = YsqrLow[j] + y1LowBits;
      link = SumLowBits;                  //  Construct hashlink head for this
      link >>= 18;                        //  sum
      for (link = HashHead[link]; link; link = HashLink[link]) {
        if (SumLowBits != YsqrLow[link])
          continue;                       //  No solution.

        //  The following code is only used if a 64 bit match has been found.
        //  If the sum of the squares of any two sides is approximately the
        //  same as the square of some 3rd value, then a solution may have been
        //  found. If very high precision were available, then an exact match
        //  would be used. The "1.0E-12" limit might allow a "false positive"
        //  to be reported, but the relatively wide limit is used to prevent
        //  precision errors from skipping over a real solution.

        if (fabs(hypot(YforTrials[i], YforTrials[j])/YforTrials[link] - 1.0)
                    < 1.0E-12) {
			ExtCount++;                             //  face of the brick.
			uint64_t a = (uint64_t)round(Xodd);
			uint64_t b = (uint64_t)round(YforTrials[i]);
			uint64_t c = (uint64_t)round(YforTrials[j]);
            if (a > b) {
                uint64_t t = a;
                a = b;
                b = t;
            }
            if (b > c) {
                uint64_t t = b;
                b = c;
                c = t;
            }
            if (a > b) {
                uint64_t t = a;
                a = b;
                b = t;
            }
			uint64_t d = (uint64_t)round(sqrt(a * a + b * b));
			uint64_t e = (uint64_t)round(sqrt(b * b + c * c));
			uint64_t f = (uint64_t)round(sqrt(c * c + a * a));
			uint64_t g = (uint64_t)round(sqrt(a * a + b * b + c * c));

			block.nA.n = a;
			block.nB.n = b;
			block.nC.n = c;
			block.nD.n = d;
			block.nE.n = e;
			block.nF.n = f;
			block.nG.n = g;
			if (a * a + b * b == d * d && b * b + c * c == e * e && c * c + a * a == f * f) {
			  LogPrintf("External sol. Nbr. %d at  X = %'.0f   Y = %'.0f   Z = %'.0f\n",
					ExtCount, Xodd, YforTrials[i], YforTrials[j]);
				if (CheckProofOfWork(block) > 0 && !chainActive.ContainsABC(block)) {
					found = 1;
					break;
				}
			}
        }                                        //  End if low matches
      }                                          //  End for link
      if (found > 0)
          break;
    }                                            //  End for j
    if (found > 0)
        break;
  }                                              //  End for i

                                                 //  Reset HashHead array back to zeros.
  for (i = Div16; i <= NotDiv16; i++) {
    hash = YsqrLow[i];
    hash >>= 18;
    HashHead[hash] = 0;
  }
  
  return found;
}                                                //  End SearchEdges



unsigned searchEulerBrick(CBlockHeader &block) {                    //  Find bricks with integer sides and diagonals

  int i, j, col;                    //  Misc. loop controls
  double ResetD1atX;                //  Always == (MaxD1+2)^2 * (MaxD1+4)
  unsigned found = 0;

  ResetD1atX = (MaxD1 + 2.0)*(MaxD1 + 2.0)*(MaxD1 + 4.0);

                                    //    Start main loop
  for (Xbase = XbaseStart; Xbase < XbaseEnd; Xbase += BlockSize) {
    if (fmod(Xbase, 1000000.0) == 0.0) {                    //    Status report
      printf("\nWorking on Xbase = %'.0f\n", Xbase);
      printf("LastRow is up to %'d (Must stay < %'d)\n", LastRow, RowLimit);
      printf("MaxNbrDiv = %d (Must stay < 2,000)\n", MaxNbrDiv);
      printf("MaxDivNodes = %'d   (Must stay under 332,000)\n",    MaxDivNodes);
      printf("MinDiv16 = %'d (Must stay > 0)\n", MinDiv16);
      printf("MaxNot16 = %'d (Must stay < 100,000)\n", MaxNot16);
    }

    for (col = 0; col < XoddPerBlock; col++) {
      Xodd += 2.0;                             //  Next trial odd edge = 1,3,5,etc.
                                               //  Xodd = Xbase + 2.0 * col + 1.0
      if (Xodd >= ResetD1atX) {                //  Test to see if limit for
        MaxD1 += 2.0;                          //  1st divisor needs update.
        ResetD1atX = (MaxD1 + 2.0)*(MaxD1 + 2.0)*(MaxD1 + 4.0);
      }

      j = 1;                                   //  Count divisors for current odd X
                                               //  Get list of divisors of X
      for (i = ColHeads[col]; i; i = Down[i])
        DivsList[j++] = Divisor[i];            //  Note: DivsList[0] always = 1.0

      if (j < 2)                               //  Need at least 2 for sol.
        continue;

      if (j > MaxNbrDiv)                       //  Range checking
        MaxNbrDiv = j;

      DivsList[j] = Xodd;                      //  End of Divisors.
      NbrOfDiv = j;                            //  Save global var.

      Div16 = 25000;                           //  Indexes Y's divisible by 16
      NotDiv16 = 24999;                        //  Indexes Y's not divisible by 16
                                               //  Used to speed up search process
                                               //  Use the list of divisors of "X" to
      MakeTriangles();                         //  generate all possible right
                                               //  triangles.

      if (Div16 < MinDiv16)                    //  Range checking
        printf("At Xodd = %'.0f  MinDiv16 = %'d (Must stay > 0)\n",
            Xodd, MinDiv16 = Div16);
      if (NotDiv16 > MaxNot16)
        printf("At Xodd = %'.0f  MaxNot16 = %'d (Must stay < 100,000)\n",
            Xodd, MaxNot16 = NotDiv16);

                                               //  Then search these combinations
      found = SearchEdges(block);                           //  to see if a solution exists.
      if (found > 0)
          break;
    }                                          //  End of cols. (odd Xs)
    for (i = RowLimit - 1; i >= 0; i--)        //  Update 1st col ptrs for
      FirstCol[i] -= XoddPerBlock;             //  next block of X's.
    if (found > 0)
        break;
  }                                            //  Repeat for next Xbase

  printf("\nProgram ended normally at XbaseEnd = %'.0f\n", XbaseEnd);
  return found;
}                                              //  End program
