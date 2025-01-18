import BranchParams::*;
import BrPred::*;
import Vector::*;
import Types::*;
import ProcTypes::*;
import EpochManager::*;

typedef struct {
    Bool taken;
    trainInfoT train;
    // For debug
    Addr pc;
} StagedDirPredResult#(type trainInfoT) deriving(Bits, Eq, FShow);

typedef struct {
    StagedDirPredResult#(trainInfoT) result;
    Epoch main_epoch;
    Bool decode_epoch;
} GuardedResult#(type trainInfoT) deriving(Bits, Eq, FShow);


interface StagedDirPredictor#(type trainInfoT);
    method Action nextPc(Addr nextPc, Epoch main_epoch, Bool decode_epoch); // By Fetch1 stage
    method ActionValue#(Vector#(SupSize, GuardedResult#(trainInfoT))) pred;// Taken by Fetch2 stage
    method Action confirmPred(Bit#(SupSize) results, SupCnt count); // By decode stage, for speculative history and end_pointer update
    method Action update(Bool taken, trainInfoT train, Bool mispred);

    method Action flushFront;
    method Action flush;
    method Bool flush_done;
endinterface
