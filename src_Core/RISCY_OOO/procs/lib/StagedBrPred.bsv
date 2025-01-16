import BranchParams::*;
import BrPred::*;
import Vector::*;
import Types::*;
import ProcTypes::*;

typedef struct {
    Bool taken;
    trainInfoT train;
} StagedDirPredResult#(type trainInfoT) deriving(Bits, Eq, FShow);


interface StagedDirPredictor#(type trainInfoT);
    method Action nextPc(Addr nextPc); // By Fetch1 stage
    method ActionValue#(Vector#(SupSize, StagedDirPredResult#(trainInfoT))) pred;// Taken by Fetch2 stage
    method Action confirmPred(Bit#(SupSize) results, SupCnt count); // By decode stage, for speculative history and end_pointer update
    method Action update(Bool taken, trainInfoT train, Bool mispred);
    method Action flush;
    method Bool flush_done;
endinterface
