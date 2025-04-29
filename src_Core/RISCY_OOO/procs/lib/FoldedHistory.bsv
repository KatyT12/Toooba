import GlobalBranchHistory::*;
import BranchParams::*;
import BrPred::*;
import ProcTypes::*;
import Types::*;

import Vector::*;
import ConfigReg::*; // Need to use this because of run rule reading the history
import Ehr::*;

import Assert::*;
// Assuming out of order updates, would actually be simpler with in order updates as I could keep a pointer
/*
Alternatively - why not simply recompute the global brnach history which will be easier since we will just shift and load
back in old values, then we can do a full recomputation of the folded history, however it may increase the cycle time

Also need to think about folding historu size, what if less than th

Periodically shift for recovery?

Multiple recovery updates to history? hopefully not possible but may need EHRs
*/
interface HistorySameWindow#(numeric type length);
    method Bit#(length) history;
endinterface

interface FoldedRecoverMechanism#(numeric type length);
    method Action undo(Bit#(1) taken, Bit#(GlobalHistoryLength) global_hist);
    `ifdef DEBUG
    method ActionValue#(Bit#(length)) debugUndo;
    `endif
endinterface

interface FoldedHistory#(numeric type length);
    method Bit#(length) history;
    method Action updateHistory(Bit#(SupSize) taken, SupCnt count);

    interface Vector#(MaxSpecSize, FoldedRecoverMechanism#(length)) recoverFrom;
    interface Vector#(SupSize, HistorySameWindow#(length)) sameWindowHistory;
        
    `ifdef DEBUG
    method Action debugInitialise(Bit#(length) newHistory);
    method Bit#(length) recomputedHistory(Bool recovery, Maybe#(Bit#(TLog#(SupSize))) count);
    `endif
endinterface


module mkFoldedHistory#(Integer histLength, GlobalBranchHistory#(GlobalHistoryLength) global)(FoldedHistory#(length));
    Reg#(Bit#(length)) folded_history <- mkReg(0);
    
    // For out of order recovery of branch history
    Reg#(Bit#(MaxSpecSize)) last_spec_outcomes <- mkReg(0);
    Reg#(Bit#(MaxSpecSize)) last_removed_history <- mkReg(0);

    PulseWire recover <- mkPulseWire;

    RWire#(Tuple2#(Bit#(1), Bit#(1))) historyRecoveredUpdateData <- mkRWire;
    RWire#(Tuple3#(Bit#(SupSize), Bit#(SupSize), SupCnt)) historyUpdateData <- mkRWire;

    RWire#(Bit#(length)) recovered_history <- mkRWire;
    RWire#(Bit#(length)) recovered_updated_history <- mkRWire;
    RWire#(Bit#(length)) updated_history <- mkRWire;

    RWire#(Tuple2#(Bit#(MaxSpecSize), Bit#(MaxSpecSize))) updated_recover_info <- mkRWire;
    RWire#(Tuple2#(Bit#(MaxSpecSize), Bit#(MaxSpecSize))) updated_recovered_recover_info <- mkRWire;
    RWire#(Tuple2#(Bit#(MaxSpecSize), Bit#(MaxSpecSize))) recovered_recover_info <- mkRWire;


    Vector#(MaxSpecSize, FoldedRecoverMechanism#(length)) recoverIfc;
    Vector#(SupSize, HistorySameWindow#(length)) sameWindowHistoryIfc;

    // Some repeated code I should sort out at some point
    function Bit#(length) updatedHistory(Bit#(length) folded, Bit#(SupSize) eliminateBits, Bit#(SupSize) newHist, SupCnt count);
        Bit#(SupSize) new_bits = newHist ^ folded[valueOf(length)-1: valueOf(length)-valueOf(SupSize)];
        Bit#(length) new_folded_history = truncateLSB({folded, new_bits} << count);

        Bit#(SupSize) elim = 0;
        elim = truncateLSB({elim, eliminateBits} << count);
        for(Integer j = 0; j < valueOf(SupSize); j = j + 1) begin
            // Eliminate history out of bounds
            if(fromInteger(j) < count) begin
                Integer i = (histLength + j) % valueOf(length);
                new_folded_history[i] = new_folded_history[i] ^ elim[j];
            end
        end
        return new_folded_history;
    endfunction

    function Action updateWith(Bit#(SupSize) eliminateBits, Bit#(SupSize) newHistory, SupCnt count);
        action
            let newHist = reverseBits(newHistory);
           
            //folded_history[1] <= updatedHistory(folded_history[1], eliminateBits, newHist, count);
            let hist = updatedHistory(folded_history, eliminateBits, newHist, count);
            let rec = tuple2(truncateLSB({last_spec_outcomes, newHist} << count), truncateLSB({last_removed_history, eliminateBits} << count));
            
            
            updated_history.wset(hist);
            updated_recover_info.wset(rec);
            // For recovery updates 0001, 1000
            //last_spec_outcomes[1] <= truncateLSB({last_spec_outcomes[1], newHist} << count);
            //last_removed_history[1] <= truncateLSB({last_removed_history[1], eliminateBits} << count);
        endaction
    endfunction

    function Action updateRecoveredWith(Bit#(SupSize) eliminateBits, Bit#(SupSize) newHistory, SupCnt count);
        action
            let newHist = reverseBits(newHistory);
            if(!(isValid(recovered_history.wget) && isValid(recovered_recover_info.wget))) begin
                doAssert(False, "Failure");
            end
            let use_hist = fromMaybe(0, recovered_history.wget);
            match {.outcomes, .removed} = fromMaybe(tuple2(0,0), recovered_recover_info.wget);
           
            //folded_history[1] <= updatedHistory(folded_history[1], eliminateBits, newHist, count);
            let hist = updatedHistory(use_hist, eliminateBits, newHist, count);
            let rec = tuple2(truncateLSB({outcomes, newHist} << count), truncateLSB({removed, eliminateBits} << count));
            
            recovered_updated_history.wset(hist);
            updated_recovered_recover_info.wset(rec);

            // For recovery updates 0001, 1000
            //last_spec_outcomes[1] <= truncateLSB({last_spec_outcomes[1], newHist} << count);
            //last_removed_history[1] <= truncateLSB({last_removed_history[1], eliminateBits} << count);
        endaction
    endfunction

    (* no_implicit_conditions, fire_when_enabled *)
    rule updateAll;
        if(recovered_updated_history.wget matches tagged Valid .hist) begin
            if(updated_recovered_recover_info.wget matches tagged Valid {.outcomes, .removed}) begin
                folded_history <= hist;
                last_spec_outcomes <= outcomes;
                last_removed_history <= removed;
            end else begin
                doAssert(False, "Updated recovered history inconsistency\n");
            end
        end
        else if (updated_history.wget matches tagged Valid .hist) begin
            if(updated_recover_info.wget matches tagged Valid {.outcomes, .removed}) begin
                folded_history <= hist;
                last_spec_outcomes <= outcomes;
                last_removed_history <= removed;
            end else begin
                doAssert(False, "Updated history inconsistency\n");
            end
        end
    endrule

    // Normal update
    (* no_implicit_conditions, fire_when_enabled *)
    rule updateHist(historyUpdateData.wget matches tagged Valid {.eliminateBits, .newHistory, .count});
        updateWith(eliminateBits, newHistory, count);
    endrule

    // Recovery
    function Bit#(length) getUndidHistory(Bit#(TLog#(MaxSpecSize)) i, Bit#(TLog#(length)) shiftNum);
        UInt#(TLog#(MaxSpecSize)) recoverIndex = unpack(i); 
        // Restore deleted historu
        Bit#(length) recovered = folded_history;
        Integer j = histLength % valueOf(length);
        for(Integer k = 0; k < valueOf(MaxSpecSize); k = k +1) begin                    
            if(fromInteger(k) <= i) begin
                Bit#(1) eliminateBit = last_removed_history[k];
                Integer position = (j + k) % valueOf(length);
                recovered[position] = eliminateBit^recovered[position];
            end
        end
        
        Bit#(length) removed = recovered[recoverIndex:0] ^ last_spec_outcomes[recoverIndex:0];
        recovered = (removed[recoverIndex:0] << shiftNum) | truncateLSB(recovered >> (i+1));

        return recovered;
    endfunction

    function Bit#(length) recomputedHistory(Bool recovery, Maybe#(Bit#(TLog#(SupSize))) count, Bit#(GlobalHistoryLength) g);
        Bit#(length) ret = 0;
        
        /*if(recovery)
            g = global.recoveredHistory;
        else
            g = global.history;
            if(count matches tagged Valid .c)
                g = g << c;*/
        
        Integer div = histLength / valueOf(length);
        Integer rem = histLength - (div * valueOf(length));

        for(Integer i = 0; i < div; i = i + 1) begin
            Bit#(length) val = g[(i+1)*valueOf(length)-1:i*valueOf(length)];
            ret = ret ^ val;
        end
        
        if(rem > 0) begin
            Bit#(length) val2 = g[rem+(div*valueOf(length))-1 : div*valueOf(length)];
            ret = ret ^ val2;
        end
        return ret;
    endfunction

    function ActionValue#(Bit#(length)) undoHistory(Bit#(TLog#(MaxSpecSize)) i, Bit#(TLog#(length)) shiftNum, Bit#(1) taken, Bit#(GlobalHistoryLength) global_hist);
        actionvalue
            let recovered = recomputedHistory(True, tagged Invalid, global_hist);

            //historyRecoveredUpdateData.wset(tuple2(eliminateBit, taken));
            //updateRecoveredWith({eliminateBit,0}, zeroExtend(newHistory), 1);

            let newHistory = zeroExtend(taken);
            Bit#(1) eliminateBit = global_hist[histLength-1];
            Bit#(SupSize) eliminateBits = {eliminateBit,0};
            SupCnt count = 1;

            Bit#(SupSize) newHist = reverseBits(newHistory);
            let use_hist = recovered;
            
            Bit#(MaxSpecSize) outcomes = last_spec_outcomes >> (i+1);
            Bit#(MaxSpecSize) removed = last_removed_history >> (i+1);
            Bit#(MaxSpecSize) outcomes_updated = truncateLSB({outcomes, newHist} << count);
            Bit#(MaxSpecSize) removed_updated = truncateLSB({removed, eliminateBits} << count);

            let hist = updatedHistory(use_hist, eliminateBits, newHist, count);
            let rec = tuple2(outcomes_updated, removed_updated);
            recovered_updated_history.wset(hist);
            updated_recovered_recover_info.wset(rec);

            return recovered;
        endactionvalue
    endfunction


    for(Integer i = 0; i < valueOf(MaxSpecSize); i = i+1) begin
        recoverIfc[i] = (interface FoldedRecoverMechanism#(length);
            method Action undo(Bit#(1) taken, Bit#(GlobalHistoryLength) global_hist);
                let a <- undoHistory(fromInteger(i), fromInteger(valueOf(length)-1-i), taken, global_hist);
            endmethod

            `ifdef DEBUG
            method ActionValue#(Bit#(length)) debugUndo;
                let ret <- undoHistory(fromInteger(i), fromInteger(valueOf(length)-1-i));
                return ret;
            endmethod
            `endif
        endinterface);
    end

    /*for(Integer i = 0; i < valueOf(SupSize); i = i+1) begin
        sameWindowHistoryIfc[i] = (interface HistorySameWindow#(length);
            method Bit#(length) history;
                return recompute(False, tagged Valid fromInteger(i));
            endmethod
        endinterface);
    end*/

    for(Integer i = 0; i < valueOf(SupSize); i = i+1) begin
    sameWindowHistoryIfc[i] = (interface HistorySameWindow#(length);
        method Bit#(length) history;
            if (i == 0) begin
                return folded_history;
            end
            else begin
                Bit#(SupSize) eliminateBits = global.history[histLength-1 : histLength-valueOf(SupSize)];
                return updatedHistory(folded_history, eliminateBits, 0, fromInteger(i));
            end
        endmethod
    endinterface);
    end

    interface recoverFrom = recoverIfc;

    interface sameWindowHistory = sameWindowHistoryIfc;

    //recompute(False, tagged Invalid);
    //recompute(True, tagged Invalid);
    method Bit#(length) history;
        return folded_history;
    endmethod

    method Action updateHistory(Bit#(SupSize) newHistory, SupCnt count);
        // Shift and add new history bit, with older history
        Integer i = histLength % valueOf(length);
        Bit#(SupSize) eliminateBits = global.history[histLength-1 : histLength-valueOf(SupSize)];
        historyUpdateData.wset(tuple3(eliminateBits, newHistory, count));
    endmethod


    `ifdef DEBUG
    method Action debugInitialise(Bit#(length) newHistory);
        folded_history[0] <= newHistory;
    endmethod

    method Bit#(length) recomputedHistory(Bool recovery, Maybe#(Bit#(TLog#(SupSize))) count);
        Bit#(length) ret = 0;
        Bit#(GlobalHistoryLength) g = 0;
        
        if(recovery)
            g = global.recoveredHistory;
        else
            g = global.history;
            if(count matches tagged Valid .c)
                g = g << c;
        
        Integer div = histLength / valueOf(length);
        Integer rem = histLength - (div * valueOf(length));

        for(Integer i = 0; i < div; i = i + 1) begin
            Bit#(length) val = g[(i+1)*valueOf(length)-1:i*valueOf(length)];
            ret = ret ^ val;
        end
        
        if(rem > 0) begin
            Bit#(length) val2 = g[rem+(div*valueOf(length))-1 : div*valueOf(length)];
            ret = ret ^ val2;
        end
        return ret;
    endmethod
    `endif
endmodule