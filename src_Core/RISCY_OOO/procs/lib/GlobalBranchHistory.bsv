// Simple global history
// No speculative recovery or anything
import Assert::*;
import BrPred::*;
import BranchParams::*;
import Vector::*;
import ConfigReg::*;
import Ehr::*;
import ProcTypes::*;
import Types::*;



interface RecoverMechanism#(numeric type length);
    method ActionValue#(Bit#(length)) undo(Bit#(1) taken);
    `ifdef DEBUG
    method ActionValue#(Bit#(length)) debugUndo;
    `endif
endinterface

interface GlobalBranchHistory#(numeric type length);
    method Bit#(length) history;
    method Bit#(length) recoveredHistory;
    method Action addHistoryBits(Bit#(SupSize) taken, SupCnt count);
    interface Vector#(MaxSpecSize, RecoverMechanism#(length)) recoverFrom;
    `ifdef DEBUG
    method Action debugInitialise(Bit#(length) newHistory);
    `endif
endinterface

module mkGlobalBranchHistory(GlobalBranchHistory#(length));
    Reg#(Bit#(length)) shift_register <- mkReg(0);
    Reg#(Bit#(MaxSpecSize)) last_removed_history <- mkReg(0);
    
    RWire#(Tuple2#(Bit#(SupSize), SupCnt)) updateHistoryData <- mkRWire;
    RWire#(Bit#(1)) updateRecoveredHistoryData <- mkRWire;

    RWire#(Bit#(length)) recovered_history <- mkRWire;
    RWire#(Bit#(length)) recovered_updated_history <- mkRWire;
    RWire#(Bit#(length)) updated_history <- mkRWire;

    RWire#(Bit#(MaxSpecSize)) updated_recover_info <- mkRWire;
    RWire#(Bit#(MaxSpecSize)) updated_recovered_recover_info <- mkRWire;

    Vector#(MaxSpecSize, RecoverMechanism#(length)) recoverIfc;

    (* no_implicit_conditions, fire_when_enabled *)
    rule updateHist(updateHistoryData.wget matches tagged Valid {.results, .count});
        //shift_register[1] <= truncateLSB({shift_register[1], reverseBits(results)} << count);
        updated_history.wset(truncateLSB({shift_register, reverseBits(results)} << count));
        Bit#(SupSize) bits = shift_register[valueOf(length)-1: valueOf(length)-valueOf(SupSize)];
        updated_recover_info.wset(truncateLSB({last_removed_history, bits} << count));
    endrule

    (* no_implicit_conditions, fire_when_enabled *)
    rule updateAll;
        if(recovered_updated_history.wget matches tagged Valid .hist) begin
            if(updated_recovered_recover_info.wget matches tagged Valid .removed) begin
                shift_register <= hist;
                last_removed_history <= removed;
            end else begin
                doAssert(False, "Updated recovered history inconsistency\n");
            end
        end
        else if (updated_history.wget matches tagged Valid .hist) begin
            if(updated_recover_info.wget matches tagged Valid .removed) begin
                shift_register <= hist;
                last_removed_history <= removed;
            end else begin
                doAssert(False, "Updated history inconsistency\n");
            end
        end
    endrule

    function ActionValue#(Bit#(length)) undoHistory(Bit#(TLog#(MaxSpecSize)) i, Bit#(1) taken);
        actionvalue
            UInt#(TLog#(MaxSpecSize)) j = unpack(i);
            Bit#(length) recovered = (last_removed_history[j:0] << (valueOf(length)-1)) >> i | truncateLSB(shift_register >> (i+1));
            let use_hist = recovered;
            let removed = last_removed_history >> (i+1);

            recovered_history.wset(recovered);
            recovered_updated_history.wset(truncateLSB({use_hist, taken} << 1));
            updated_recovered_recover_info.wset(truncateLSB({removed, use_hist[valueOf(length)-1]} << 1));
            return recovered;
        endactionvalue
    endfunction

    for(Integer i = 0; i < valueOf(MaxSpecSize); i = i+1) begin
        recoverIfc[i] = (interface RecoverMechanism#(length);
            method ActionValue#(Bit#(length)) undo(Bit#(1) taken);
                let a <- undoHistory(fromInteger(i), taken);
                return a;
            endmethod

            `ifdef DEBUG
            method ActionValue#(Bit#(length)) debugUndo;
                let ret <- undoHistory(fromInteger(i));
                return ret;
            endmethod
            `endif
        endinterface);
    end
    interface recoverFrom = recoverIfc;

    method Action addHistoryBits(Bit#(SupSize) taken, SupCnt count);
        updateHistoryData.wset(tuple2(taken, count));
        //update.send;
    endmethod


    method Bit#(length) history = shift_register;
    method Bit#(length) recoveredHistory;
        return shift_register; // !!!
    endmethod

    `ifdef DEBUG
    method Action debugInitialise(Bit#(length) newHistory);
        shift_register[0] <= newHistory;
    endmethod
    `endif
endmodule