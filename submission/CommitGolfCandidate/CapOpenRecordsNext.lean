import CommitGolfCandidate.CapOpenRecordsReady

/-! Transport of the actual record-pass invariant. The consumed ordinal
advances once, the residual decreases once, and the admitted input window
supplies the next index load even after earlier cap marks were changed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

theorem cap_open_records_ready_next (context : CapOpenRecordContext)
    (records : List Index) (reference state : MachineState) (remaining : Nat)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (inputs : CapOpenRecordInputs context records reference)
    (ready : CapOpenRecordsReady context records reference (remaining+1) state) :
    CapOpenRecordsReady context records reference remaining (capOpenRecordState state) := by
  have bounded := ready.bounded
  have currentPC : state.pc = 4212 := by simpa using ready.pc
  have ordinalBound : records.length-(remaining+1) < records.length := by omega
  let position := (records[records.length-(remaining+1)]'ordinalBound).val
  let cursor := context.output+576*(records.length-(remaining+1))
  have positionBound : position < 16777216 := by
    simpa only [position, LENGTH, LOG_LENGTH, Nat.reducePow] using
      (records[records.length-(remaining+1)]'ordinalBound).isLt
  have loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position :=
    cap_open_records_loaded context records reference state remaining indexSpace inputs ready
  have pointer : state.getReg .x25 = BitVec.ofNat 64 cursor := ready.cursor
  have aligned : cursor % 8 = 0 := by
    have base := context.outputAligned
    dsimp only [cursor]
    omega
  have space : cursor+576 ≤ context.limit := by
    dsimp only [cursor]
    omega
  refine ⟨by omega, cap_open_record_counter state (remaining+1) (by omega) ready.counter,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have exit := cap_open_record_exit state context.roots context.limit cursor position
      (remaining+1) currentPC ready.roots pointer aligned space context.limitBound
      positionBound loaded ready.leaves (by omega) (by omega) ready.counter
    by_cases last : remaining = 0
    · subst remaining
      simpa using exit
    · have more : remaining+1 ≠ 1 := by omega
      simpa only [last, more, ite_false] using exit
  · exact (cap_open_record_register state .x9 (by decide)).trans ready.roots
  · exact (cap_open_record_register state .x18 (by decide)).trans ready.salts
  · exact (cap_open_record_register state .x19 (by decide)).trans ready.leaves
  · exact (cap_open_record_register state .x22 (by decide)).trans ready.marks
  · exact (cap_open_record_register state .x31 (by decide)).trans ready.one
  · rw [cap_open_record_index_pointer, ready.indices]
    change BitVec.ofNat 64 (context.indices+8*(records.length-(remaining+1))) +
      BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [cap_open_record_cursor, ready.cursor, ← BitVec.ofNat_add]
    congr 1
    omega
  · exact cap_open_record_retained_inputs context.output context.roots context.limit
      cursor position state reference currentPC ready.roots pointer aligned space
      context.limitBound (by dsimp only [cursor]; omega) positionBound loaded
      ready.leaves ready.marks ready.frame

end CommitGolfCandidate
