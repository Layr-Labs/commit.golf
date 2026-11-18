import CommitGolfCandidate.CapOpenRecordsReady
import CommitGolfCandidate.CapOpenRecordLowFrame

/-! Transport of the actual record-pass invariant. The consumed ordinal
advances once, the residual decreases once, and the admitted input window
supplies the next index load even after earlier cap marks were changed. The
proof output above the advanced cursor is still zero. -/
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
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records reference)
    (ready : CapOpenRecordsReady context records reference (remaining+1) state) :
    CapOpenRecordsReady context records reference remaining (capOpenRecordState state) := by
  have bounded := ready.bounded
  have entry := cap_open_records_entry context records reference state remaining
    indexSpace outputSpace heapBelow saltsBelow inputs ready
  have limitBound := context.limitBound
  refine ⟨by omega, cap_open_record_counter entry (remaining+1) (by omega) ready.counter,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have exit := cap_open_record_exit entry (remaining+1) (by omega) (by omega) ready.counter
    by_cases last : remaining = 0
    · subst remaining
      simpa using exit
    · have more : remaining+1 ≠ 1 := by omega
      simpa only [last, more, ite_false] using exit
  · exact (cap_open_record_register state .x9 (by decide) entry).trans ready.roots
  · exact (cap_open_record_register state .x18 (by decide) entry).trans ready.salts
  · exact (cap_open_record_register state .x19 (by decide) entry).trans ready.leaves
  · exact (cap_open_record_register state .x22 (by decide) entry).trans ready.marks
  · exact (cap_open_record_register state .x31 (by decide) entry).trans ready.one
  · rw [cap_open_record_index_pointer entry, ready.indices]
    change BitVec.ofNat 64 (context.indices+8*(records.length-(remaining+1))) +
      BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · rw [cap_open_record_cursor entry]
    congr 1
    omega
  · exact cap_open_record_retained_inputs context.output entry reference (by omega) ready.frame
  · exact (cap_open_record_register state .x17 (by decide) entry).trans ready.nonceStride
  · intro address aligned lower upper
    have small : address+32 ≤ 2^64 := by
      have memory : MEMORY_BYTES+32 ≤ 2^64 := by simp only [MEMORY_BYTES]; omega
      omega
    rw [cap_open_record_high_word entry address aligned small (Or.inr (by omega))]
    exact ready.fresh address aligned (by omega) upper

end CommitGolfCandidate
