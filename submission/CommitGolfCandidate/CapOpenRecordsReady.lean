import CommitGolfCandidate.CapOpenRecordFrame
import CommitGolfCandidate.CapOpenReadDigest

/-! Natural windows for the actual record pass. A context gives the retained
input interval and output capacity; readiness tracks the consumed ordinal and
physical registers. The index list is connected to reference memory explicitly,
then the bounded byte frame transports each real LD value at its current state. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

structure CapOpenRecordContext where
  roots : Nat
  salts : Nat
  indices : Nat
  output : Nat
  limit : Nat
  rootAligned : roots % 8 = 0
  rootBound : roots+1073741824 ≤ MEMORY_BYTES
  saltAligned : salts % 8 = 0
  saltBound : salts+536870912 ≤ MEMORY_BYTES
  indexHigh : 22528 ≤ indices
  indexAligned : indices % 8 = 0
  outputAligned : output % 8 = 0
  limitBound : limit ≤ MEMORY_BYTES

def CapOpenRecordInputs (context : CapOpenRecordContext) (records : List Index)
    (reference : MachineState) : Prop :=
  ∀ ordinal (inside : ordinal < records.length),
    reference.getMem (BitVec.ofNat 64 (context.indices+8*ordinal)) =
      BitVec.ofNat 64 (records[ordinal]'inside).val

structure CapOpenRecordsReady (context : CapOpenRecordContext) (records : List Index)
    (reference : MachineState) (remaining : Nat) (state : MachineState) : Prop where
  bounded : remaining ≤ records.length
  counter : state.getReg .x27 = BitVec.ofNat 64 remaining
  pc : state.pc = if remaining = 0 then 4364 else 4212
  roots : state.getReg .x9 = BitVec.ofNat 64 context.roots
  salts : state.getReg .x18 = BitVec.ofNat 64 context.salts
  leaves : state.getReg .x19 = 16777216
  marks : state.getReg .x22 = 20480
  one : state.getReg .x31 = 1
  indices : state.getReg .x24 =
    BitVec.ofNat 64 (context.indices+8*(records.length-remaining))
  cursor : state.getReg .x25 =
    BitVec.ofNat 64 (context.output+576*(records.length-remaining))
  frame : CapOpenRetainedInputs context.output reference state

theorem cap_open_records_loaded (context : CapOpenRecordContext) (records : List Index)
    (reference state : MachineState) (remaining : Nat)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (inputs : CapOpenRecordInputs context records reference)
    (ready : CapOpenRecordsReady context records reference (remaining+1) state) :
    state.getMem (state.getReg .x24) =
      BitVec.ofNat 64 (records[records.length-(remaining+1)]'(by
        have bounded := ready.bounded
        omega)).val := by
  have bounded := ready.bounded
  have ordinalBound : records.length-(remaining+1) < records.length := by omega
  have addressHigh : 22528 ≤ context.indices+8*(records.length-(remaining+1)) := by
    have high := context.indexHigh
    omega
  have addressInside : context.indices+8*(records.length-(remaining+1))+32 ≤
      context.output := by omega
  have aligned : (context.indices+8*(records.length-(remaining+1))) % 8 = 0 := by
    have indexAligned := context.indexAligned
    omega
  have same := cap_open_retained_read context.output reference state
    (context.indices+8*(records.length-(remaining+1))) 32
    addressHigh addressInside ready.frame
  have word := congrArg (fun digest : Digest => digest.extractLsb' 0 64) same
  have words : state.getMem
      (BitVec.ofNat 64 (context.indices+8*(records.length-(remaining+1)))) =
      reference.getMem
        (BitVec.ofNat 64 (context.indices+8*(records.length-(remaining+1)))) := by
    simpa only [read_digest_word _ _ 0 aligned (by decide), Nat.mul_zero,
      Nat.add_zero] using word
  rw [ready.indices, words]
  exact inputs _ ordinalBound

end CommitGolfCandidate
