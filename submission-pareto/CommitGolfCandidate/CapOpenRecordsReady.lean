import CommitGolfCandidate.CapOpenRecordFrame
import CommitGolfCandidate.CapOpenReadDigest

/-! Natural windows for the actual record pass. A context gives the retained
input interval and output capacity; readiness tracks the consumed ordinal,
physical registers and the still-zero proof output above the cursor. The index
list is connected to reference memory explicitly, then the bounded byte frame
transports each real LD value at its current state. -/
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
  rootBound : roots+2147483648 ≤ MEMORY_BYTES
  saltAligned : salts % 8 = 0
  saltBound : salts+536870912 ≤ MEMORY_BYTES
  indexHigh : 32768 ≤ indices
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
  leaves : state.getReg .x19 = 4194304
  marks : state.getReg .x22 = 28672
  one : state.getReg .x31 = 1
  indices : state.getReg .x24 =
    BitVec.ofNat 64 (context.indices+8*(records.length-remaining))
  cursor : state.getReg .x25 =
    BitVec.ofNat 64 (context.output+576*(records.length-remaining))
  frame : CapOpenRetainedInputs context.output reference state
  nonceStride : state.getReg .x17 = 16
  fresh : ∀ address, address % 8 = 0 → context.output+576*(records.length-remaining) ≤ address →
    address+8 ≤ context.limit → state.getMem (BitVec.ofNat 64 address) = 0

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
  have addressHigh : 32768 ≤ context.indices+8*(records.length-(remaining+1)) := by
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

private theorem word_access (address : Nat) (aligned : address % 8 = 0)
    (bounded : address+8 ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) 8 = true := by
  have small : address < 2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, bounded, aligned, decide_true, Bool.true_and]

/-- A ready record pass with a record left is at a record entry of the opener. -/
theorem cap_open_records_entry (context : CapOpenRecordContext) (records : List Index)
    (reference state : MachineState) (remaining : Nat)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records reference)
    (ready : CapOpenRecordsReady context records reference (remaining+1) state) :
    CapOpenRecordAt context.roots context.salts
      (context.output+576*(records.length-(remaining+1))) context.limit
      (records[records.length-(remaining+1)]'(by
        have bounded := ready.bounded
        omega)).val state := by
  have bounded := ready.bounded
  have ordinalBound : records.length-(remaining+1) < records.length := by omega
  have positionBound : (records[records.length-(remaining+1)]'ordinalBound).val < 16777216 := by
    simpa only [LENGTH, LOG_LENGTH, Nat.reducePow] using
      (records[records.length-(remaining+1)]'ordinalBound).isLt
  have outputAligned := context.outputAligned
  have indexAligned := context.indexAligned
  have limitBound := context.limitBound
  have consumed : 576*(records.length-(remaining+1))+576 ≤ 576*records.length := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  have indexStep : 8*(records.length-(remaining+1))+8 ≤ 8*records.length := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  refine ⟨?_, ready.roots, ready.salts, ready.cursor,
    cap_open_records_loaded context records reference state remaining indexSpace inputs ready,
    ?_, positionBound, ready.leaves, ready.marks, ready.nonceStride, context.rootAligned,
    context.saltAligned, ?_, ?_, ?_, ?_, ?_, limitBound⟩
  · simpa using ready.pc
  · rw [ready.indices]
    exact word_access _ (by omega) (Nat.le_trans (by omega) limitBound)
  · omega
  · rw [show (2:Nat)^31 = 2147483648 from rfl]
    omega
  · omega
  · omega
  · omega

end CommitGolfCandidate
