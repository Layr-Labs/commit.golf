import CommitGolfCandidate.Layout2Phase2
import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.GroupOpenCapEmitPrefix
import CommitGolfCandidate.GroupOpenTable

/-! Fused opener (Layout 2 V2 Increment 4b), the loop code after each phase writer: the per-phase tail
(`ftailWord p`, 6 or 7 words: stride, byte mark of the cap leaf, index advance, latch) and the exit stubs
(`fexitWord p`: flush of the 6/4/2/0 pending stream bytes of `tp` and the jump to the cap stage at 6960). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase)
open CommitGolfCandidate.Layout2Phase2 (bodyLen)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem heap_base : Layout2Phase.heapBase=trapdoorBase := by decide
theorem slot_base : Layout2Phase.slotBase=groupSlots := by decide
theorem salt_base : Layout2Phase.saltBase=nonceBase := by decide
theorem record_base0 : Layout2Phase.recordBase0=proofBase := by decide
theorem word_address (i : Nat) : Layout2Phase.wordAddress i=address i := rfl

/-- Fused loop geometry (Layout 2 V2 Increment 4b): phase `p` of the loop starts at `fphaseWord p`; its writer
(`Layout2Writer3`, `writerLen p` words) at `fwriterWord p`; its tail (stride, byte mark, index advance, latch) at
`ftailWord p`; its exit stub at `fexitWord p`. -/
def fphaseWord (p : Nat) : Nat := 4097+272*p
def fwriterWord (p : Nat) : Nat := 4160+272*p
def ftailWord (p : Nat) : Nat := fwriterWord p+(bodyLen p-1)
def fexitWord (p : Nat) : Nat := if p=3 then 5178 else ftailWord p+6
/-- Bytes the exit stub of phase `p` flushes (the pending stream bits of `tp`). -/
def flushLen (p : Nat) : Nat := if p=0 then 6 else if p=1 then 4 else if p=2 then 2 else 0
/-- Cycles of the exit stub of phase `p`. -/
def exitCost (p : Nat) : Nat := if p=0 then 5 else if p=3 then 1 else 3

/-- `jal`/branch offsets from word `w` to word `t`, in Nat arithmetic (no `Int`, cheap for the kernel). -/
def jumpTo (w t : Nat) : BitVec 21 := BitVec.ofNat 21 ((2097152+4*t-4*w)%2097152)
def branchTo (w t : Nat) : BitVec 13 := BitVec.ofNat 13 ((8192+4*t-4*w)%8192)

/-- The straight part of a fused tail: `addi s5,s5,stride; srli t1,t1,1; add t2,s10,t1; sb s7,0(t2); addi s0,s0,8`.
The mark of the record's cap leaf `256 + pos/65536` is the byte `1` at `4096 + 256 + pos/65536`. -/
def tailBodyRows (p : Nat) : List Row :=
  [(ftailWord p,.ADDI .x21 .x21 (BitVec.ofNat 12 (stride p))),(ftailWord p+1,.SRLI .x6 .x6 1),
   (ftailWord p+2,.ADD .x7 .x26 .x6),(ftailWord p+3,.SB .x7 .x23 0),(ftailWord p+4,.ADDI .x8 .x8 8)]
/-- The latch: `bne s0,a7,<next phase>` (phases 0..2, falling through to the exit stub), or for phase 3
`beq s0,a7,<5178>` and, unless it was the last record, `jal <4097>`. -/
def latchRows (p : Nat) (last : Bool) : List Row :=
  if p=3 then (5176,.BEQ .x8 .x17 (branchTo 5176 5178)) :: (if last then [] else [(5177,.JAL .x0 (jumpTo 5177 4097))])
  else [(ftailWord p+5,.BNE .x8 .x17 (branchTo (ftailWord p+5) (fphaseWord (p+1))))]
def ftailRows (p : Nat) (last : Bool) : List Row := tailBodyRows p ++ latchRows p last
/-- Cycles of a fused tail. -/
def tailCost (p : Nat) (last : Bool) : Nat := if p=3 ∧ last=false then 7 else 6

def fexitRows (p : Nat) : List Row :=
  if p=0 then [(4358,.SW .x21 .x4 0),(4359,.SRLI .x4 .x4 32),(4360,.SH .x21 .x4 4),(4361,.ADDI .x21 .x21 6),
    (4362,.JAL .x0 (jumpTo 4362 6960))]
  else if p=1 then [(4634,.SW .x21 .x4 0),(4635,.ADDI .x21 .x21 4),(4636,.JAL .x0 (jumpTo 4636 6960))]
  else if p=2 then [(4906,.SH .x21 .x4 0),(4907,.ADDI .x21 .x21 2),(4908,.JAL .x0 (jumpTo 4908 6960))]
  else [(5178,.JAL .x0 (jumpTo 5178 6960))]

theorem tail_words : ftailWord 0=4352 ∧ ftailWord 1=4628 ∧ ftailWord 2=4900 ∧ ftailWord 3=5171 := by decide

theorem tail_present (p : Nat) (hp : p<4) (last : Bool) : presentRows (ftailRows p last) := by
  apply rows_present; revert p; cases last <;> decide +kernel
theorem exit_present (p : Nat) (hp : p<4) : presentRows (fexitRows p) := by
  apply rows_present; revert p; decide +kernel

theorem exit_words (p : Nat) (hp : p<4) : (fexitRows p).head?.map Prod.fst=some (fexitWord p) := by
  revert p; decide

theorem exit_cost (p : Nat) (hp : p<4) : price (fexitRows p)=exitCost p ∧ (fexitRows p).length=exitCost p := by
  revert p; decide

theorem tail_cost (p : Nat) (hp : p<4) (last : Bool) : price (ftailRows p last)=tailCost p last ∧
    (ftailRows p last).length=tailCost p last := by
  revert p; cases last <;> decide

/-! ### Word and halfword stores of the exit stubs -/

private theorem offset_bound (address : Word) : byteOffset address<8 := by
  unfold byteOffset
  have h : (address &&& 7#64).toNat ≤ 7 := by
    rw [BitVec.toNat_and]; exact (Nat.and_le_right).trans (by decide)
  omega

private theorem replace_word_read (word : Word) (value : BitVec 32) (slot index : Nat)
    (slotBound : slot<2) (indexBound : index<8) :
    extractByte (replaceWord32 word slot value) index =
      if index/4=slot then (value >>> ((index%4)*8)).truncate 8 else extractByte word index := by
  interval_cases slot <;> interval_cases index <;>
    simp (config := {decide := true}) [extractByte, replaceWord32] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit bitBound <;> interval_cases bit <;>
    simp

/-- A 32-bit store changes the four bytes of one word slot of one doubleword. -/
theorem word_store_byte (state : MachineState) (destination query : Word) (value : BitVec 32) :
    (state.setWord32 destination value).getByte query =
      if alignToDword query=alignToDword destination ∧ byteOffset query/4=byteOffset destination/4 then
        (value >>> ((byteOffset query%4)*8)).truncate 8
      else state.getByte query := by
  by_cases aligned : alignToDword query=alignToDword destination
  · simp only [MachineState.setWord32, MachineState.getByte, aligned, MachineState.getMem_setMem_eq, true_and]
    exact replace_word_read _ _ _ _ (by have := offset_bound destination; omega) (offset_bound query)
  · simp only [MachineState.setWord32, MachineState.getByte, MachineState.getMem_setMem_ne aligned, aligned,
      false_and, ite_false]

private theorem nat_offset (q : Nat) (fit : q<2^64) : byteOffset (BitVec.ofNat 64 q)=q%8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit,
    show (7#64 : Word).toNat=2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

private theorem nat_align (q : Nat) (fit : q<2^64) : (alignToDword (BitVec.ofNat 64 q)).toNat=q-q%8 := by
  have whole : alignToDword (BitVec.ofNat 64 q)+BitVec.ofNat 64 (byteOffset (BitVec.ofNat 64 q))=BitVec.ofNat 64 q :=
    table_align_add _
  rw [nat_offset q fit] at whole
  have t := congrArg BitVec.toNat whole
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit,
    Nat.mod_eq_of_lt (show q%8<2^64 by omega)] at t
  have bound : (alignToDword (BitVec.ofNat 64 q)).toNat ≤ q := by
    change (BitVec.ofNat 64 q &&& ~~~7#64).toNat ≤ q
    rw [BitVec.toNat_and]
    exact Nat.and_le_left.trans (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit])
  omega

private theorem same_align (a b : Nat) (fa : a<2^64) (fb : b<2^64) :
    alignToDword (BitVec.ofNat 64 a)=alignToDword (BitVec.ofNat 64 b) ↔ a-a%8=b-b%8 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; rwa [nat_align a fa, nat_align b fb] at this
  · intro h; apply BitVec.eq_of_toNat_eq; rw [nat_align a fa, nat_align b fb, h]

/-- Byte `b < 4` of a word stored at an 8-aligned address. -/
theorem word_stored (state : MachineState) (D b : Nat) (v : BitVec 32) (al : D%8=0) (fit : D+8 ≤ 2^64)
    (small : b<4) :
    (state.setWord32 (BitVec.ofNat 64 D) v).getByte (BitVec.ofNat 64 (D+b))=v.extractLsb' (8*b) 8 := by
  rw [word_store_byte, if_pos ⟨(same_align _ _ (by omega) (by omega)).mpr (by omega),
    by rw [nat_offset _ (by omega), nat_offset _ (by omega)]; omega⟩, nat_offset _ (by omega)]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, show (D+b)%8%4=b by omega]
  rw [Nat.mul_comm b 8]

/-- A word stored at an 8-aligned `D` leaves every byte outside `[D, D+4)`. -/
theorem word_outside (state : MachineState) (D a : Nat) (v : BitVec 32) (al : D%8=0) (fit : D+8 ≤ 2^64)
    (fa : a<2^64) (away : a<D ∨ D+4 ≤ a) :
    (state.setWord32 (BitVec.ofNat 64 D) v).getByte (BitVec.ofNat 64 a)=state.getByte (BitVec.ofNat 64 a) := by
  rw [word_store_byte, if_neg]
  rintro ⟨same, slot⟩
  rw [same_align _ _ fa (by omega)] at same
  rw [nat_offset _ fa, nat_offset _ (by omega)] at slot
  omega

/-- Byte `b < 2` of a halfword stored at an even address. -/
theorem half_stored (state : MachineState) (D b : Nat) (v : BitVec 16) (al : D%2=0) (fit : D+2 ≤ 2^64)
    (small : b<2) :
    (state.setHalfword (BitVec.ofNat 64 D) v).getByte (BitVec.ofNat 64 (D+b))=v.extractLsb' (8*b) 8 :=
  emit_stored_byte state D b v al fit small

end TwoPermutationPrototype.GroupedOpening.Layout2
