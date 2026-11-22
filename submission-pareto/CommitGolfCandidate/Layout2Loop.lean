import CommitGolfCandidate.Layout2Phase
import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.GroupOpenCapEmitPrefix
import CommitGolfCandidate.GroupOpenTable

/-! Layout 2 opener, record loop code around the phase writers: the first record's header (words 15..17) with the
entry jump (18) and the entry stub (5071, 5072), the per-phase header (`hdrWord p`, 3 words), the per-phase tail
(`tailWord p`, 7 words: stride, mark of the cap leaf, index advance, latch) and the exit stubs (`exitWord p`:
flush of the 6/4/2/0 pending stream bytes and the jump to the cap preparation at 1097). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase bodyWord bodyLen tailWord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem heap_base : Layout2Phase.heapBase=trapdoorBase := by decide
theorem slot_base : Layout2Phase.slotBase=groupSlots := by decide
theorem salt_base : Layout2Phase.saltBase=nonceBase := by decide
theorem record_base0 : Layout2Phase.recordBase0=proofBase := by decide
theorem word_address (i : Nat) : Layout2Phase.wordAddress i=address i := rfl

/-- First word of phase `p`'s header and of its exit stub. -/
def hdrWord (p : Nat) : Nat := bodyWord p-3
def exitWord (p : Nat) : Nat := tailWord p+7
/-- Bytes the exit stub of phase `p` flushes (the pending stream bits of `a1`). -/
def flushLen (p : Nat) : Nat := if p=0 then 6 else if p=1 then 4 else if p=2 then 2 else 0
/-- Cycles of the exit stub of phase `p`. -/
def exitCost (p : Nat) : Nat := if p=0 then 5 else if p=3 then 1 else 3

/-- `jal`/branch offsets from word `w` to word `t`, in Nat arithmetic (no `Int`, cheap for the kernel). -/
def jumpTo (w t : Nat) : BitVec 21 := BitVec.ofNat 21 ((2097152+4*t-4*w)%2097152)
def branchTo (w t : Nat) : BitVec 13 := BitVec.ofNat 13 ((8192+4*t-4*w)%8192)

/-- A record header at word `w`: `ld t1,0(s0); slli t2,t1,4; add t2,s6,t2`. -/
def hdrRowsAt (w : Nat) : List Row := [(w,.LD .x6 .x8 0),(w+1,.SLLI .x7 .x6 4),(w+2,.ADD .x7 .x22 .x7)]
def hdrRows (p : Nat) : List Row := hdrRowsAt (hdrWord p)
/-- Word 18 and the entry stub: `jal <5071>`, `addi s2,s8,584`, `jal <4099>`. -/
def jumpRows : List Row := [(18,.JAL .x0 (jumpTo 18 5071)),(5071,.ADDI .x18 .x24 584),(5072,.JAL .x0 (jumpTo 5072 4099))]
/-- Words 15..18 and the entry stub. -/
def firstRows : List Row := hdrRowsAt 15++jumpRows

def tailRows (p : Nat) : List Row :=
  [(tailWord p,.ADDI .x21 .x21 (BitVec.ofNat 12 (stride p))),(tailWord p+1,.SRLI .x6 .x6 1),
   (tailWord p+2,.SLLI .x7 .x6 3),(tailWord p+3,.ADD .x7 .x26 .x7),(tailWord p+4,.SD .x7 .x23 0),
   (tailWord p+5,.ADDI .x8 .x8 8),(tailWord p+6,.BNE .x8 .x17 (branchTo (tailWord p+6) (hdrWord ((p+1)%4))))]

def exitRows (p : Nat) : List Row :=
  if p=0 then [(4334,.SW .x21 .x11 0),(4335,.SRLI .x11 .x11 32),(4336,.SH .x21 .x11 4),(4337,.ADDI .x21 .x21 6),
    (4338,.JAL .x0 (jumpTo 4338 1097))]
  else if p=1 then [(4581,.SW .x21 .x11 0),(4582,.ADDI .x21 .x21 4),(4583,.JAL .x0 (jumpTo 4583 1097))]
  else if p=2 then [(4826,.SH .x21 .x11 0),(4827,.ADDI .x21 .x21 2),(4828,.JAL .x0 (jumpTo 4828 1097))]
  else [(5070,.JAL .x0 (jumpTo 5070 1097))]

theorem first_hdr_present : presentRows (hdrRowsAt 15) := by apply rows_present; decide +kernel
theorem jump_present : presentRows jumpRows := by apply rows_present; decide +kernel
theorem hdr_present (p : Nat) (hp : p<4) : presentRows (hdrRows p) := by
  apply rows_present; revert p; decide +kernel
theorem tail_present (p : Nat) (hp : p<4) : presentRows (tailRows p) := by
  apply rows_present; revert p; decide +kernel
theorem exit_present (p : Nat) (hp : p<4) : presentRows (exitRows p) := by
  apply rows_present; revert p; decide +kernel

theorem exit_words (p : Nat) (hp : p<4) : (exitRows p).head?.map Prod.fst=some (exitWord p) := by
  revert p; decide

theorem exit_cost (p : Nat) (hp : p<4) : price (exitRows p)=exitCost p ∧ (exitRows p).length=exitCost p := by
  revert p; decide

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
