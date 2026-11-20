import CommitGolfCandidate.GroupOpenSibling
import CommitGolfCandidate.GroupOpenFields
import CommitGolfCandidate.TwoPermutationOpeningGeometry

namespace TwoPermutationPrototype.GroupedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64


def nonceAddress (index : Index) : Nat := nonceBase+16*index.val

/-- Where the writer copies the level-`level` sibling of `index` from: the commit's level-22 node of the sibling
quartet for level 0 (through the prefix's pointer word), the heap slot otherwise. -/
def siblingAddress (index : Index) (level : Nat) : Nat :=
  if level = 0 then quadAddress index.val else trapdoorBase+32*(upperNode index level ^^^ 1)

theorem sibling_address_upper (index : Index) (level : Nat) (nz : level ≠ 0) :
    siblingAddress index level = trapdoorBase+32*(upperNode index level ^^^ 1) := by
  unfold siblingAddress; rw [if_neg nz]

theorem sibling_address_inside (index : Index) (level : Nat) :
    siblingAddress index level % 8 = 0 ∧ trapdoorBase ≤ siblingAddress index level ∧
      siblingAddress index level+32 ≤ nonceBase := by
  by_cases zero : level = 0
  · unfold siblingAddress; rw [if_pos zero]
    exact quad_address_inside index.val index.isLt
  · rw [sibling_address_upper index level zero]
    have bound := upper_swap_bound index level
    have heapEnd := heap_before_nonces
    have base : trapdoorBase % 8 = 0 := by decide
    omega

theorem packed_proof_memory : proofBase+capacity ≤ MEMORY_BYTES := by decide

theorem all_record_ends_fit (ordinal : Nat) (inside : ordinal < LENGTH) :
    recordBase (ordinal+1) ≤ MEMORY_BYTES := by
  apply Nat.le_trans _ packed_proof_memory
  unfold recordBase capacity
  apply Nat.add_le_add_left
  exact (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt inside)).trans (Nat.le_add_right _ _)

theorem all_nonce_copies_fit (index : Index) (ordinal : Nat) (inside : ordinal < LENGTH) :
    nonceAddress index % 2 = 0 ∧ recordBase ordinal % 2 = 0 ∧
      nonceAddress index+16 ≤ recordBase ordinal ∧ recordBase ordinal+16 ≤ MEMORY_BYTES := by
  have endRecord := all_record_ends_fit ordinal inside
  have indexBound := index.isLt
  have tapeEnd := nonces_end_at_indices
  have indexEnd := indices_before_records
  have nonceEven : nonceBase % 2 = 0 := by decide
  have proofEven : proofBase % 2 = 0 := by decide
  unfold nonceAddress recordBase recordBytes at *
  omega

theorem all_sibling_copies_fit (index : Index) (ordinal level : Nat)
    (inside : ordinal < LENGTH) (valid : level < 14) :
    siblingAddress index level % 2 = 0 ∧ siblingDestination ordinal level % 2 = 0 ∧
      siblingAddress index level+siblingWidth level ≤ siblingDestination ordinal level ∧
      siblingDestination ordinal level+siblingWidth level ≤ MEMORY_BYTES := by
  have endRecord := all_record_ends_fit ordinal inside
  have offsets := sibling_inside_record level valid
  have src := sibling_address_inside index level
  have indexEnd := indices_before_records
  have tapeEnd := nonces_end_at_indices
  have widthBound : siblingWidth level ≤ 32 := sibling_width_le level
  refine ⟨by omega, even_sibling_destination ordinal level, ?_, ?_⟩
  all_goals simp only [siblingDestination, recordBase, recordBytes, Nat.mul_add] at * <;> omega

theorem physical_nonce_source (state : MachineState) (index : Index)
    (tape : state.getReg .x22 = BitVec.ofNat 64 nonceBase)
    (readIndex : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index.val) :
    (nonceSetup state).getReg .x7 = BitVec.ofNat 64 (nonceAddress index) := by
  rw [(nonce_setup_post state).2.2.1, Opening.nonceSource, tape,readIndex,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 nonceBase + BitVec.ofNat 64 index.val * BitVec.ofNat 64 16 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm _ 16, ← BitVec.ofNat_add]
  rfl

theorem physical_sibling_source (state : MachineState) (index : Index) (level : Nat) (nz : level ≠ 0)
    (heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (node : state.getReg .x6 = BitVec.ofNat 64 (upperNode index level)) :
    (headPrefix state 3).getReg .x7 = BitVec.ofNat 64 (siblingAddress index level) := by
  rw [sibling_address_upper index level nz, (sibling_head_post state).2.2.1, heap, node, ← BitVec.ofNat_xor,
    BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 trapdoorBase + BitVec.ofNat 64 (upperNode index level ^^^ 1) *
    BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm _ 32, ← BitVec.ofNat_add]

theorem node_shift (index : Index) (level : Nat) :
    BitVec.ofNat 64 (upperNode index level) >>> 1 = BitVec.ofNat 64 (upperNode index (level+1)) := by
  rw [upper_node_next]
  apply BitVec.eq_of_toNat_eq
  have size := upper_node_bound index level
  have length64 : 2*LENGTH < 2^64 := by decide
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show upperNode index level < 2^64 by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]

theorem physical_sibling_parent {state : MachineState} (index : Index) (level : Fin 14)
    (node : state.getReg .x6 = BitVec.ofNat 64 (upperNode index level.val)) :
    (tailPrefix state level 2).getReg .x6 = BitVec.ofNat 64 (upperNode index (level.val+1)) := by
  rw [(sibling_tail_post state level).2.2.2.1, node, node_shift]

theorem destination_next (ordinal level : Nat) (inside : level < 14) :
    BitVec.ofNat 64 (siblingDestination ordinal level) + BitVec.ofNat 64 (siblingWidth level) =
      BitVec.ofNat 64 (siblingDestination ordinal (level+1)) := by
  rw [← BitVec.ofNat_add]
  congr 1
  simp [siblingDestination, sibling_offset_next level inside, Nat.add_assoc]

theorem physical_sibling_destination {state : MachineState} (ordinal : Nat) (level : Fin 14)
    (dest : state.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level.val)) :
    (tailPrefix state level 2).getReg .x21 =
      BitVec.ofNat 64 (siblingDestination ordinal (level.val+1)) := by
  rw [(sibling_tail_post state level).2.2.1, dest, destination_next ordinal level.val level.isLt]

end TwoPermutationPrototype.GroupedOpening
