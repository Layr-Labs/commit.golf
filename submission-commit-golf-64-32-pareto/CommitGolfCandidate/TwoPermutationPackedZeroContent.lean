import CommitGolfCandidate.TwoPermutationPackedZeroLeaves
import CommitGolfCandidate.TwoPermutationPinnedCommitSpec

/-! The heap after the zeroing loop holds 240-bit leaf digests. -/
namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000

theorem trunc_word3 (d : BitVec 256) :
    (BitVec.ofNat 256 (d.toNat % 2^240)).extractLsb' 192 64 = replaceHalfword (d.extractLsb' 192 64) 3 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold replaceHalfword
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, hi, decide_true,
    Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
  by_cases low : i < 48
  · have a : 192+i < 240 := by omega
    have c : ¬ (i < 3*16) = False := by simp; omega
    simp [a, low, show 192+i < 256 by omega, BitVec.testBit_toNat]
  · have a : ¬ 192+i < 240 := by omega
    simp [a, show 192+i < 256 by omega]
    intro _
    rw [show (65535 : Nat) = 2^16-1 by norm_num, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    omega
theorem trunc_low (d : BitVec 256) (k : Nat) (hk : k < 3) :
    (BitVec.ofNat 256 (d.toNat % 2^240)).extractLsb' (64*k) 64 = d.extractLsb' (64*k) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, hi, decide_true,
    Bool.true_and]
  have a : 64*k+i < 256 := by omega
  have b : 64*k+i < 240 := by omega
  simp [a, b, BitVec.testBit_toNat]

private theorem not_zeroed (w : Nat) (bound : w < 2^61)
    (avoid : ∀ j < 2^24, w ≠ leafDest j + 3) :
    ¬ ∃ j < 2^24, wordAddress w = zeroAddress j := by
  rintro ⟨j, lt, same⟩
  have n := congrArg BitVec.toNat same
  simp only [zeroAddress, wordAddress, BitVec.toNat_ofNat] at n
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by unfold leafDest; omega)] at n
  exact avoid j lt (by omega)

theorem memory_view_mem (st : MachineState) (w : Nat) : memoryView st w = st.mem (wordAddress w) := rfl

theorem pinned_parent_content_zeroed (oracle : Oracle) (before : Memory) (leaves : MachineState)
    (atLeaves : leaves.pc = 184608) (stride : leaves.getReg .x19 = 536870912)
    (stop : leaves.getReg .x21 = wordAddress (leafDest (2^24)))
    (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (inv : PinnedLeafPrefix oracle before leaves (2^24))
    (leaf : ∀ i : Index, heap (LENGTH+i.val) =
      BitVec.ofNat 256 ((outputDigest (pinnedFinalReply oracle before i.val)).toNat % 2^240))
    (original_salts : ∀ i : Index, (window before (leafSalt i.val) : Words 2)=saltWords (salts i)) :
    ParentContent (zeroEntry leaves) heap salts (2^24-1) := by
  have mem := zero_entry_mem leaves atLeaves stride stop
  have view (w : Nat) : memoryView (zeroEntry leaves) w = zeroedMemory leaves.mem (2^24) (wordAddress w) := by
    rw [memory_view_mem, mem]
  constructor
  · intro n lo hi
    have valid : n-LENGTH<LENGTH := by omega
    let i : Index := ⟨n-LENGTH,valid⟩
    have idx : n=LENGTH+i.val := by change n=LENGTH+(n-LENGTH);change 2^24-1<n at lo; have e : LENGTH=2^24:=rfl;omega
    rw [idx,leaf i]
    unfold nodeDigest
    have addr : treeWord (LENGTH+i.val)=leafDest i.val := by change 516+32*2^24+4*(2^24+i.val)=_;unfold leafDest;omega
    rw [addr]
    apply aligned_buffer_eq (zeroEntry leaves) _ 32 (by decide)
    intro k hk
    have value := congrFun (inv.digests i.val i.isLt) (⟨k,hk⟩ : Fin 4)
    change memoryView leaves (leafDest i.val+k)=_ at value
    rw [low_digest_word _ (⟨k,hk⟩ : Fin 4)] at value
    rw [view]
    have iLt : i.val < 2^24 := i.isLt
    by_cases top : k = 3
    · subst top
      have hit : ∃ j < 2^24, wordAddress (leafDest i.val + 3) = zeroAddress j := ⟨i.val, iLt, rfl⟩
      rw [zeroed_hit _ _ _ hit]
      change replaceHalfword (memoryView leaves (leafDest i.val+3)) 3 0 = _
      rw [value]
      exact (trunc_word3 _).symm
    · have miss := not_zeroed (leafDest i.val + k) (by unfold leafDest; omega)
        (fun j _ eq => by unfold leafDest at eq; omega)
      rw [zeroed_miss _ _ _ miss]
      change memoryView leaves (leafDest i.val+k) = _
      rw [value]
      exact (trunc_low _ k (by omega)).symm
  · intro i
    unfold nonceBuffer
    apply aligned_buffer_eq (zeroEntry leaves) _ 16 (by decide)
    intro k hk
    have iLt : i.val < 2^24 := i.isLt
    have v := congrFun ((inv.salts i.val i.isLt).trans (original_salts i)) (⟨k,hk⟩ : Fin 2)
    rw [view]
    have miss := not_zeroed (leafSalt i.val + k) (by unfold leafSalt; omega)
      (fun j lt eq => by unfold leafSalt leafDest at eq; omega)
    rw [zeroed_miss _ _ _ miss]
    exact v

end TwoPermutationPrototype.RV64.PackedLeaves
