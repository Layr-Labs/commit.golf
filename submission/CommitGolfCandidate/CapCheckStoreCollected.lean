import CommitGolfCandidate.CapCheckGroupStoreFrame
import CommitGolfCandidate.CapCheckCollected
import CommitGolfCandidate.CapMarkPointUpdate

/-! First-occurrence storage establishes the collected-map point update.
The stored digest is the reconstructed scratch digest, and all other
occupied cap leaves/marks retain their original values. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capWordCopyPrefix readBuffer

private theorem natural_distinct (left right : Nat) (leftSmall : left < 2^64)
    (rightSmall : right < 2^64) (different : left ≠ right) :
    BitVec.ofNat 64 left ≠ BitVec.ofNat 64 right := by
  intro equal
  have value := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt leftSmall,Nat.mod_eq_of_lt rightSmall] at value
  exact different value

theorem cap_check_store_collected (state : MachineState) (roots : CapRootMap)
    (ready : CapCheckCollected state roots) (group : Nat) (bounded : group < 128)
    (scratch : state.getReg .x21 = 256)
    (rootPointer : state.getReg .x23 = BitVec.ofNat 64 (capCheckRootAddress group))
    (markPointer : state.getReg .x30 = capMarkAddress (128+group))
    (one : state.getReg .x31 = 1) :
    CapCheckCollected (capCheckGroupStoreState state)
      (fun index => if index=group then some (readBuffer state 256 32) else roots index) := by
  let copied := capWordCopyPrefix .x21 .x23 0 0 state 8
  have markMemory : (capCheckGroupStoreState state).mem =
      (copied.setMem (capMarkAddress (128+group)) 1).mem := by
    rw [cap_check_group_store_memory,markPointer,one]
  have markBefore (other : Nat) (otherBound : other < 128) :
      copied.getMem (capMarkAddress (128+other)) =
        state.getMem (capMarkAddress (128+other)) := by
    apply cap_word_copy_memory_outside .x21 .x23 state (by decide) (by decide)
    intro word
    rw [rootPointer,← BitVec.ofNat_add]
    apply natural_distinct _ _ (by omega)
      (by unfold capCheckRootAddress; have inside:=word.isLt; omega)
    unfold capCheckRootAddress
    have inside := word.isLt
    omega
  constructor
  · intro other otherBound
    have result := cap_mark_point_update state copied (capCheckGroupStoreState state)
      (128+group) (128+other) (by omega) (by omega) markMemory (markBefore other otherBound)
    by_cases same : other=group
    · subst other
      simpa only [if_pos rfl,Option.isSome_some,↓reduceIte] using result
    · have different : 128+other ≠ 128+group := by omega
      rw [if_neg different,ready.marks other otherBound] at result
      simpa only [if_neg same] using result
  · intro other otherBound value known
    by_cases same : other=group
    · subst other
      simp only [ite_true,Option.some.injEq] at known
      rw [← known]
      apply cap_check_group_store_digest state scratch _ rootPointer
        (by unfold capCheckRootAddress; omega)
        (by unfold capCheckRootAddress; omega)
        (by unfold capCheckRootAddress; omega)
      rw [markPointer]
      change 20480 ≤ (BitVec.ofNat 64 (20480+8*(128+group))).toNat
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [if_neg same] at known
      apply (read_digest_congr _ state (capCheckRootAddress other)
        (by unfold capCheckRootAddress; omega) _).trans (ready.roots other otherBound value known)
      intro word inside
      apply cap_check_group_store_outside
      · rw [markPointer]
        apply natural_distinct _ _ (by unfold capCheckRootAddress; omega) (by omega)
        unfold capCheckRootAddress
        omega
      · intro target
        rw [rootPointer,← BitVec.ofNat_add]
        apply natural_distinct _ _
          (by unfold capCheckRootAddress; omega)
          (by unfold capCheckRootAddress; have targetBound:=target.isLt; omega)
        unfold capCheckRootAddress
        have targetBound := target.isLt
        omega

end CommitGolfCandidate
