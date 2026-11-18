import CommitGolfCandidate.CapCheckGroupStore
import CommitGolfCandidate.CapWordCopyMemory

/-! The stored root and occupancy update are separate memory effects.
The mark store must exclude every word of the copied root. All other words
are preserved unless they belong to that root or its occupancy entry. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capWordCopyPrefix

theorem cap_check_group_store_pc (state : MachineState) (pc : state.pc = 4500) :
    (capCheckGroupStoreState state).pc = 4536 := by
  unfold capCheckGroupStoreState
  change (capWordCopyPrefix .x21 .x23 0 0 state 8).pc+4 = _
  rw [cap_word_copy_prefix_pc _ _ _ _ _ 8 (by decide), pc]
  rfl

theorem cap_check_group_store_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6) :
    (capCheckGroupStoreState state).getReg reg = state.getReg reg := by
  unfold capCheckGroupStoreState
  change ((capWordCopyPrefix .x21 .x23 0 0 state 8).setMem
    ((capWordCopyPrefix .x21 .x23 0 0 state 8).getReg .x30 + signExtend12 0)
    ((capWordCopyPrefix .x21 .x23 0 0 state 8).getReg .x31)).getReg reg = _
  have same (current : MachineState) (address value : Word) :
      (current.setMem address value).getReg reg = current.getReg reg := by
    cases reg <;> rfl
  rw [same]
  exact cap_word_copy_prefix_register .x21 .x23 0 0 state 8 (by decide) reg outside

theorem cap_check_group_store_memory (state : MachineState) :
    (capCheckGroupStoreState state).mem =
      ((capWordCopyPrefix .x21 .x23 0 0 state 8).setMem
        (state.getReg .x30) (state.getReg .x31)).mem := by
  unfold capCheckGroupStoreState
  change ((capWordCopyPrefix .x21 .x23 0 0 state 8).setMem
    ((capWordCopyPrefix .x21 .x23 0 0 state 8).getReg .x30 + signExtend12 0)
    ((capWordCopyPrefix .x21 .x23 0 0 state 8).getReg .x31)).mem = _
  rw [cap_word_copy_prefix_register .x21 .x23 0 0 state 8 (by decide) .x30 (by decide),
    cap_word_copy_prefix_register .x21 .x23 0 0 state 8 (by decide) .x31 (by decide)]
  change ((capWordCopyPrefix .x21 .x23 0 0 state 8).setMem
    (state.getReg .x30+(0#64)) (state.getReg .x31)).mem = _
  rw [BitVec.add_zero]

theorem cap_check_group_store_outside (state : MachineState) (address : Word)
    (markOutside : address ≠ state.getReg .x30)
    (rootOutside : ∀ word : Fin 4,
      address ≠ state.getReg .x23+BitVec.ofNat 64 (8*word.val)) :
    (capCheckGroupStoreState state).getMem address = state.getMem address := by
  have memory := congrFun (cap_check_group_store_memory state) address
  change (capCheckGroupStoreState state).getMem address =
    ((capWordCopyPrefix .x21 .x23 0 0 state 8).setMem
      (state.getReg .x30) (state.getReg .x31)).getMem address at memory
  rw [memory, MachineState.getMem_setMem_ne markOutside]
  exact cap_word_copy_memory_outside .x21 .x23 state (by decide) (by decide)
    address rootOutside

theorem cap_check_group_store_mark (state : MachineState) :
    (capCheckGroupStoreState state).getMem (state.getReg .x30) =
      state.getReg .x31 := by
  have memory := congrFun (cap_check_group_store_memory state) (state.getReg .x30)
  exact memory.trans (MachineState.getMem_setMem_eq)

theorem cap_check_group_store_root_word (state : MachineState)
    (separated : ∀ i j : Fin 4,
      state.getReg .x21+BitVec.ofNat 64 (8*i.val) ≠
        state.getReg .x23+BitVec.ofNat 64 (8*j.val))
    (markSeparate : ∀ word : Fin 4,
      state.getReg .x23+BitVec.ofNat 64 (8*word.val) ≠ state.getReg .x30)
    (word : Fin 4) :
    (capCheckGroupStoreState state).getMem
      (state.getReg .x23+BitVec.ofNat 64 (8*word.val)) =
      state.getMem (state.getReg .x21+BitVec.ofNat 64 (8*word.val)) := by
  have memory := congrFun (cap_check_group_store_memory state)
    (state.getReg .x23+BitVec.ofNat 64 (8*word.val))
  change (capCheckGroupStoreState state).getMem
    (state.getReg .x23+BitVec.ofNat 64 (8*word.val)) =
    ((capWordCopyPrefix .x21 .x23 0 0 state 8).setMem
      (state.getReg .x30) (state.getReg .x31)).getMem
      (state.getReg .x23+BitVec.ofNat 64 (8*word.val)) at memory
  rw [memory, MachineState.getMem_setMem_ne (markSeparate word)]
  exact cap_word_copy_memory .x21 .x23 state (by decide) (by decide) separated word

theorem cap_check_group_store_digest (state : MachineState)
    (scratch : state.getReg .x21 = 256) (root : Nat)
    (rootPointer : state.getReg .x23 = BitVec.ofNat 64 root)
    (aligned : root % 8 = 0) (bounded : root+32 ≤ 28672)
    (aboveScratch : 320 ≤ root)
    (mark : 28672 ≤ (state.getReg .x30).toNat) :
    readBuffer (capCheckGroupStoreState state) root 32 = readBuffer state 256 32 := by
  apply (read_digest_eq_iff _ _ _ _ aligned (by decide)).mpr
  intro word inside
  have scratchNat : state.getReg .x21 = BitVec.ofNat 64 256 := scratch
  have copied := cap_check_group_store_root_word state (by
      intro i j
      rw [scratchNat, rootPointer, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      exact separate_digest_words 256 root i.val j.val
        (by decide) (by omega) i.isLt j.isLt (Or.inl (by omega)))
    (by
      intro i equal
      have value := congrArg BitVec.toNat equal
      rw [rootPointer, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)] at value
      omega) ⟨word,inside⟩
  simpa only [scratchNat, rootPointer, ← BitVec.ofNat_add] using copied

end CommitGolfCandidate
