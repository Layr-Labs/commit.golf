import CommitGolfCandidate.UnrolledShift

/-! The unrolled salt copy reads the nonce of leaf `slot` through a fixed salt
base and the immediate offsets 24*slot, 24*slot+8 and 24*slot+16. On the shifted
frame these are exactly the reference loads. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def unrolledSaltInstructions (slot : Nat) : List Instr :=
  [.LD .x6 .x18 (BitVec.ofNat 12 (24*slot)), .SD .x10 .x6 0,
   .LD .x6 .x18 (BitVec.ofNat 12 (24*slot+8)), .SD .x10 .x6 8,
   .LD .x6 .x18 (BitVec.ofNat 12 (24*slot+16)), .SD .x10 .x6 16, .SD .x10 .x0 24]

def UnrolledSaltFetched (image : Image) (slot : Nat) (start : Word) : Prop :=
  ∀ (state : MachineState) (i : Nat), i < 7 → state.pc = start + BitVec.ofNat 64 (4 * i) →
    fetch image state = some (.base (((unrolledSaltInstructions slot)[i]?).getD .EBREAK))

theorem unrolled_load_address (slot : Nat) (state : MachineState) (offset : Nat)
    (small : 24 * slot + offset < 2048) :
    (unrolledShift slot state).getReg .x18 + signExtend12 (BitVec.ofNat 12 (24 * slot + offset)) =
      state.getReg .x18 + signExtend12 (BitVec.ofNat 12 offset) := by
  rw [unrolled_shift_salt, unrolled_sign_extend _ small, unrolled_sign_extend _ (by omega),
    BitVec.ofNat_add]
  generalize state.getReg .x18 = base
  generalize BitVec.ofNat 64 (24 * slot) = shift
  generalize BitVec.ofNat 64 offset = rest
  rw [← BitVec.add_assoc, BitVec.sub_add_cancel]


theorem unrolled_load_step (slot : Nat) (state : MachineState) (new old : BitVec 12) (offset : Nat)
    (small : 24 * slot + offset < 2048) (newEq : new = BitVec.ofNat 12 (24 * slot + offset))
    (oldEq : old = BitVec.ofNat 12 offset) :
    execInstrBr (unrolledShift slot state) (.LD .x6 .x18 new) =
      unrolledShift slot (execInstrBr state (.LD .x6 .x18 old)) := by
  subst newEq oldEq
  simp only [execInstrBr]
  rw [unrolled_load_address slot state offset small, unrolled_shift_set_pc,
    unrolled_shift_set_reg slot _ .x6 _ (by decide) (by decide)]
  rfl

theorem unrolled_load_valid (slot : Nat) (state : MachineState) (new old : BitVec 12) (offset : Nat)
    (small : 24 * slot + offset < 2048) (newEq : new = BitVec.ofNat 12 (24 * slot + offset))
    (oldEq : old = BitVec.ofNat 12 offset) :
    memoryArgumentsValid (unrolledShift slot state) (.LD .x6 .x18 new) =
      memoryArgumentsValid state (.LD .x6 .x18 old) := by
  subst newEq oldEq
  simp only [memoryArgumentsValid, memAccess]
  rw [unrolled_load_address slot state offset small]

theorem unrolled_store_step (slot : Nat) (state : MachineState) (source : Reg) (offset : BitVec 12)
    (not18 : source ≠ .x18) (not23 : source ≠ .x23) :
    execInstrBr (unrolledShift slot state) (.SD .x10 source offset) =
      unrolledShift slot (execInstrBr state (.SD .x10 source offset)) := by
  simp only [execInstrBr]
  rw [unrolled_shift_register slot state .x10 (by decide) (by decide),
    unrolled_shift_register slot state source not18 not23, unrolled_shift_set_pc,
    unrolled_shift_set_mem]
  rfl

theorem unrolled_store_valid (slot : Nat) (state : MachineState) (source : Reg) (offset : BitVec 12) :
    memoryArgumentsValid (unrolledShift slot state) (.SD .x10 source offset) =
      memoryArgumentsValid state (.SD .x10 source offset) := by
  simp only [memoryArgumentsValid, memAccess]
  rw [unrolled_shift_register slot state .x10 (by decide) (by decide)]

theorem unrolled_ordinary_shift (slot : Nat) (state : MachineState) (new old : Instr)
    (oldValid : memoryArgumentsValid state old = true)
    (sameValid : memoryArgumentsValid (unrolledShift slot state) new = memoryArgumentsValid state old)
    (sameStep : execInstrBr (unrolledShift slot state) new = unrolledShift slot (execInstrBr state old))
    (ordinaryNew : ordinaryStep (unrolledShift slot state) (.base new) =
      if memoryArgumentsValid (unrolledShift slot state) new
      then some (execInstrBr (unrolledShift slot state) new) else none) :
    ordinaryStep (unrolledShift slot state) (.base new) = some (unrolledShift slot (execInstrBr state old)) := by
  rw [ordinaryNew, sameValid, oldValid, if_pos rfl, sameStep]

theorem unrolled_salt_prefix_pc (state : MachineState) (i : Nat) (bounded : i ≤ 7) :
    (nonceSaltPrefix state i).pc = state.pc + BitVec.ofNat 64 (4 * i) := by
  interval_cases i <;>
    simp [nonceSaltPrefix, nonceSaltInstructions, execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem unrolled_nonce_prefix_succ (state : MachineState) (i : Nat) (hi : i < 7) :
    nonceSaltPrefix state (i + 1) =
      execInstrBr (nonceSaltPrefix state i) ((nonceSaltInstructions[i]?).getD .EBREAK) := by
  interval_cases i <;>
    simp only [nonceSaltPrefix, nonceSaltInstructions, List.take, List.foldl,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]

/-- Seven ordinary instructions copy the reference salt from the shifted frame. -/
theorem unrolled_salt_execute (image : Image) (slot : Nat) (small : slot < 64) (start : Word)
    (fetched : UnrolledSaltFetched image slot start)
    (state : MachineState) (pc : state.pc = start)
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute image (7 + fuel) (unrolledShift slot state) true =
      (do let result ← execute image fuel (unrolledShift slot (nonceSaltState state)) true
          return result.charge 7 0) := by
  change execute image (7 + fuel) (unrolledShift slot state) true =
    (do let result ← execute image fuel (unrolledShift slot (nonceSaltPrefix state 7)) true
        return result.charge 7 0)
  have initial : unrolledShift slot state = unrolledShift slot (nonceSaltPrefix state 0) := rfl
  rw [initial]
  apply execute_unit_steps (states := fun i => unrolledShift slot (nonceSaltPrefix state i))
  intro i hi
  refine ⟨.base (((unrolledSaltInstructions slot)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched _ i hi
    rw [unrolled_shift_pc, unrolled_salt_prefix_pc state i (by omega), pc]
  · have source := nonce_salt_prefix_register state i (by omega) .x18 (by decide)
    have destination := nonce_salt_prefix_register state i (by omega) .x10 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (nonceSaltPrefix state i)
        ((nonceSaltInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [nonceSaltInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
          memAccess, source, destination, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 |
          exact d0 | exact d1 | exact d2 | exact d3
    rw [unrolled_nonce_prefix_succ state i hi]
    generalize nonceSaltPrefix state i = current at valid ⊢
    interval_cases i <;>
      simp only [unrolledSaltInstructions, nonceSaltInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢
    · exact unrolled_ordinary_shift slot _ _ _ valid
        (unrolled_load_valid slot _ _ _ 0 (by omega) (by simp) rfl)
        (unrolled_load_step slot _ _ _ 0 (by omega) (by simp) rfl) rfl
    · exact unrolled_ordinary_shift slot _ _ _ valid
        (unrolled_store_valid slot _ _ _) (unrolled_store_step slot _ _ _ (by decide) (by decide)) rfl
    · exact unrolled_ordinary_shift slot _ _ _ valid
        (unrolled_load_valid slot _ _ _ 8 (by omega) rfl rfl)
        (unrolled_load_step slot _ _ _ 8 (by omega) rfl rfl) rfl
    · exact unrolled_ordinary_shift slot _ _ _ valid
        (unrolled_store_valid slot _ _ _) (unrolled_store_step slot _ _ _ (by decide) (by decide)) rfl
    · exact unrolled_ordinary_shift slot _ _ _ valid
        (unrolled_load_valid slot _ _ _ 16 (by omega) rfl rfl)
        (unrolled_load_step slot _ _ _ 16 (by omega) rfl rfl) rfl
    · exact unrolled_ordinary_shift slot _ _ _ valid
        (unrolled_store_valid slot _ _ _) (unrolled_store_step slot _ _ _ (by decide) (by decide)) rfl
    · exact unrolled_ordinary_shift slot _ _ _ valid
        (unrolled_store_valid slot _ _ _) (unrolled_store_step slot _ _ _ (by decide) (by decide)) rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
