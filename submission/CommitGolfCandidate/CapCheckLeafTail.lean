import CommitGolfCandidate.CapCheckCompression

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckLeafTailInstructions : List Instr :=
  [.ADDI .x8 .x8 32, .ADDI .x28 .x28 4095, .BNE .x28 .x0 8128]

def capCheckLeafTailPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckLeafTailInstructions.take count).foldl execInstrBr state

def CapCheckLeafTailFetched (image : Image) (entry : Word) : Prop :=
  ∀ state : MachineState, ∀ i < 3, state.pc = entry →
    fetch image (capCheckLeafTailPrefix state i) =
      some (.base ((capCheckLeafTailInstructions[i]?).getD .EBREAK))

theorem cap_check_leaf_tail_succ (state : MachineState) (count : Nat)
    (bounded : count < 3) :
    capCheckLeafTailPrefix state (count + 1) =
      execInstrBr (capCheckLeafTailPrefix state count)
        ((capCheckLeafTailInstructions[count]?).getD .EBREAK) := by
  have inside : count < capCheckLeafTailInstructions.length := by
    simpa only [capCheckLeafTailInstructions, List.length_cons, List.length_nil] using bounded
  unfold capCheckLeafTailPrefix
  rw [List.take_succ_eq_append_getElem inside, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil,
    getElem?_pos capCheckLeafTailInstructions count inside, Option.getD_some]

theorem cap_check_leaf_tail_prefix_pc (state : MachineState) (count : Nat)
    (bounded : count < 3) :
    (capCheckLeafTailPrefix state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capCheckLeafTailPrefix, capCheckLeafTailInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_leaf_tail_execute (image : Image) (entry : Word)
    (fetched : CapCheckLeafTailFetched image entry)
    (state : MachineState) (pc : state.pc = entry) (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let result ← execute image fuel (capCheckLeafTailPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := capCheckLeafTailPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckLeafTailInstructions[i]?).getD .EBREAK),
    fetched state i bounded pc, ?_, ?_⟩
  · rw [cap_check_leaf_tail_succ state i bounded]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem tail_branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x28 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem tail_branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x28 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

attribute [local irreducible] capCheckLeafTailPrefix

theorem cap_check_leaf_tail_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x8 ∧ reg ≠ .x28) :
    (capCheckLeafTailPrefix state 3).getReg reg = state.getReg reg := by
  rw [cap_check_leaf_tail_succ state 2 (by decide)]
  change (execInstrBr (capCheckLeafTailPrefix state 2) (.BNE .x28 .x0 8128)).getReg reg = _
  rw [tail_branch_register]
  simp only [capCheckLeafTailPrefix, capCheckLeafTailInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2)]

theorem cap_check_leaf_tail_pointers (state : MachineState) :
    (capCheckLeafTailPrefix state 3).getReg .x8 = state.getReg .x8 + 32 ∧
    (capCheckLeafTailPrefix state 3).getReg .x28 = state.getReg .x28 - 1 := by
  have last (reg : Reg) : (capCheckLeafTailPrefix state 3).getReg reg =
      (capCheckLeafTailPrefix state 2).getReg reg := by
    rw [cap_check_leaf_tail_succ state 2 (by decide)]
    exact tail_branch_register _ _ reg
  rw [last .x8, last .x28]
  simp (disch := decide) only [capCheckLeafTailPrefix, capCheckLeafTailInstructions,
    List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  constructor
  · rfl
  · rw [BitVec.sub_eq_add_neg]
    rfl

theorem cap_check_leaf_tail_memory (state : MachineState) :
    (capCheckLeafTailPrefix state 3).mem = state.mem := by
  rw [cap_check_leaf_tail_succ state 2 (by decide)]
  change (execInstrBr (capCheckLeafTailPrefix state 2) (.BNE .x28 .x0 8128)).mem = _
  rw [tail_branch_memory]
  simp only [capCheckLeafTailPrefix, capCheckLeafTailInstructions, List.take, List.foldl,
    execInstrBr, MachineState.setReg, MachineState.setPC]

theorem cap_check_leaf_tail_pc (state : MachineState) :
    (capCheckLeafTailPrefix state 3).pc =
      if state.getReg .x28 - 1 = 0 then state.pc + 12 else state.pc - 56 := by
  have counter : (capCheckLeafTailPrefix state 2).getReg .x28 = state.getReg .x28 - 1 := by
    simp (disch := decide) only [capCheckLeafTailPrefix, capCheckLeafTailInstructions,
      List.take, List.foldl, execInstrBr, signExtend12,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    rw [BitVec.sub_eq_add_neg]
    rfl
  have pc := cap_check_leaf_tail_prefix_pc state 2 (by decide)
  change (capCheckLeafTailPrefix state 2).pc = state.pc + 8 at pc
  rw [cap_check_leaf_tail_succ state 2 (by decide)]
  change (execInstrBr (capCheckLeafTailPrefix state 2) (.BNE .x28 .x0 8128)).pc = _
  simp only [execInstrBr, counter, pc,
    show (capCheckLeafTailPrefix state 2).getReg .x0 = 0 from rfl]
  by_cases zero : state.getReg .x28 - 1 = 0
  · rw [zero]
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false,
      MachineState.setPC, ite_true]
    change state.pc + 8 + 4 = state.pc + 12
    ring
  · rw [ite_eq_left (bne_iff_ne.mpr zero), if_neg zero]
    simp only [MachineState.setPC,
      show signExtend13 (8128 : BitVec 13) = (-64 : Word) by decide]
    change state.pc + 8 + (-64) = state.pc - 56
    ring

end CommitGolfCandidate
