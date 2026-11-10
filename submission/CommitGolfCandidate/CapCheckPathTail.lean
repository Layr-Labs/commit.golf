import CommitGolfCandidate.CapCheckCompression

/-! The four actual lower-path latch instructions advance the proof cursor,
shift the node, and decrement the seventeen-sibling counter. Fetch and cycle
accounting refer to the experimental checker, with natural bounds separate. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckPathTailInstructions : List Instr :=
  [.ADDI .x25 .x25 32, .SRLI .x20 .x20 1, .ADDI .x29 .x29 4095, .BNE .x29 .x0 8048]

def capCheckPathTailPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckPathTailInstructions.take count).foldl execInstrBr state

def CapCheckPathTailFetched (image : Image) (entry : Word) : Prop :=
  ∀ state : MachineState, ∀ i < 4, state.pc = entry →
    fetch image (capCheckPathTailPrefix state i) =
      some (.base ((capCheckPathTailInstructions[i]?).getD .EBREAK))

theorem cap_check_path_tail_succ (state : MachineState) (count : Nat)
    (bounded : count < 4) :
    capCheckPathTailPrefix state (count + 1) =
      execInstrBr (capCheckPathTailPrefix state count)
        ((capCheckPathTailInstructions[count]?).getD .EBREAK) := by
  have inside : count < capCheckPathTailInstructions.length := by
    simpa only [capCheckPathTailInstructions, List.length_cons, List.length_nil] using bounded
  unfold capCheckPathTailPrefix
  rw [List.take_succ_eq_append_getElem inside, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil,
    getElem?_pos capCheckPathTailInstructions count inside, Option.getD_some]

theorem cap_check_path_tail_prefix_pc (state : MachineState) (count : Nat)
    (bounded : count < 4) :
    (capCheckPathTailPrefix state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capCheckPathTailPrefix, capCheckPathTailInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_path_tail_execute (image : Image) (entry : Word)
    (fetched : CapCheckPathTailFetched image entry)
    (state : MachineState) (pc : state.pc = entry) (fuel : Nat) (allowCoins : Bool) :
    execute image (4 + fuel) state allowCoins =
      (do let result ← execute image fuel (capCheckPathTailPrefix state 4) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := capCheckPathTailPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckPathTailInstructions[i]?).getD .EBREAK),
    fetched state i bounded pc, ?_, ?_⟩
  · rw [cap_check_path_tail_succ state i bounded]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem tail_branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x29 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem tail_branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x29 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

attribute [local irreducible] capCheckPathTailPrefix

theorem cap_check_path_tail_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x29) :
    (capCheckPathTailPrefix state 4).getReg reg = state.getReg reg := by
  rw [cap_check_path_tail_succ state 3 (by decide)]
  change (execInstrBr (capCheckPathTailPrefix state 3) (.BNE .x29 .x0 8048)).getReg reg = _
  rw [tail_branch_register]
  simp only [capCheckPathTailPrefix, capCheckPathTailInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem cap_check_path_tail_pointers (state : MachineState) :
    (capCheckPathTailPrefix state 4).getReg .x25 = state.getReg .x25 + 32 ∧
    (capCheckPathTailPrefix state 4).getReg .x29 = state.getReg .x29 - 1 := by
  have last (reg : Reg) : (capCheckPathTailPrefix state 4).getReg reg =
      (capCheckPathTailPrefix state 3).getReg reg := by
    rw [cap_check_path_tail_succ state 3 (by decide)]
    exact tail_branch_register _ _ reg
  rw [last .x25, last .x29]
  simp (disch := decide) only [capCheckPathTailPrefix, capCheckPathTailInstructions,
    List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  constructor
  · rfl
  · rw [BitVec.sub_eq_add_neg]
    rfl

theorem cap_check_path_tail_memory (state : MachineState) :
    (capCheckPathTailPrefix state 4).mem = state.mem := by
  rw [cap_check_path_tail_succ state 3 (by decide)]
  change (execInstrBr (capCheckPathTailPrefix state 3) (.BNE .x29 .x0 8048)).mem = _
  rw [tail_branch_memory]
  simp only [capCheckPathTailPrefix, capCheckPathTailInstructions, List.take, List.foldl,
    execInstrBr, MachineState.setReg, MachineState.setPC]

theorem cap_check_path_tail_pc (state : MachineState) :
    (capCheckPathTailPrefix state 4).pc =
      if state.getReg .x29 - 1 = 0 then state.pc + 16 else state.pc - 132 := by
  have counter : (capCheckPathTailPrefix state 3).getReg .x29 = state.getReg .x29 - 1 := by
    simp (disch := decide) only [capCheckPathTailPrefix, capCheckPathTailInstructions,
      List.take, List.foldl, execInstrBr, signExtend12,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    rw [BitVec.sub_eq_add_neg]
    rfl
  have pc := cap_check_path_tail_prefix_pc state 3 (by decide)
  change (capCheckPathTailPrefix state 3).pc = state.pc + 12 at pc
  rw [cap_check_path_tail_succ state 3 (by decide)]
  change (execInstrBr (capCheckPathTailPrefix state 3) (.BNE .x29 .x0 8048)).pc = _
  simp only [execInstrBr, counter, pc,
    show (capCheckPathTailPrefix state 3).getReg .x0 = 0 from rfl]
  by_cases zero : state.getReg .x29 - 1 = 0
  · rw [zero]
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false,
      MachineState.setPC, ite_true]
    change state.pc + 12 + 4 = state.pc + 16
    ring
  · rw [ite_eq_left (bne_iff_ne.mpr zero), if_neg zero]
    simp only [MachineState.setPC,
      show signExtend13 (8048 : BitVec 13) = (-144 : Word) by decide]
    change state.pc + 12 + (-144) = state.pc - 132
    ring

end CommitGolfCandidate
