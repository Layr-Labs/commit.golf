import CommitGolfCandidate.CapCheckCompression

/-! The seven lower-path latch instructions: a call into the truncation code,
which clears bytes 30 and 31 of the scratch reply and advances the proof cursor,
the return, then the node shift and the decrement of the sibling counter.
Fetch and cycle accounting refer to the experimental checker. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckPathTailInstructions : List Instr :=
  [.JAL .x1 1452, .SH .x21 .x0 30, .ADDI .x25 .x25 32, .JALR .x0 .x1 0,
   .SRLI .x20 .x20 1, .ADDI .x29 .x29 4095, .BNE .x29 .x0 8048]

def capCheckPathTailPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckPathTailInstructions.take count).foldl execInstrBr state

/-- Word positions of the seven latch instructions: the call at word 77, the
truncation code at words 440..442, the remaining latch at words 78..80. -/
def capCheckPathTailWord : Nat → Nat
  | 0 => 77
  | 1 => 440
  | 2 => 441
  | 3 => 442
  | 4 => 78
  | 5 => 79
  | _ => 80

/-- The latch starts at PC 4404 (word 77). -/
def CapCheckPathTailFetched (image : Image) : Prop :=
  ∀ state : MachineState, ∀ i < 7, state.pc = 4404 →
    fetch image (capCheckPathTailPrefix state i) =
      some (.base ((capCheckPathTailInstructions[i]?).getD .EBREAK))

theorem cap_check_path_tail_succ (state : MachineState) (count : Nat)
    (bounded : count < 7) :
    capCheckPathTailPrefix state (count + 1) =
      execInstrBr (capCheckPathTailPrefix state count)
        ((capCheckPathTailInstructions[count]?).getD .EBREAK) := by
  have inside : count < capCheckPathTailInstructions.length := by
    simpa only [capCheckPathTailInstructions, List.length_cons, List.length_nil] using bounded
  unfold capCheckPathTailPrefix
  rw [List.take_succ_eq_append_getElem inside, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil,
    getElem?_pos capCheckPathTailInstructions count inside, Option.getD_some]

private theorem half_register (state : MachineState) (address : Word) (half : BitVec 16)
    (reg : Reg) : (state.setHalfword address half).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem set_zero_register (state : MachineState) (value : Word) :
    state.setReg .x0 value = state := rfl

private theorem pc_set_pc (state : MachineState) (value : Word) :
    (state.setPC value).pc = value := rfl

private theorem pc_set_reg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).pc = state.pc := by
  cases reg <;> rfl

private theorem pc_set_half (state : MachineState) (address : Word) (half : BitVec 16) :
    (state.setHalfword address half).pc = state.pc := rfl

private theorem mem_set_pc (state : MachineState) (value : Word) :
    (state.setPC value).mem = state.mem := rfl

private theorem mem_set_reg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by
  cases reg <;> rfl

private theorem half_congr (left right : MachineState) (same : left.mem = right.mem)
    (address : Word) (half : BitVec 16) :
    (left.setHalfword address half).mem = (right.setHalfword address half).mem := by
  simp only [MachineState.setHalfword, MachineState.setMem, MachineState.getMem, same]

theorem cap_check_path_tail_prefix_pc (state : MachineState) (count : Nat)
    (bounded : count < 7) (pc : state.pc = 4404) :
    (capCheckPathTailPrefix state count).pc =
      BitVec.ofNat 64 (4096 + 4 * capCheckPathTailWord count) := by
  interval_cases count <;>
    simp (disch := decide) only [capCheckPathTailPrefix, capCheckPathTailInstructions, List.take,
      List.foldl, execInstrBr, pc_set_pc, MachineState.getReg_setPC,
      half_register, set_zero_register, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, pc, capCheckPathTailWord]
  all_goals rfl

theorem cap_check_path_tail_execute (image : Image)
    (fetched : CapCheckPathTailFetched image)
    (state : MachineState) (pc : state.pc = 4404) (scratch : state.getReg .x21 = 256)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (7 + fuel) state allowCoins =
      (do let result ← execute image fuel (capCheckPathTailPrefix state 7) allowCoins
          return result.charge 7 0) := by
  have halfScratch : (capCheckPathTailPrefix state 1).getReg .x21 = 256 := by
    rw [← scratch]
    rfl
  apply execute_unit_steps (states := capCheckPathTailPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckPathTailInstructions[i]?).getD .EBREAK),
    fetched state i bounded pc, ?_, ?_⟩
  · rw [cap_check_path_tail_succ state i bounded]
    interval_cases i
    · rfl
    · simp only [ordinaryStep, memoryArgumentsValid, memAccess, capCheckPathTailInstructions,
        List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, halfScratch]
      rfl
    all_goals rfl
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

/-- The registers the latch leaves alone. -/
theorem cap_check_path_tail_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x29 ∧ reg ≠ .x1) :
    (capCheckPathTailPrefix state 7).getReg reg = state.getReg reg := by
  rw [cap_check_path_tail_succ state 6 (by decide)]
  change (execInstrBr (capCheckPathTailPrefix state 6) (.BNE .x29 .x0 8048)).getReg reg = _
  rw [tail_branch_register]
  simp only [capCheckPathTailPrefix, capCheckPathTailInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC, half_register,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2), set_zero_register]

theorem cap_check_path_tail_pointers (state : MachineState) :
    (capCheckPathTailPrefix state 7).getReg .x25 = state.getReg .x25 + 32 ∧
    (capCheckPathTailPrefix state 7).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (capCheckPathTailPrefix state 7).getReg .x29 = state.getReg .x29 - 1 := by
  have last (reg : Reg) : (capCheckPathTailPrefix state 7).getReg reg =
      (capCheckPathTailPrefix state 6).getReg reg := by
    rw [cap_check_path_tail_succ state 6 (by decide)]
    exact tail_branch_register _ _ reg
  have small : signExtend12 (32 : BitVec 12) = (32 : Word) := by decide
  have minus : signExtend12 (4095 : BitVec 12) = (-1 : Word) := by decide
  refine ⟨?_, ?_, ?_⟩ <;> rw [last] <;>
    simp (disch := decide) only [capCheckPathTailPrefix, capCheckPathTailInstructions,
      List.take, List.foldl, execInstrBr, small, minus, half_register, set_zero_register,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      show (1 : BitVec 6).toNat = 1 by decide, BitVec.sub_eq_add_neg]

/-- The latch writes only the two cleared bytes, in the scratch word at 280. -/
theorem cap_check_path_tail_memory (state : MachineState) :
    (capCheckPathTailPrefix state 7).mem =
      (state.setHalfword (state.getReg .x21 + 30) 0).mem := by
  rw [cap_check_path_tail_succ state 6 (by decide)]
  change (execInstrBr (capCheckPathTailPrefix state 6) (.BNE .x29 .x0 8048)).mem = _
  rw [tail_branch_memory]
  have scratch : ((state.setReg .x1 (state.pc + 4)).setPC
      (state.pc + signExtend21 1452)).getReg .x21 = state.getReg .x21 := by
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
  simp only [capCheckPathTailPrefix, capCheckPathTailInstructions, List.take, List.foldl,
    execInstrBr, mem_set_pc, mem_set_reg, set_zero_register, scratch,
    show signExtend12 (30 : BitVec 12) = (30 : Word) by decide]
  exact half_congr _ _ (by rw [mem_set_pc, mem_set_reg]) _ _

theorem cap_check_path_tail_pc (state : MachineState) (pc : state.pc = 4404) :
    (capCheckPathTailPrefix state 7).pc =
      if state.getReg .x29 - 1 = 0 then 4420 else 4272 := by
  have counter : (capCheckPathTailPrefix state 6).getReg .x29 = state.getReg .x29 - 1 := by
    simp (disch := decide) only [capCheckPathTailPrefix, capCheckPathTailInstructions,
      List.take, List.foldl, execInstrBr, signExtend12, half_register, set_zero_register,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
    rw [BitVec.sub_eq_add_neg]
    rfl
  have latch := cap_check_path_tail_prefix_pc state 6 (by decide) pc
  change (capCheckPathTailPrefix state 6).pc = 4416 at latch
  rw [cap_check_path_tail_succ state 6 (by decide)]
  change (execInstrBr (capCheckPathTailPrefix state 6) (.BNE .x29 .x0 8048)).pc = _
  simp only [execInstrBr, counter, latch,
    show (capCheckPathTailPrefix state 6).getReg .x0 = 0 from rfl]
  by_cases zero : state.getReg .x29 - 1 = 0
  · rw [zero]
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false,
      MachineState.setPC, ite_true]
    rfl
  · rw [ite_eq_left (bne_iff_ne.mpr zero), ite_eq_right_iff.mpr (fun h => absurd h zero)]
    simp only [MachineState.setPC]
    rfl

end CommitGolfCandidate
