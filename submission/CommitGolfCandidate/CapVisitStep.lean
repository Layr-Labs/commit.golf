import CommitGolfCandidate.CapMarkImage

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem zero_offset (address : Word) :
    address + signExtend12 (0 : BitVec 12) = address := by
  simp [signExtend12]

def capVisitInstructions (marks : Reg) : List Instr :=
  [.SLLI .x7 .x20 3, .ADD .x23 marks .x7, .LD .x6 .x23 0]

def capVisitPrefix (marks : Reg) (state : MachineState) (count : Nat) : MachineState :=
  ((capVisitInstructions marks).take count).foldl execInstrBr state

def CapVisitFetched (image : Image) (marks : Reg) (entry : Word) : Prop :=
  ∀ state : MachineState, ∀ i < 3, state.pc = entry →
    fetch image (capVisitPrefix marks state i) =
      some (.base (((capVisitInstructions marks)[i]?).getD .EBREAK))

theorem cap_visit_prefix_succ (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count < 3) :
    capVisitPrefix marks state (count + 1) =
      execInstrBr (capVisitPrefix marks state count)
        (((capVisitInstructions marks)[count]?).getD .EBREAK) := by
  interval_cases count <;> rfl

theorem cap_visit_prefix_pc (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) :
    (capVisitPrefix marks state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capVisitPrefix, capVisitInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  · rfl
  · rfl
  · rfl

theorem cap_visit_prefix_memory (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) :
    (capVisitPrefix marks state count).mem = state.mem := by
  interval_cases count <;> rfl

theorem cap_visit_prefix_register (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23) :
    (capVisitPrefix marks state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capVisitPrefix, capVisitInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem cap_visit_address (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capVisitPrefix marks state 2).getReg .x23 = capMarkAddress node := by
  rcases selected with rfl | rfl <;>
    simp (disch := decide) only [capVisitPrefix, capVisitInstructions, List.take,
      List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      base, index, show (3 : BitVec 6).toNat = 3 by decide] <;>
    exact cap_mark_parent_pointer node

theorem cap_visit_mark (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capVisitPrefix marks state 3).getReg .x6 = state.getMem (capMarkAddress node) := by
  rw [cap_visit_prefix_succ marks state 2 (by decide)]
  simp (disch := decide) only [capVisitInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, zero_offset]
  rw [cap_visit_address marks state node selected base index]
  exact congrFun (cap_visit_prefix_memory marks state 2 (by decide)) _

theorem cap_visit_execute (image : Image) (marks : Reg) (entry : Word)
    (fetched : CapVisitFetched image marks entry)
    (state : MachineState) (pc : state.pc = entry)
    (valid : accessValid ((capVisitPrefix marks state 2).getReg .x23) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let result ← execute image fuel (capVisitPrefix marks state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := capVisitPrefix marks state)
  intro i bounded
  refine ⟨.base (((capVisitInstructions marks)[i]?).getD .EBREAK),
    fetched state i bounded pc, ?_, ?_⟩
  · have access : memoryArgumentsValid (capVisitPrefix marks state i)
        (((capVisitInstructions marks)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [capVisitInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess]
      simpa only [zero_offset] using valid
    rw [cap_visit_prefix_succ marks state i bounded]
    interval_cases i <;>
      simp only [capVisitInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at access ⊢ <;>
      simp only [ordinaryStep, access, ↓reduceIte]
  · interval_cases i <;> rfl

theorem cap_visit_mark_ready (marks : Reg) (state : MachineState) (node : Nat)
    (marked : Nat → Bool) (selected : CapMarksRegister marks)
    (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 512)
    (ready : CapMarksReady state 256 0 marked) :
    (capVisitPrefix marks state 3).getReg .x6 = capMarkWord (marked node) :=
  (cap_visit_mark marks state node selected base index).trans
    (ready node positive bounded)

theorem cap_visit_load_valid (marks : Reg) (state : MachineState) (node : Nat)
    (selected : CapMarksRegister marks) (base : state.getReg marks = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    accessValid ((capVisitPrefix marks state 2).getReg .x23) 8 = true := by
  rw [cap_visit_address marks state node selected base index]
  exact (cap_mark_address_valid 256 node (by decide) bounded).1

def capVisitBranchState (offset : BitVec 13) (state : MachineState) : MachineState :=
  execInstrBr state (.BEQ .x6 .x0 offset)

theorem cap_visit_branch_execute (image : Image) (offset : BitVec 13)
    (state : MachineState)
    (fetched : fetch image state = some (.base (.BEQ .x6 .x0 offset)))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1 + fuel) state allowCoins =
      (do let result ← execute image fuel (capVisitBranchState offset state) allowCoins
          return result.charge 1 0) := by
  have step : ordinaryStep state (.base (.BEQ .x6 .x0 offset)) =
      some (capVisitBranchState offset state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true,
      capVisitBranchState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

theorem cap_visit_branch_pc (state : MachineState) (offset : BitVec 13)
    (marked : Bool) (mark : state.getReg .x6 = capMarkWord marked) :
    (capVisitBranchState offset state).pc =
      if marked then state.pc + 4 else state.pc + signExtend13 offset := by
  have zero : state.getReg .x0 = 0 := rfl
  cases marked <;>
    simp [capVisitBranchState, execInstrBr, mark, zero, capMarkWord, MachineState.setPC]

theorem cap_visit_branch_register (state : MachineState) (offset : BitVec 13)
    (reg : Reg) :
    (capVisitBranchState offset state).getReg reg = state.getReg reg := by
  simp only [capVisitBranchState, execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem cap_visit_branch_memory (state : MachineState) (offset : BitVec 13) :
    (capVisitBranchState offset state).mem = state.mem := by
  simp only [capVisitBranchState, execInstrBr]
  split <;> rfl

theorem cap_open_visit_fetched :
    CapVisitFetched ((capExperimental 24).image .opening) .x22 4420 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capVisitPrefix .x22 state i) (81 + i) _ (by omega)
  · rw [cap_visit_prefix_pc .x22 state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_visit_fetched :
    CapVisitFetched ((capExperimental 24).image .check) .x9 4604 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capVisitPrefix .x9 state i) (127 + i) _ (by omega)
  · rw [cap_visit_prefix_pc .x9 state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_open_visit_branch_fetched (state : MachineState) (pc : state.pc = 4432) :
    fetch ((capExperimental 24).image .opening) state =
      some (.base (.BEQ .x6 .x0 20)) := by
  apply cap_image_fetch _ state 84 _ (by decide) pc
  rfl

theorem cap_check_visit_branch_fetched (state : MachineState) (pc : state.pc = 4616) :
    fetch ((capExperimental 24).image .check) state =
      some (.base (.BEQ .x6 .x0 20)) := by
  apply cap_image_fetch _ state 130 _ (by decide) pc
  rfl

end CommitGolfCandidate
