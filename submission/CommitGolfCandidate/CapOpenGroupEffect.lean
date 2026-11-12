import CommitGolfCandidate.CapOpenGroupStep

/-! The record-exit memory effect is exactly one occupancy word store. Its
outside-register and retained-input frames permit an outer record induction
without falsely equating the changed marks with their original zero values. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x27 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x27 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem store_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem add_zero_word (word : Word) : word + (0 : Word) = word :=
  BitVec.add_zero word

private theorem suffix_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr (execInstrBr (execInstrBr (execInstrBr state (.SD .x23 .x31 0))
      (.ADDI .x24 .x24 8)) (.ADDI .x27 .x27 4095)) (.BNE .x27 .x0 offset)).mem =
        (state.setMem (state.getReg .x23) (state.getReg .x31)).mem := by
  rw [branch_memory]
  simp only [execInstrBr, MachineState.setPC, MachineState.setReg,
    show signExtend12 (0 : BitVec 12) = (0 : Word) by decide, add_zero_word]

theorem cap_open_group_memory (state : MachineState) (node : Nat)
    (marks : state.getReg .x22 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capOpenGroupPrefix state 6).mem =
      (state.setMem (BitVec.ofNat 64 (28672+8*node)) (state.getReg .x31)).mem := by
  have source : (capOpenGroupPrefix state 2).getReg .x31 = state.getReg .x31 := by
    simp (disch := decide) only [capOpenGroupPrefix, capOpenGroupInstructions,
      List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne]
  have before : (capOpenGroupPrefix state 2).mem = state.mem := by rfl
  rw [cap_open_group_succ state 5 (by decide), cap_open_group_succ state 4 (by decide),
    cap_open_group_succ state 3 (by decide), cap_open_group_succ state 2 (by decide)]
  simp only [capOpenGroupInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some]
  rw [suffix_memory, cap_open_group_address state node marks index, source]
  simp only [MachineState.setMem, before]

theorem cap_open_group_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x27) :
    (capOpenGroupPrefix state 6).getReg reg = state.getReg reg := by
  rw [cap_open_group_succ state 5 (by decide)]
  change (execInstrBr (capOpenGroupPrefix state 5) (.BNE .x27 .x0 8044)).getReg reg = _
  rw [branch_register]
  simp only [capOpenGroupPrefix, capOpenGroupInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC, store_register,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2)]

theorem cap_open_group_retained_inputs (floor : Nat) (state reference : MachineState)
    (node : Nat) (floorBound : floor ≤ 2^64) (bounded : node < 512)
    (marks : state.getReg .x22 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (frame : CapOpenRetainedInputs floor reference state) :
    CapOpenRetainedInputs floor reference (capOpenGroupPrefix state 6) := by
  have written := cap_open_retained_store floor state reference (28672+8*node)
    (state.getReg .x31) floorBound (by omega) frame
  exact cap_open_retained_memory floor _ _ reference
    (cap_open_group_memory state node marks index) written

end CommitGolfCandidate
