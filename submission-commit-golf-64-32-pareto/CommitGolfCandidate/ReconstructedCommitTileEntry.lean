import CommitGolfCandidate.ReconstructedCommitExact

namespace CommitGolfCandidate.Reconstruction.CommitTile
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitControl CommitBlocks CommitSetup CommitExact OracleComp

set_option maxRecDepth 16384
set_option maxHeartbeats 800000
attribute [local irreducible] ArtifactEncoding.decode execute

/-- Setup starts immediately after RANDOM, so these writes include the public marker,
but cannot touch the three key words already written at byte address 5637148560. -/
def ops : List Instr := [
  .ADDI .x5 .x0 0, .ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x9 .x0 4095,
  .SD .x8 .x9 0, .ADDI .x17 .x0 4095, .LUI .x19 36864, .ADDIW .x19 .x19 153,
  .SLLI .x19 .x19 5, .LUI .x10 1, .ADDIW .x10 .x10 3896, .LUI .x20 1]

def before (s : MachineState) (n : Nat) := (ops.take n).foldl execInstrBr s
private def opcode (n : Nat) := ops[n]?.getD .EBREAK

private theorem decoded (i : Fin 12) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨7+i.val, by have := i.isLt; omega⟩) =
      some (.base (opcode i.val)) := by fin_cases i <;> rfl

private theorem pc_op (s : MachineState) (i : Fin 12) :
    (execInstrBr s (opcode i.val)).pc = s.pc + 4 := by fin_cases i <;> rfl

private theorem succ (s : MachineState) (i : Fin 12) :
    before s (i.val+1) = execInstrBr (before s i.val) (opcode i.val) := by fin_cases i <;> rfl

theorem pc_before (s : MachineState) (pc : s.pc = addr 7) (n : Nat) (le : n ≤ 12) :
    (before s n).pc = addr (7+n) := by
  induction n with
  | zero => exact pc
  | succ n ih =>
    let i : Fin 12 := ⟨n,by omega⟩
    rw [succ s i,pc_op _ i,ih (by omega)]
    exact (addr_next (7+n)).symm

private theorem valid (s : MachineState) (base : s.getReg .x8 = 5637148528) (i : Fin 12) :
    ordinaryStep (before s i.val) (.base (opcode i.val)) = some (before s (i.val+1)) := by
  rw [succ s i]
  fin_cases i <;> first | rfl | skip
  change (if memoryArgumentsValid (before s 4) (.SD .x8 .x9 0) then _ else _) = _
  have b : (before s 4).getReg .x8 = 5637148528 := base
  have memory : memoryArgumentsValid (before s 4) (.SD .x8 .x9 0) = true := by
    simp only [memoryArgumentsValid,memAccess,b]; decide
  rw [memory]
  rfl

theorem registers (s : MachineState) (base : s.getReg .x8 = 5637148528) :
    let t := before s 12
    t.getReg .x5 = 0 ∧ t.getReg .x8 = 5637148528 ∧ t.getReg .x10 = 3896 ∧
    t.getReg .x11 = 200 ∧ t.getReg .x13 = 1 ∧ t.getReg .x17 = -1 ∧
    t.getReg .x19 = 4831843104 ∧ t.getReg .x20 = 4096 := by
  have reg : s.regs .x8 = 5637148528 := base
  simp [before,ops,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,signExtend12,reg]

theorem memory (s : MachineState) (base : s.getReg .x8 = 5637148528) :
    (before s 12).mem = (s.setMem 5637148528 (-1)).mem := by
  have reg : s.regs .x8 = 5637148528 := base
  simp [before,ops,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg,MachineState.setMem,signExtend12,reg]

theorem setup (o : Oracle) (s : MachineState) (pc : s.pc = addr 7) (base : s.getReg .x8 = 5637148528) :
    Segment o im 12 s (before s 12) := by
  have traceTo (n : Nat) (le : n ≤ 12) : Segment o im n s (before s n) := by
    induction n with
    | zero => exact CommitExact.empty o im s
    | succ n ih =>
      let i : Fin 12 := ⟨n,by omega⟩
      have f := fetch_at ⟨7+n,by omega⟩ _ (decoded i) (before s n) (pc_before s pc n (by omega))
      exact CommitExact.compose (ih (by omega)) (plain o im _ _ _ f (valid s base i))
  exact traceTo 12 (by decide)

end CommitGolfCandidate.Reconstruction.CommitTile
