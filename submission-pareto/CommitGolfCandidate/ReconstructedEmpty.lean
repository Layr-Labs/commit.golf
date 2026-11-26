import CommitGolf.Artifact
import CommitGolfCandidate.Execution
import CommitGolfCandidate.ReconstructedFetch

namespace CommitGolfCandidate.Reconstruction
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

def entryImage (checker : Bool) : Image :=
  Artifact.submission.image (if checker then .check else .opening)

private def selector (checker : Bool) : Instr :=
  if checker then .SLTU .x10 .x0 .x17 else .ADDI .x10 .x0 0

private def entryOp (checker : Bool) : Fin 5 → Instr
  | 0 => .BNE .x16 .x0 20
  | 1 => selector checker
  | 2 => .ADDI .x11 .x0 0
  | 3 => .ADDI .x5 .x0 1
  | 4 => .ECALL

private theorem decoded (checker : Bool) (i : Fin 5) :
    ((entryImage checker).code[i.val]?).bind decodeInstruction = some (.base (entryOp checker i)) := by
  cases checker <;> fin_cases i <;> rfl

private theorem fetch_entry (checker : Bool) (i : Fin 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4*i.val)) :
    fetch (entryImage checker) state = some (.base (entryOp checker i)) := by
  have small := i.isLt
  have hn : state.pc.toNat = 4096 + 4*i.val := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, hn, ite_eq_left (by omega), show (4096 + 4*i.val - 4096) / 4 = i.val by omega]
  have h := decoded checker i
  cases w : (entryImage checker).code[i.val]? with
  | none => simp [w] at h
  | some word => simpa [w] using h

def emptyFinal (s : MachineState) : MachineState :=
  (((s.setReg .x10 0).setReg .x11 0).setReg .x5 1).setPC 4112

/-- Concrete five-instruction empty-opening path in each submitted image. -/
theorem empty_execution (checker : Bool) (s : MachineState) (pc : s.pc = 4096)
    (empty : s.getReg .x16 = 0) (proof : checker = true → s.getReg .x17 = 0)
    (extra : Nat) (coins : Bool) :
    execute (entryImage checker) (5+extra) s coins = pure ⟨.success, emptyFinal s, 5, 0⟩ := by
  let s1 := s.setPC 4100
  let s2 := (s.setReg .x10 0).setPC 4104
  let s3 := ((s.setReg .x10 0).setReg .x11 0).setPC 4108
  have f0 := fetch_entry checker 0 s pc
  have f1 := fetch_entry checker 1 s1 rfl
  have f2 := fetch_entry checker 2 s2 rfl
  have f3 := fetch_entry checker 3 s3 rfl
  have f4 := fetch_entry checker 4 (emptyFinal s) rfl
  have t0 : ordinaryStep s (.base (entryOp checker 0)) = some s1 := by
    simp [entryOp, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, empty, pc,
      show s.getReg .x0 = 0#64 from rfl, s1]
  have t1 : ordinaryStep s1 (.base (entryOp checker 1)) = some s2 := by
    cases checker <;> simp_all [s1, s2, entryOp, selector, ordinaryStep, memoryArgumentsValid,
      memAccess, execInstrBr, signExtend12, MachineState.setPC, MachineState.setReg, MachineState.getReg]
  have t2 : ordinaryStep s2 (.base (entryOp checker 2)) = some s3 := by rfl
  have t3 : ordinaryStep s3 (.base (entryOp checker 3)) = some (emptyFinal s) := by rfl
  have halt : execute (entryImage checker) (extra+1) (emptyFinal s) coins =
      pure ⟨.success, emptyFinal s, 1, 0⟩ := by
    change fetch _ _ = some (.base .ECALL) at f4
    rw [execute, f4]
    rfl
  rw [Nat.add_comm 5 extra,
    execute_ordinary_step _ _ _ _ _ _ f0 t0, execute_ordinary_step _ _ _ _ _ _ f1 t1,
    execute_ordinary_step _ _ _ _ _ _ f2 t2, execute_ordinary_step _ _ _ _ _ _ f3 t3, halt]
  simp only [pure_bind]
  cases checker <;> rfl

private theorem open_run (sub : Submission) (input : Input sub.sizes .opening) :
    sub.run .opening input = execute (sub.image .opening) (sub.steps .opening)
      (sub.initialState .opening input) true := rfl

private theorem check_run (sub : Submission) (input : CheckInput) (h : input.proof.length ≤ sub.sizes.proof) :
    sub.run .check input = execute (sub.image .check) (sub.steps .check)
      (sub.initialState .check input) false := by simp [Submission.run, h]

private theorem start_pc (sub : Submission) (p : Program) (input : Input sub.sizes p) :
    (sub.initialState p input).pc = 4096 := rfl

private theorem start_count (sub : Submission) (p : Program) (input : Input sub.sizes p) :
    (sub.initialState p input).getReg .x16 = BitVec.ofNat 64 (inputCount p input) := rfl

private theorem start_length (sub : Submission) (input : CheckInput) :
    (sub.initialState .check input).getReg .x17 = BitVec.ofNat 64 input.proof.length := rfl

theorem run_empty_opening (trapdoor : BitVec (8 * Artifact.submission.sizes.trapdoor)) :
    let input : Input Artifact.submission.sizes .opening := (trapdoor, ∅)
    Artifact.submission.run .opening input =
      pure ⟨.success, emptyFinal (Artifact.submission.initialState .opening input), 5, 0⟩ := by
  intro input
  rw [open_run, show Artifact.submission.steps .opening = 5 + (68719476736-5) by rfl]
  apply empty_execution false _ (start_pc _ _ _) _ _ _ true
  · rw [start_count]; rfl
  · intro h; contradiction

theorem run_empty_check (root : Commitment) (values : Values ∅) :
    let input : CheckInput := ⟨root, ∅, values, []⟩
    Artifact.submission.run .check input =
      pure ⟨.success, emptyFinal (Artifact.submission.initialState .check input), 5, 0⟩ := by
  intro input
  rw [check_run _ input (by exact Nat.zero_le _),
    show Artifact.submission.steps .check = 5 + (274877906944-5) by rfl]
  apply empty_execution true _ (start_pc _ _ _) _ _ _ false
  · exact (start_count Artifact.submission .check input).trans (by rfl)
  · intro h; exact (start_length Artifact.submission input).trans (by rfl)

end CommitGolfCandidate.Reconstruction
