import CommitGolfCandidate.TwoPermutationHybridPhase
import CommitGolfCandidate.TwoPermutationPackedSetup

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1700000
attribute [local irreducible] execute packed_wideReadyState parentSetup rootPrefix

structure PackedLeavesFinished (state : MachineState) : Prop where
  pc : state.pc=184784
  selector : state.getReg .x5=0
  heap : state.getReg .x9=4294971424
  stride : state.getReg .x19=536870912
  stop : state.getReg .x21=wordAddress (leafDest (2^24))
  output : state.getReg .x8=4294971392

structure PackedLeafExecution where
  trace : MachineState → OracleComp World MachineState
  executes : ∀ (initial : MachineState), CommitEntry initial → ∀ {bits : Nat}
    (coins : BitVec bits) (fuel : Nat),
      execute packedWideCommitImage (268705792+fuel) (packed_wideReadyState initial coins) true =
        (do let leaves ← trace (packed_wideReadyState initial coins)
            let out ← execute packedWideCommitImage fuel leaves true
            return out.charge 1107566592 67108864)
  finished : ∀ (initial : MachineState), CommitEntry initial → ∀ {bits : Nat}
    (coins : BitVec bits) (out : MachineState),
      out ∈ support (trace (packed_wideReadyState initial coins)) → PackedLeavesFinished out

theorem regs_set_pc {s : MachineState} {n : Nat} (regs : ParentRegs s n) (pc : Word) :
    ParentRegs (s.setPC pc) n := ⟨regs.source,regs.target,regs.selector,regs.size,regs.primitive,regs.heap⟩

def relocatedPhase (s : MachineState) := hybridParentPhase (s.setPC 217572)

theorem relocated_phase (s : MachineState) (fuel : Nat) (regs : ParentRegs s (2^24-1))
    (pc : s.pc=184804) (output : s.getReg .x8=4294971392) :
    execute packedWideCommitImage (59785730+fuel) s true =
      (do let next ← relocatedPhase s
          let result ← execute packedWideCommitImage fuel next true
          return result.charge 177226235 16777215) := by
  have fetch := packed_wide_fetch_decoded s 45177 (by decide) pc (.JAL .x0 32768) rfl
  have step : ordinaryStep s (.base (.JAL .x0 32768)) = some (s.setPC 217572) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,MachineState.setPC,pc]
    rfl
  rw [show 59785730+fuel=(59785729+fuel)+1 by omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fetch step,
    hybrid_parent_phase (s.setPC 217572) fuel (regs_set_pc regs _) rfl output]
  simp [relocatedPhase,instructionCycles,Execution.charge,←Nat.add_assoc]

theorem relocated_phase_post (s : MachineState) (regs : ParentRegs s (2^24-1))
    (_pc : s.pc=184804) (output : s.getReg .x8=4294971392) {out : MachineState}
    (hit : out ∈ support (relocatedPhase s)) :
    ParentRegs out 0 ∧ out.pc=1052336 ∧ out.getReg .x8=s.getReg .x8 :=
  hybrid_parent_phase_post (s.setPC 217572) (regs_set_pc regs _) rfl output hit

def packed_wideCommitBody (leaf : PackedLeafExecution) (initial : MachineState) {bits : Nat}
    (coins : BitVec bits) : OracleComp World MachineState := do
  let leaves ← leaf.trace (packed_wideReadyState initial coins)
  let parents ← relocatedPhase (parentSetup leaves 5)
  return rootPrefix parents 10

theorem packed_wide_commit_after_draw (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) {bits : Nat} (coins : BitVec bits) (fuel : Nat) :
    execute packedWideCommitImage (328491538+fuel) (packed_wideReadyState initial coins) true =
      (do let result ← packed_wideCommitBody leaf initial coins
          return ⟨.success,result,1284792843,83886079⟩) := by
  rw [show 328491538+fuel=268705792+(5+(59785730+(11+fuel))) by omega,
    leaf.executes initial entry coins]
  simp only [packed_wideCommitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have fin := leaf.finished initial entry coins leaves reached
  have regs := packed_wide_parent_setup_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop
  rw [packed_execute_wide_parent_setup leaves fin.pc,relocated_phase _ _ regs.1 regs.2.1 (regs.2.2.trans fin.output)]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,pc,out⟩ := relocated_phase_post _ regs.1 regs.2.1 (regs.2.2.trans fin.output) reached
  rw [execute_packed_root parents pc terms.heap (out.trans (regs.2.2.trans fin.output))]
  simp only [bind_assoc,pure_bind,Execution.charge]

def packed_wideCommitTrace (leaf : PackedLeafExecution) (initial : MachineState) :
    OracleComp World Execution := do
  let coins ← liftM ($ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat) :
    ProbComp (BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)))
  let state ← packed_wideCommitBody leaf initial coins
  return ⟨.success,state,1318347295,83886079⟩

theorem packed_wide_commit_execution (leaf : PackedLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) (fuel : Nat) :
    execute packedWideCommitImage (328491558+fuel) initial true=packed_wideCommitTrace leaf initial := by
  rw [show 328491558+fuel=20+(328491538+fuel) by omega,packed_execute_wide_setup initial entry]
  simp only [packed_wideCommitTrace,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro coins _
  rw [packed_wide_commit_after_draw leaf initial entry coins]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem packed_submission_wide_commit_run (leaf : PackedLeafExecution) (program : Submission)
    (image : program.image .commit=packedWideCommitImage) (enough : 328491558≤program.steps .commit)
    (message : Message) (entry : CommitEntry (program.initialState .commit message)) :
    program.run .commit message=packed_wideCommitTrace leaf (program.initialState .commit message) := by
  change execute (program.image .commit) (program.steps .commit)
    (program.initialState .commit message) true=_
  rw [image,show program.steps .commit=328491558+(program.steps .commit-328491558) by omega]
  exact packed_wide_commit_execution leaf _ entry _

end TwoPermutationPrototype.RV64
