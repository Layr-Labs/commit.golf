import CommitGolfCandidate.TwoPermutationWideSetup

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192
set_option maxHeartbeats 1700000
attribute [local irreducible] execute wideReadyState parentSetup rootPrefix

structure WideLeavesFinished (state : MachineState) : Prop where
  pc : state.pc=18536
  selector : state.getReg .x5=0
  heap : state.getReg .x9=4294971424
  stride : state.getReg .x19=536870912
  stop : state.getReg .x21=wordAddress (leafDest (2^24))
  output : state.getReg .x8=4294971392

structure WideLeafExecution where
  trace : MachineState → OracleComp World MachineState
  executes : ∀ (initial : MachineState), CommitEntry initial → ∀ {bits : Nat}
    (coins : BitVec bits) (fuel : Nat),
      execute wideCommitImage (235405311+fuel) (wideReadyState initial coins) true =
        (do let leaves ← trace (wideReadyState initial coins)
            let out ← execute wideCommitImage fuel leaves true
            return out.charge 470286335 33554432)
  finished : ∀ (initial : MachineState), CommitEntry initial → ∀ {bits : Nat}
    (coins : BitVec bits) (out : MachineState),
      out ∈ support (trace (wideReadyState initial coins)) → WideLeavesFinished out

def wideCommitBody (leaf : WideLeafExecution) (initial : MachineState) {bits : Nat}
    (coins : BitVec bits) : OracleComp World MachineState := do
  let leaves ← leaf.trace (wideReadyState initial coins)
  let parents ← wideParentGroups 18556 86037 195 (parentSetup leaves 5)
  return rootPrefix parents 10

theorem wide_commit_after_draw (leaf : WideLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) {bits : Nat} (coins : BitVec bits) (fuel : Nat) :
    execute wideCommitImage (285737361+fuel) (wideReadyState initial coins) true =
      (do let result ← wideCommitBody leaf initial coins
          return ⟨.success,result,638058890,50331647⟩) := by
  rw [show 285737361+fuel=235405311+(5+(50332034+(11+fuel))) by omega,
    leaf.executes initial entry coins]
  simp only [wideCommitBody,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have fin := leaf.finished initial entry coins leaves reached
  have regs := wide_parent_setup_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop
  rw [execute_wide_parent_setup leaves fin.pc,wide_parent_phase _ _ regs.1 regs.2.1]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,pc,out⟩ := wide_parent_phase_post _ regs.1 regs.2.1 reached
  rw [execute_wide_root parents pc terms.heap (out.trans (regs.2.2.trans fin.output))]
  simp only [bind_assoc,pure_bind,Execution.charge]

def wideCommitTrace (leaf : WideLeafExecution) (initial : MachineState) :
    OracleComp World Execution := do
  let coins ← liftM ($ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat) :
    ProbComp (BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)))
  let state ← wideCommitBody leaf initial coins
  return ⟨.success,state,671613340,50331647⟩

theorem wide_commit_execution (leaf : WideLeafExecution) (initial : MachineState)
    (entry : CommitEntry initial) (fuel : Nat) :
    execute wideCommitImage (285737379+fuel) initial true=wideCommitTrace leaf initial := by
  rw [show 285737379+fuel=18+(285737361+fuel) by omega,execute_wide_setup initial entry]
  simp only [wideCommitTrace,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro coins _
  rw [wide_commit_after_draw leaf initial entry coins]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem submission_wide_commit_run (leaf : WideLeafExecution) (program : Submission)
    (image : program.image .commit=wideCommitImage) (enough : 285737379≤program.steps .commit)
    (message : Message) (entry : CommitEntry (program.initialState .commit message)) :
    program.run .commit message=wideCommitTrace leaf (program.initialState .commit message) := by
  change execute (program.image .commit) (program.steps .commit)
    (program.initialState .commit message) true=_
  rw [image,show program.steps .commit=285737379+(program.steps .commit-285737379) by omega]
  exact wide_commit_execution leaf _ entry _

end TwoPermutationPrototype.RV64
