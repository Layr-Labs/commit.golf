import CommitGolfCandidate.GroupedSeed
import CommitGolfCandidate.GroupedParentSetup
import CommitGolfCandidate.MixedWidthStopRun

/-! The whole P4 commit run: the key prologue, the grouped leaf scan over all 2^24 leaves, and 04680e02's
three-full-level parent sweep and root copy moved by one artifact chunk. Exact: every run takes 238,691,487 steps,
602,023,067 cycles and 51,904,511 oracle calls. (04680e02 `TwoPermutationPackedCommit`, with the chain expansion
and the old leaf loop replaced.) -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64

set_option maxRecDepth 60000
set_option maxHeartbeats 1700000
attribute [local irreducible] execute parentSetup rootPrefix

theorem image_eq : image = packedWideCommitImage := rfl

def postLeaves (leaves : MachineState) : OracleComp World MachineState := do
  let full ← FullWidth.parentGroups 186816 32768 65535 510 (mixedStopSetup (parentSetup leaves 5))
  let parents ← packedParentGroups 580040 13107 5 full
  return rootPrefix parents 10

theorem live_end_pc (s : MachineState) (r : Live s N) : s.pc=186784 := by
  have h := r.pc
  simp only [startPC,if_pos rfl] at h
  exact h

theorem post_leaves_run (leaves : MachineState) (r : Live leaves N) (fuel : Nat) :
    execute image (5+(3+(50136059+(262149+(11+fuel))))) leaves true =
      (do let result ← postLeaves leaves
          return ⟨.success,result,167838732,16777215⟩) := by
  have pc := live_end_pc leaves r
  have regs := parent_setup_ready leaves pc r.selector r.heapBase r.strideBase r.quartet
  let ready := parentSetup leaves 5
  have readyRegs : ParentRegs ready (2^24-1) := regs.1
  have fullRegs := mixed_stop_parent_regs ready (2^24-1) readyRegs
  have stop := mixed_stop_value ready (2^24-1) readyRegs
  have fullPC : (mixedStopSetup ready).pc=186816 := by
    rw [mixed_stop_pc,show ready.pc=186804 from regs.2.1]
    rfl
  rw [execute_parent_setup leaves pc,image_eq,execute_mixed_stop ready regs.2.1,
    mixed_full_phase _ _ fullRegs stop fullPC]
  simp only [postLeaves,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro full fullReached
  have fullPost := FullWidth.groups_post 186816 32768 65535 510 (mixedStopSetup ready)
    (by decide) (fun _ => fullPC) fullRegs fullReached
  have projectedPC : full.pc=580040 := fullPost.2 (by decide)
  have fullOutput : full.getReg .x8=(mixedStopSetup ready).getReg .x8 :=
    FullWidth.groups_keep_register _ _ _ _ _ _ .x8 (by decide) (by decide) fullReached
  rw [mixed_projected_phase full _ fullPost.1 projectedPC]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,ppc,out⟩ := mixed_projected_phase_post _ fullPost.1 projectedPC reached
  have output : parents.getReg .x8=4294971392 := out.trans
    (fullOutput.trans ((mixed_stop_register ready .x8 (by decide)).trans (regs.2.2.trans r.out)))
  rw [execute_packed_root parents ppc terms.heap output]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem S_N : S N=186261503 := by decide
theorem Q_N : Q N=35127296 := by decide
theorem C_N : C N=432152575 := by decide

def body (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← scan N 0 ready
  postLeaves leaves

theorem body_run (ready : MachineState) (r : Live ready 0) (fuel : Nat) :
    execute image (186261503+(5+(3+(50136059+(262149+(11+fuel)))))) ready true =
      (do let result ← body ready
          return ⟨.success,result,599991307,51904511⟩) := by
  have scanned := run_scan N 0 ready (by decide) r (5+(3+(50136059+(262149+(11+fuel)))))
  rw [show S (0+N)-S 0=186261503 by decide,show C (0+N)-C 0=432152575 by decide,
    show Q (0+N)-Q 0=35127296 by decide] at scanned
  rw [scanned]
  simp only [body,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have live : Live leaves N := by simpa using scan_post N 0 ready leaves (by decide) r reached
  rw [post_leaves_run leaves live fuel]
  simp only [bind_assoc,pure_bind,Execution.charge]

def commitTrace (initial : MachineState) : OracleComp World Execution := do
  let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
  let state ← body (keyReady initial k)
  return ⟨.success,state,599991331,51904511⟩

end TwoPermutationPrototype.Grouped
