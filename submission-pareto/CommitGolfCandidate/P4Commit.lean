import CommitGolfCandidate.GroupedSeed
import CommitGolfCandidate.GroupedParentSetup
import CommitGolfCandidate.TwoPermutationPackedParentImage

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
  let parents ← packedParentGroups 186804 36873 455 (parentSetup leaves 5)
  return rootPrefix parents 10

theorem live_end_pc (s : MachineState) (r : Live s N) : s.pc=186784 := by
  have h := r.pc
  simp only [startPC,if_pos rfl] at h
  exact h

theorem post_leaves_run (leaves : MachineState) (r : Live leaves N) (fuel : Nat) :
    execute image (5+(67109769+(11+fuel))) leaves true =
      (do let result ← postLeaves leaves
          return ⟨.success,result,184550290,16777215⟩) := by
  have pc := live_end_pc leaves r
  have regs := parent_setup_ready leaves pc r.selector r.heapBase r.strideBase r.quartet
  rw [execute_parent_setup leaves pc,image_eq,packed_parent_phase _ _ regs.1 regs.2.1]
  simp only [postLeaves,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro parents reached
  obtain ⟨terms,ppc,out⟩ := packed_parent_phase_post _ regs.1 regs.2.1 reached
  rw [execute_packed_root parents ppc terms.heap (out.trans (regs.2.2.trans r.out))]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem S_N : S N=184688639 := by decide
theorem Q_N : Q N=35082240 := by decide
theorem C_N : C N=430264319 := by decide

def body (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← scan N 0 ready
  postLeaves leaves

theorem body_run (ready : MachineState) (r : Live ready 0) (fuel : Nat) :
    execute image (184688639+(5+(67109769+(11+fuel)))) ready true =
      (do let result ← body ready
          return ⟨.success,result,614814609,51859455⟩) := by
  have scanned := run_scan N 0 ready (by decide) r (5+(67109769+(11+fuel)))
  rw [show S (0+N)-S 0=184688639 by decide,show C (0+N)-C 0=430264319 by decide,
    show Q (0+N)-Q 0=35082240 by decide] at scanned
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
  return ⟨.success,state,614814633,51859455⟩

end TwoPermutationPrototype.Grouped
