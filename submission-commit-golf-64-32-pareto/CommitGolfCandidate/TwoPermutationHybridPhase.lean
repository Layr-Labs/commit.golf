import CommitGolfCandidate.R1bParentEntry
import CommitGolfCandidate.TwoPermutationHybridLower
import CommitGolfCandidate.TwoPermutationPackedParentImage

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute packedWideCommitImage

def hybridStart (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.LUI .x18 65536)) (.ADD .x18 .x18 .x8)

def hybridUpper (s : MachineState) := R1bParents.trace hybridCut (R1bParents.setup s 5)

def hybridParentPhase (s : MachineState) : OracleComp World MachineState := do
  let lower ← hybridLower 256 (hybridStart s)
  hybridUpper (lower.setPC 4180)

theorem hybrid_start_run (s : MachineState) (pc : s.pc=217572) (fuel : Nat) :
    execute packedWideCommitImage (2+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (hybridStart s) true
          return out.charge 2 0) := by
  let mid := execInstrBr s (.LUI .x18 65536)
  have here : mid.pc=217576 := by change s.pc+4=_;rw [pc];rfl
  rw [show 2+fuel=(fuel+1)+1 by omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (hybrid_threshold_lui s pc)
      (show ordinaryStep s _=some mid from rfl),
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (hybrid_threshold_add mid here)
      (show ordinaryStep mid _=some (hybridStart s) from rfl)]
  simp [instructionCycles,Execution.charge,←Nat.add_assoc]

theorem hybrid_start_regs (s : MachineState) (n : Nat) (regs : ParentRegs s n) :
    ParentRegs (hybridStart s) n :=
  ⟨regs.source,regs.target,regs.selector,regs.size,regs.primitive,regs.heap⟩

theorem hybrid_threshold (s : MachineState) (out : s.getReg .x8=4294971392) :
    (hybridStart s).getReg .x18=wordAddress (treeWord hybridCut) := by
  change 268435456+s.getReg .x8=_;rw [out];rfl

theorem hybrid_skip_run (s : MachineState) (pc : s.pc=610804) (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (s.setPC 4180) true
          return out.charge 1 0) := by
  have jump : ordinaryStep s (.base (.JAL .x0 1490528)) = some (s.setPC 4180) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,MachineState.setPC,pc]
    rfl
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (hybrid_skip s pc) jump]
  rfl

theorem hybrid_upper_run (s : MachineState) (fuel : Nat) (regs : ParentRegs s hybridCut) (pc : s.pc=4180) :
    execute packedWideCommitImage (34619391+fuel) s true =
      (do let out ← hybridUpper s
          let res ← execute packedWideCommitImage fuel out true
          return res.charge 93339640 hybridCut) := by
  have ready:=R1bParents.setupReady s pc regs
  have trace:=R1bParents.trace_run R1bParents.node_execution hybridCut fuel _ (by decide) ready
  change execute packedWideCommitImage (34619386+fuel) _ true=_ at trace
  rw [show 34619391+fuel=5+(34619386+fuel) by omega,R1bParents.setupRun s pc,trace]
  simp [hybridUpper,Execution.charge,←Nat.add_assoc,R1bParents.remainingSteps,hybridCut]

theorem hybrid_upper_post (s : MachineState) (regs : ParentRegs s hybridCut) (pc : s.pc=4180)
    {out : MachineState} (hit : out ∈ support (hybridUpper s)) :
    ParentRegs out 0 ∧ out.pc=1052336 ∧ out.getReg .x8=s.getReg .x8 := by
  obtain ⟨done,saved⟩ := R1bParents.trace_post hybridCut _ (R1bParents.setupReady s pc regs) hit
  exact ⟨done.toParentRegs,done.pc,saved⟩

private theorem fixedLowerCode : HybridLowerCode packedWideCommitImage :=
  ⟨hybrid_full_words,hybrid_lower_branch,hybrid_lower_back⟩

theorem hybrid_parent_phase (state : MachineState) (fuel : Nat) (regs : ParentRegs state (2^24-1))
    (pc : state.pc=217572) (output : state.getReg .x8=4294971392) :
    execute packedWideCommitImage (59785729+fuel) state true =
      (do let next ← hybridParentPhase state
          let result ← execute packedWideCommitImage fuel next true
          return result.charge 177226234 16777215) := by
  have start : (hybridStart state).pc=217580 := by change state.pc+4+4=_;rw [pc];rfl
  have regs' := hybrid_start_regs state _ regs
  rw [show 59785729+fuel=2+(lowerCost 3 256+(1+(34619391+fuel))) by change 59785729+fuel=2+(25166335+(1+(34619391+fuel)));omega,hybrid_start_run state pc,
    lower_run packedWideCommitImage fixedLowerCode 256 _ _ (by decide) regs' (fun _ => start) (hybrid_threshold state output)]
  simp only [hybridParentPhase,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro mid hit
  have post := lower_post 256 _ (fun _ => start) regs' hit
  have next : ParentRegs (mid.setPC 4180) hybridCut := ⟨post.1.source,post.1.target,post.1.selector,
    post.1.size,post.1.primitive,post.1.heap⟩
  rw [hybrid_skip_run mid (post.2.1 (by decide)),hybrid_upper_run _ fuel next rfl]
  simp [Execution.charge,lowerCost,fullSpan,hybridCut,←Nat.add_assoc]

theorem hybrid_parent_phase_post (state : MachineState) (regs : ParentRegs state (2^24-1))
    (pc : state.pc=217572) (_output : state.getReg .x8=4294971392) {out : MachineState}
    (hit : out ∈ support (hybridParentPhase state)) :
    ParentRegs out 0 ∧ out.pc=1052336 ∧ out.getReg .x8=state.getReg .x8 := by
  simp only [hybridParentPhase,mem_support_bind_iff] at hit
  obtain ⟨mid,path,tail⟩ := hit
  have start : (hybridStart state).pc=217580 := by change state.pc+4+4=_;rw [pc];rfl
  have post := lower_post 256 _ (fun _ => start) (hybrid_start_regs state _ regs) path
  have nr : ParentRegs (mid.setPC 4180) hybridCut :=
    ⟨post.1.source,post.1.target,post.1.selector,post.1.size,post.1.primitive,post.1.heap⟩
  have rest := hybrid_upper_post _ nr rfl tail
  exact ⟨rest.1,rest.2.1,rest.2.2.trans post.2.2⟩

end TwoPermutationPrototype.RV64
