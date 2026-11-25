import CommitGolfCandidate.TwoPermutationHybridLower
import CommitGolfCandidate.TwoPermutationPackedParentImage

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute packedWideCommitImage

def hybridStart (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.LUI .x18 512)) (.ADD .x18 .x18 .x8)

def hybridUpper (s : MachineState) : OracleComp World MachineState := do
  let mid ← packedParentsTrace 55190 10345 s
  packedParentGroups 610808 27595 2 (mid.setPC 610808)

def hybridParentPhase (s : MachineState) : OracleComp World MachineState := do
  let lower ← hybridLower 510 (hybridStart s)
  hybridUpper (lower.setPC 886808)

theorem hybrid_start_run (s : MachineState) (pc : s.pc=217572) (fuel : Nat) :
    execute packedWideCommitImage (2+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (hybridStart s) true
          return out.charge 2 0) := by
  let mid := execInstrBr s (.LUI .x18 512)
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
  change 2097152+s.getReg .x8=_;rw [out];rfl

theorem hybrid_skip_run (s : MachineState) (pc : s.pc=610804) (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (s.setPC 886808) true
          return out.charge 1 0) := by
  have jump : ordinaryStep s (.base (.JAL .x0 276004)) = some (s.setPC 886808) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,MachineState.setPC,pc]
    rfl
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (hybrid_skip s pc) jump]
  rfl

theorem hybrid_upper_run (s : MachineState) (fuel : Nat) (regs : ParentRegs s hybridCut) (pc : s.pc=886808) :
    execute packedWideCommitImage (262145+fuel) s true =
      (do let out ← hybridUpper s
          let res ← execute packedWideCommitImage fuel out true
          return res.charge 720890 hybridCut) := by
  have part := packed_parent_segment packedWideCommitImage 610808 27595 packed_parent_words 55190 10345 17250
    (2+(220763+fuel)) s (by decide) (by decide) regs pc
  rw [show 262145+fuel=4*10345+(2+(220763+fuel)) by omega,part]
  simp only [hybridUpper,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro body hit
  have post := packed_parent_segment_post 610808 55190 10345 17250 s regs pc hit
  have latch := packed_parent_latch packedWideCommitImage 610808 27595 fixedWideParentControl 55190 (220763+fuel)
    body (by decide) post.1 post.2
  rw [show 2=longParentLatchCost 55190 from rfl,latch]
  let next := body.setPC 610808
  have nr : ParentRegs next 55190 :=
    ⟨post.1.source,post.1.target,post.1.selector,post.1.size,post.1.primitive,post.1.heap⟩
  have rest := packed_group_execution packedWideCommitImage 610808 27595 packed_parent_words
    fixedWideParentControl (by decide) 2 fuel next (by decide) nr (fun _ => rfl)
  change execute packedWideCommitImage (220763+fuel) next true = _ at rest
  rw [show body.setPC (packedParentNextPC 610808 27595 55190)=next from rfl,rest]
  simp [next,Execution.charge,←Nat.add_assoc]
  rfl

private theorem packed_groups_frame (groups : Nat) (s : MachineState) {out : MachineState}
    (hit : out ∈ support (packedParentGroups 610808 27595 groups s)) : out.getReg .x8=s.getReg .x8 := by
  induction groups generalizing s with
  | zero => simp only [packedParentGroups,support_pure,Set.mem_singleton_iff] at hit;subst out;rfl
  | succ n ih =>
    simp only [packedParentGroups,mem_support_bind_iff] at hit
    obtain ⟨body,path,tail⟩ := hit
    exact (ih _ tail).trans (packed_trace_frame _ _ s (out:=body) path)

theorem hybrid_upper_post (s : MachineState) (regs : ParentRegs s hybridCut) (pc : s.pc=886808)
    {out : MachineState} (hit : out ∈ support (hybridUpper s)) :
    ParentRegs out 0 ∧ out.pc=1052336 ∧ out.getReg .x8=s.getReg .x8 := by
  simp only [hybridUpper,mem_support_bind_iff] at hit
  obtain ⟨body,path,tail⟩ := hit
  have post := packed_parent_segment_post 610808 55190 10345 17250 s regs pc path
  let next := body.setPC 610808
  have nr : ParentRegs next 55190 :=
    ⟨post.1.source,post.1.target,post.1.selector,post.1.size,post.1.primitive,post.1.heap⟩
  have rest := packed_groups_post 610808 27595 2 next (by decide) (fun _ => rfl) nr tail
  exact ⟨rest.1,rest.2 (by decide),(packed_groups_frame 2 next tail).trans (packed_trace_frame _ _ s (out:=body) path)⟩

private theorem fixedLowerCode : HybridLowerCode packedWideCommitImage :=
  ⟨hybrid_full_words,hybrid_lower_branch,hybrid_lower_back⟩

theorem hybrid_parent_phase (state : MachineState) (fuel : Nat) (regs : ParentRegs state (2^24-1))
    (pc : state.pc=217572) (output : state.getReg .x8=4294971392) :
    execute packedWideCommitImage (50398207+fuel) state true =
      (do let next ← hybridParentPhase state
          let result ← execute packedWideCommitImage fuel next true
          return result.charge 167838712 16777215) := by
  have start : (hybridStart state).pc=217580 := by change state.pc+4+4=_;rw [pc];rfl
  have regs' := hybrid_start_regs state _ regs
  rw [show 50398207+fuel=2+(lowerCost 3 510+(1+(262145+fuel))) by change 50398207+fuel=2+(50136059+(1+(262145+fuel)));omega,hybrid_start_run state pc,
    lower_run packedWideCommitImage fixedLowerCode 510 _ _ (by decide) regs' (fun _ => start) (hybrid_threshold state output)]
  simp only [hybridParentPhase,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro mid hit
  have post := lower_post 510 _ (fun _ => start) regs' hit
  have next : ParentRegs (mid.setPC 886808) hybridCut := ⟨post.1.source,post.1.target,post.1.selector,
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
  have post := lower_post 510 _ (fun _ => start) (hybrid_start_regs state _ regs) path
  have nr : ParentRegs (mid.setPC 886808) hybridCut :=
    ⟨post.1.source,post.1.target,post.1.selector,post.1.size,post.1.primitive,post.1.heap⟩
  have rest := hybrid_upper_post _ nr rfl tail
  exact ⟨rest.1,rest.2.1,rest.2.2.trans post.2.2⟩

end TwoPermutationPrototype.RV64
