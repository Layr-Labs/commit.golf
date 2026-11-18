import CommitGolfCandidate.GroupedSetup
import CommitGolfCandidate.GroupedQPost
import CommitGolfCandidate.GroupedUpperImage
import CommitGolfCandidate.QuartetCommitJoinRegs

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qUpper packed_sequence_keeps_output wide_parent_full_register)
set_option maxRecDepth 32000
set_option maxHeartbeats 1800000
attribute [local irreducible] execute image GroupedUpper.packedWideCommitImage qGroups qUnits scan packedParentsTrace packedParentGroups rootPrefix

structure Kept (s : MachineState) : Prop where
  heap : s.getReg .x9=4294971424
  output : s.getReg .x8=4294971392
  stride : s.getReg .x19=536870912

theorem quartet_entry (s : MachineState) (r : Live s N) :
    s.pc=wordPC 45591 ∧ (qStartPrefix s 3).pc=quadPC 0 ∧ QRegs (qStartPrefix s 3) 0 ∧ Kept (qStartPrefix s 3) := by
  have pc : s.pc=wordPC 45591 := by simpa only [startPC,ite_true] using r.pc
  refine ⟨pc,?_,?_,⟨r.heapBase,r.out,r.strideBase⟩⟩
  · change s.pc+4+4+4=_;rw [pc];rfl
  · refine ⟨?_,?_,r.selector,r.size,r.primitive,r.counter⟩
    · change s.getReg .x21+0=_;rw [r.quartet];rfl
    · change s.getReg .x9+(s.getReg .x19 >>> (2:Nat))=_;rw [r.heapBase,r.strideBase];rfl

theorem start_upper (before : MachineState) (r : QRegs before 0) (pc : before.pc=quadPC 0)
    (carry : Kept before) {s : MachineState} (hit : s ∈ support (qGroups 512 0 before)) :
    s.pc=wordPC 70172 ∧ (upStartPrefix s 6).pc=284808 ∧ ParentRegs (upStartPrefix s 6) 4194303 ∧
      (upStartPrefix s 6).getReg .x8=4294971392 := by
  obtain ⟨regs,here⟩ := q_groups_end before 512 0 (by decide) (by decide) r pc hit
  have stride := (q_groups_saved before 0 512 .x19 (by decide) (by decide) hit).trans carry.stride
  have heap := (q_groups_saved before 0 512 .x9 (by decide) (by decide) hit).trans carry.heap
  have output := (q_groups_saved before 0 512 .x8 (by decide) (by decide) hit).trans carry.output
  refine ⟨here,?_,?_,output⟩
  · change s.pc+4+4+4+4+4+4=_;rw [here];rfl
  · refine ⟨?_,?_,regs.selector,rfl,rfl,heap⟩
    · change s.getReg .x12+signExtend12 4032=_;rw [regs.dest];rfl
    · change s.getReg .x12-(s.getReg .x19 >>> (2 : Nat))+signExtend12 4064=_;rw [regs.dest,stride];rfl


def tailBody (s : MachineState) : OracleComp World MachineState := do
  let quad ← qGroups 512 0 (qStartPrefix s 3)
  let us ← packedParentsTrace 4194176 127 (upStartPrefix quad 6)
  let parents ← packedParentGroups GroupedUpper.loopBase 32767 128 us
  return rootPrefix parents 10

theorem tail_run (s : MachineState) (r : Live s N) (fuel : Nat) :
    execute image (29361422+fuel) s true = (do let t ← tailBody s; return ⟨.success,t, 88081671,8388607⟩) := by
  have same_image : image=GroupedUpper.packedWideCommitImage := exact_image.trans GroupedUpper.packed_manifest_image.symm
  rw [show 29361422+fuel=3+(12583935+(6+(508+(16776959+(11+fuel))))) by omega]
  unfold tailBody
  obtain ⟨lpc,qpc,qregs,carry⟩ := quartet_entry s r
  rw [qStart_run _ lpc,entire_quartet_phase _ _ qregs qpc]
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro quad path
  obtain ⟨rpc,startpc,regs,out⟩ := start_upper _ qregs qpc carry path
  rw [upStart_run _ rpc,same_image,GroupedUpper.upper_prefix_run _ _ regs startpc]
  simp only [bind_assoc]; apply bind_congr_of_forall_mem_support
  intro upperStart path
  have ⟨last,loopPC⟩ := packed_parent_segment_post 284808 4194176 127 0 _ regs
    (by simpa [packedParentPC] using startpc) path
  have atLoop : upperStart.pc=GroupedUpper.loopBase := loopPC
  have outPrefix := (packed_sequence_keeps_output _ _ _ path).trans out
  rw [GroupedUpper.upper_loop_run upperStart _ last atLoop]
  simp only [bind_assoc];apply bind_congr_of_forall_mem_support
  intro parents path
  obtain ⟨last,rootPC⟩ := packed_groups_post GroupedUpper.loopBase 32767 128 _ (by decide) (fun _ => atLoop) last path
  have rootPos : parents.pc=811120 := rootPC (by decide)
  have outParent := (wide_parent_full_register _ _ _ _ path).trans outPrefix
  rw [GroupedUpper.execute_packed_root _ rootPos last.heap outParent]
  simp only [bind_assoc,pure_bind,Execution.charge]


def commitTrace (s : MachineState) : OracleComp World Execution := do
  let key ← liftM ($ᵗ Key : ProbComp Key)
  let leaves ← scan N 0 (readyState s key)
  let out ← tailBody leaves
  return ⟨.success,out,519505182,43470847⟩

attribute [local irreducible] tailBody readyState

theorem full_commit (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (215209250+fuel) s true = commitTrace s := by
  rw [show 215209250+fuel=21+(185847807+(29361422+fuel)) by omega,setup_run s e]
  simp only [commitTrace,bind_assoc,pure_bind];apply bind_congr;intro key
  have read := ready_live s e key
  have run := run_scan N 0 _ (by decide) read (29361422+fuel)
  rw [show S (0+N)-S 0=185847807 by decide,show C (0+N)-C 0=431423487 by decide,
    show Q (0+N)-Q 0=35082240 by decide] at run
  rw [run];simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support;intro leaves hit
  have last := scan_post N 0 _ _ (by decide) read hit
  rw [tail_run leaves (by simpa only [Nat.zero_add] using last)]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem commit_of_image (program : Submission) (im : program.image .commit=image)
    (allowance : 215209250≤program.steps .commit) (m : Message) (e : CommitEntry (program.initialState .commit m)) :
    program.run .commit m = commitTrace (program.initialState .commit m) := by
  change execute (program.image .commit) (program.steps .commit) _ true=_
  rw [im, show program.steps .commit=215209250+(program.steps .commit-215209250) by omega]
  exact full_commit _ e _

theorem actual_commit (m : Message) : GroupedArtifact.submission.run .commit m =
    commitTrace (GroupedArtifact.submission.initialState .commit m) :=
  commit_of_image _ exact_image.symm (by decide) m ⟨rfl,rfl,rfl,rfl⟩

theorem commit_resources (m : Message) (z : Execution) (reachable : z∈support (GroupedArtifact.submission.run .commit m)) :
    z.exit=.success ∧ z.cycles=519505182 ∧ z.oracleCalls≤COMMIT_BUDGET := by
  rw [actual_commit] at reachable
  simp only [commitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reachable
  obtain ⟨_,_,_,_,_,_,rfl⟩:=reachable
  exact ⟨rfl,rfl,show 43470847≤COMMIT_BUDGET by decide⟩

end TwoPermutationPrototype.Grouped
