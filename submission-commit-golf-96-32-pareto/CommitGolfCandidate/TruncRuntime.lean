import CommitGolfCandidate.TruncEnter
import CommitGolfCandidate.TruncExit
import CommitGolfCandidate.TruncLeaves
import CommitGolfCandidate.TruncCommitRun
import CommitGolfCandidate.CommitInput
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 14000
set_option maxHeartbeats 400000
attribute [local irreducible] execute

theorem parentsSupportFrame (q : Nat) (s t : MachineState) (f : ParentFrame q s) (h : t∈support (parentProgram q s)) :
    ParentFrame 0 t := by
  induction q generalizing s with
  | zero =>
    simp only [parentProgram,support_pure,Set.mem_singleton_iff] at h
    exact h ▸ f
  | succ q ih =>
    rw [parentProgram,mem_support_bind_iff] at h
    obtain ⟨v,_,tail⟩:=h
    exact ih _ (advanceFrame (q+1) (by omega) s v f) tail

theorem rootRun (s : MachineState) (f : ParentFrame 0 s) (fuel : Nat) :
    execute (submission.image .commit) (11+fuel) s true=pure ⟨.success,commitExitState (commitRootCopyState s),11,0⟩ := by
  have src : ∀ w : Fin 4,accessValid (s.getReg .x9+BitVec.ofNat 64 (32+8*w.val)) 8 := by
    rw [f.pointers.heap];decide
  have dst : ∀ w : Fin 4,accessValid (s.getReg .x26+BitVec.ofNat 64 (8*w.val)) 8 := by
    rw [f.root];decide
  have pc : s.pc=7236:=f.pc
  have nextPC : (commitRootCopyState s).pc=7268 := by rw [commit_root_copy_pc,pc];rfl
  rw [show 11+fuel=8+(3+fuel) by omega,commit_root_copy s pc src dst,commit_exit _ nextPC]
  rfl

theorem readyFrame (m : Message) {bits : Nat} (ans : BitVec bits) (t : MachineState)
    (h : t∈support (commitLeaves (commitInputReady m ans) (2^19))) : ParentFrame (2^24-1) (enterState t) := by
  let s:=commitInputReady m ans
  have l:=commit_input_leaves m ans
  obtain ⟨pc,hp,keep⟩:=commit_leaves_finished s (2^19) l t h
  have r:=commit_input_registers m ans
  apply enterFrame t pc
  · exact (keep .x9 (by decide)).trans r.2.1
  · rw [hp,r.2.2.2.1];rfl
  · exact (keep .x26 (by decide)).trans r.2.2.2.2.1
  · exact (keep .x5 (by decide)).trans l.r5
  · exact (keep .x11 (by decide)).trans l.r11
  · exact (keep .x13 (by decide)).trans l.r13

def commitBody (s : MachineState) : OracleComp World MachineState := do
  let l←commitLeaves s (2^19)
  let t←parentProgram (2^24-1) (enterState l)
  return commitExitState (commitRootCopyState t)

attribute [local irreducible] parentProgram commitLeaves commitRootCopyState enterState

private theorem runTree (s : MachineState) (n q fuel : Nat) (inv : CommitLeavesInvariant s n) (small : q<2^24)
    (pc : ∀ l∈support (commitLeaves s n),l.pc=6420)
    (frame : ∀ l∈support (commitLeaves s n),ParentFrame q (enterState l)) :
    execute (submission.image .commit) (547*n+(18+(treeSteps q+(11+fuel)))) s true =
      (do let l←commitLeaves s n
          let t←parentProgram q (enterState l)
          return ⟨.success,commitExitState (commitRootCopyState t),1443*n+(18+(treeSteps q+7*q+11)),128*n+q⟩) := by
  rw [Trunc.commit_leaves s n inv]
  apply bind_congr_of_forall_mem_support
  intro l lh
  rw [enterRun l (pc l lh) _ true,parent_exec q small (enterState l) (frame l lh)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro t th
  rw [rootRun t (parentsSupportFrame _ _ t (frame l lh) th)]
  simp only [pure_bind,Execution.charge,Nat.add_zero,Nat.zero_add] <;> rfl

theorem bodyRun (m : Message) {bits : Nat} (ans : BitVec bits) (fuel : Nat) :
    execute (submission.image .commit) (342884375+fuel) (commitInputReady m ans) true =
      (do let t←commitBody (commitInputReady m ans);return ⟨.success,t,930086928,83886079⟩) := by
  let s:=commitInputReady m ans
  have split : 342884375+fuel=547*2^19+(18+(treeSteps (2^24-1)+(11+fuel))) := by
    have exactSteps : treeSteps (2^24-1)=56098810 := by decide
    omega
  have run:=runTree s (2^19) (2^24-1) fuel (commit_input_leaves m ans) (by decide)
    (fun l h=>(commit_leaves_finished s (2^19) (commit_input_leaves m ans) l h).1) (readyFrame m ans)
  rw [split,run]
  simp only [commitBody,bind_assoc,pure_bind]
  rfl

private theorem addReadyCharge (p : OracleComp World MachineState) (c k : Nat) :
    (do let r←(do let x←p;return (⟨.success,x,c,k⟩ : Execution));return r.charge 4 0) =
      (do let x←p;return (⟨.success,x,4+c,k⟩ : Execution)) := by
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add]

private theorem readyCost {fuel n : Nat} (w : MachineState) (pc : w.pc=4216) (doneP : OracleComp World MachineState)
    (h : execute (submission.image .commit) (n+fuel) (commitReadyState w) true=
      (do let t←doneP;return ⟨.success,t,930086928,83886079⟩)) :
    execute (submission.image .commit) (4+(n+fuel)) w true=
      (do let t←doneP;return ⟨.success,t,930086932,83886079⟩) := by
  apply (Trunc.commit_ready w pc (n+fuel)).trans
  apply (congrArg (fun p : OracleComp World Execution=>p >>= fun r=>pure (r.charge 4 0)) h).trans
  exact addReadyCharge doneP 930086928 83886079

private theorem initialCommit (m : Message) : submission.initialState .commit m=CommitGolfCandidate.submission.initialState .commit m := rfl

theorem afterRandom (m : Message) {bits : Nat} (ans : BitVec bits) (fuel : Nat) :
    let setup:=commitSetupState (submission.initialState .commit m)
    execute (submission.image .commit) (4+(342884375+fuel)) (writeBits setup (setup.getReg .x10) ans) true =
      (do let t←commitBody (commitInputReady m ans);return ⟨.success,t,930086932,83886079⟩) := by
  dsimp only
  rw [initialCommit]
  let setup:=commitSetupState (CommitGolfCandidate.submission.initialState .commit m)
  let w:=writeBits setup (setup.getReg .x10) ans
  have pc : w.pc=4216 := by rw [show w.pc=setup.pc+4 from writeBits_pc _ _ _,commit_setup_pc _ rfl];rfl
  exact readyCost w pc _ (bodyRun m ans fuel)

def commitExecution (message : Message) : OracleComp World Execution := do
  let setup := commitSetupState (submission.initialState .commit message)
  let answer ← liftM ($ᵗ BitVec (8 * (setup.getReg .x11).toNat) :
    ProbComp (BitVec (8 * (setup.getReg .x11).toNat)))
  let finished ← commitBody (commitInputReady message answer)
  return ⟨.success, finished, 963641394, 5 * 2 ^ 24 - 1⟩

set_option maxRecDepth 4096 in
/-- Exact execution from the real ABI, including salt generation and all setup. -/
theorem commit_execute (message : Message) (fuel : Nat) :
    execute (submission.image .commit) (342884409 + fuel)
      (submission.initialState .commit message) true = commitExecution message := by
  let initial := submission.initialState .commit message
  let setup := commitSetupState initial
  have regs := commit_setup_registers initial
  have setupPC : setup.pc = 4212 := commit_setup_pc initial rfl
  have valid : randomArgumentsValid setup = true := by
    unfold randomArgumentsValid
    rw [regs.2.2.2.1, regs.2.2.2.2.1]
    have heap : initial.getReg .x12 = (4294971424 : Word) := rfl
    rw [heap]
    have sum : (4294971424 : Word) + 1610612736 = 5905584160#64 := rfl
    rw [sum]
    rfl
  rw [show 342884409 + fuel = 29 + (1 + (4 + (342884375 + fuel))) by omega,
    commit_setup _ rfl, commit_random setup setupPC regs.1 valid]
  simp only [commitExecution, bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  rw [afterRandom message answer fuel]
  simp only [bind_assoc, pure_bind, commitInputReady]
  apply congrArg (fun continuation => commitBody (commitReadyState
    (writeBits setup (setup.getReg .x10) answer)) >>= continuation)
  funext finished
  have bytes : (setup.getReg .x11).toNat = 268435456 := by rw [regs.2.2.2.2.1]; rfl
  simp only [Execution.charge, bytes]
  rfl

private theorem run_commit (candidate : Submission) (message : Message) :
    candidate.run .commit message = execute (candidate.image .commit) (candidate.steps .commit)
      (candidate.initialState .commit message) true := rfl

/-- The submitted commitment's full instruction allowance reaches the exact
successful execution above. -/
theorem commit_execution (message : Message) : submission.run .commit message = commitExecution message := by
  rw [run_commit]
  have allowance : submission.steps .commit = 342884409 + 8247051207 := by decide
  rw [allowance, commit_execute]

/-- Exact machine resources for every commitment, before interpreting oracle calls. -/
theorem commit_input_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 963641394 ∧ result.oracleCalls = 83886079 := by
  rw [commit_execution] at reachable
  simp only [commitExecution, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, finished, _, rfl⟩ := reachable
  exact ⟨rfl, rfl, rfl⟩

end CommitGolfCandidate.Trunc
