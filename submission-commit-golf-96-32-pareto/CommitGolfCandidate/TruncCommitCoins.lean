import CommitGolfCandidate.TruncBodyEval
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 240000
attribute [local irreducible] checkEvaluation parentProgram fixedParents commitLeaves

attribute [local irreducible] commitBody commitInputReady

private def packCommitResult (body : MachineState × Nat) : Execution × Nat :=
  (⟨.success,body.1,963641394,5*LENGTH-1⟩,body.2)

noncomputable def commitFinalResult (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) : Execution × Nat :=
  packCommitResult (checkEvaluation o (commitBody (commitInputReady m a)))

private theorem packState (r : MachineState×Nat) : (packCommitResult r).1.state=r.1 := rfl

private theorem initialEq (m : Message) : submission.initialState .commit m=CommitGolfCandidate.submission.initialState .commit m := rfl

private noncomputable def saltOutcome (o : Oracle) (m : Message) (initial : MachineState) : ProbComp (Execution×Nat) := do
  let a ← ($ᵗ BitVec (8*((commitSetupState initial).getReg .x11).toNat) : ProbComp _)
  pure (commitFinalResult o m a)

private theorem sampleBody (o : Oracle) (n : Nat) (body : BitVec n→OracleComp World MachineState)
    (det : ∀ a,o.run (body a)=pure (checkEvaluation o (body a))) :
    o.run (do let a←(liftM ($ᵗ BitVec n : ProbComp (BitVec n)) : OracleComp World (BitVec n))
              let t←body a
              return (⟨.success,t,963641394,5*2^24-1⟩ : Execution)) =
    (($ᵗ BitVec n : ProbComp (BitVec n)) >>= fun a=>pure (packCommitResult (checkEvaluation o (body a)))) := by
  rw [oracle_run_coins_bind]
  simp only [oracle_run_bind,det,pure_bind,oracle_run_pure,Nat.add_zero,packCommitResult]
  rfl

theorem commit_run_distribution (o : Oracle) (m : Message) :
    o.run (submission.run .commit m)=(commitSaltCoins m >>= fun a=>pure (commitFinalResult o m a)) := by
  have law : o.run (commitExecution m)=saltOutcome o m (submission.initialState .commit m) :=
    sampleBody o (8*((commitSetupState (submission.initialState .commit m)).getReg .x11).toNat)
      (fun a=>commitBody (commitInputReady m a)) (fun a=>bodyDet o (commitInputReady m a))
  exact ((congrArg (fun p : OracleComp World Execution=>o.run p) (commit_execution m)).trans law).trans
    (congrArg (saltOutcome o m) (initialEq m))

private theorem finalState (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) :
    (commitFinalResult o m a).1.state=returned o m a :=
  (packState (checkEvaluation o (commitBody (commitInputReady m a)))).trans (bodyExact o m a)

private theorem transfer {o : Oracle} {m : Message} {s t : MachineState} {a : BitVec (128*LENGTH)}
    (eqn : s=t) (ok : CommittedState o m t) (src : ∀ i : Index,readBuffer t (5905584160+16*i.val) 16=a.extractLsb' (128*i.val) 128) :
    CommittedState o m s ∧ ∀ i : Index,readBuffer s (5905584160+16*i.val) 16=a.extractLsb' (128*i.val) 128 := by
  subst s;exact ⟨ok,src⟩

attribute [local irreducible] commitFinalResult returned CommittedState readBuffer in
theorem commit_final_origin (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) (width : bits=128*LENGTH) :
    CommittedState o m (commitFinalResult o m a).1.state ∧
    ∀ i : Index,readBuffer (commitFinalResult o m a).1.state (5905584160+16*i.val) 16=a.extractLsb' (128*i.val) 128 := by
  subst bits
  exact transfer (finalState o m a) (returnedTruth o m a) (outputSalt o m a)

end CommitGolfCandidate.Trunc
