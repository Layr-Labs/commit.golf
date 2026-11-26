import CommitGolfCandidate.LateOpenOutput
import CommitGolfCandidate.LateCheckModel

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv OracleComp

private theorem honestCode (m : Message) (p : Positions) : submission.honestMachine m p =
    (do let c ← submission.run .commit m
        let a ← submission.run .opening ((submission.readCommit c).2,p)
        pure ⟨c.exit == .success && submission.openingSucceeded a,c.cycles,a.cycles,(submission.readProof a).length⟩) := rfl

attribute [local irreducible] Open.result endCommit words cachedLevels lastParent readBuffer

private theorem exactCommit (o : Oracle) (m : Message) :
    o.run (Artifact.submission.run .commit m)= (do let ws←words;pure (endCommit o m ws,83886079)) :=
  full_commit_run o m
private theorem exactOpen (t : Trapdoor) (p : Positions) :
    Artifact.submission.run .opening (t,p)=pure (Open.result t p) := Open.open_execution t p

theorem machine_run (o : Oracle) (m : Message) (p : Positions) :
    o.run (CommitGolf.Artifact.submission.honestMachine m p) =
      (do let _ ← words; pure (⟨true,919142745,Open.wireCycles p.card,Open.wireSize p.card⟩,83886079)) := by
  have code : Artifact.submission.honestMachine m p=submission.honestMachine m p := rfl
  rw [code,honestCode,oracle_run_bind,full_commit_run,bind_assoc]
  apply bind_congr;intro ws
  simp only [pure_bind,Open.open_execution,oracle_run_pure,Nat.zero_add,Nat.add_zero]
  rw [Open.succeeded,Open.read_length]
  simp only [endCommit,Open.result,beq_self_eq_true,Bool.true_and]

theorem machine_success : CommitGolf.Artifact.submission.MachineSuccess := by
  intro o m p
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reached
  rw [machine_run,mem_support_bind_iff] at reached
  obtain ⟨ws,_,h⟩ := reached
  rw [support_pure,Set.mem_singleton_iff] at h;subst r;rfl

theorem prover_cycles : CommitGolf.Artifact.submission.ProverCycles 919142745 116041 := by
  intro o m p batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reached
  rw [machine_run,mem_support_bind_iff] at reached
  obtain ⟨ws,_,h⟩ := reached
  rw [support_pure,Set.mem_singleton_iff] at h;subst r
  change 919142745≤919142745 ∧ Open.wireCycles p.card≤116041
  rw [batch]; decide

theorem open_scheme_run (o : Oracle) (t : Trapdoor) (p : Positions) :
    o.run (CommitGolf.Artifact.submission.scheme.opening t p) = pure (CommitGolf.Artifact.submission.readProof (Open.result t p),0) := by
  change o.run (CommitGolf.Artifact.submission.readProof <$> CommitGolf.Artifact.submission.run .opening (t,p)) = _
  rw [exactOpen,map_pure,oracle_run_pure]

theorem open_terminates (o : Oracle) (t : Trapdoor) (p : Positions) :
    Pr{let e ← o.run (CommitGolf.Artifact.submission.run .opening (t,p))}[e.1.exit ≠ Exit.unfinished] = 1 := by
  rw [exactOpen,oracle_run_pure]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reach;rw [support_pure,Set.mem_singleton_iff] at reach;subst r
  unfold Open.result
  exact (by decide : Exit.success≠Exit.unfinished)

def actualEvaluation (o : Oracle) (x : CheckInput) := o.eval (Artifact.submission.scheme.check x.commitment x.positions x.values x.proof)

def honestInput (o : Oracle) (m : Message) (ws : List PairCoins) (p : Positions) : CheckInput :=
  let ls := cachedLevels o m ws
  ⟨node ls LOG_LENGTH 0,p,m.restrict p,opening ls (wordTape ws) p⟩

theorem proof_of_tape (o : Oracle) (m : Message) (ws : List PairCoins) (member : ws ∈ support words) (p : Positions) :
    CommitGolf.Artifact.submission.readProof (Open.result (trapdoorOf o m ws) p) = opening (cachedLevels o m ws) (wordTape ws) p := by
  unfold trapdoorOf cachedLevels
  exact Open.read_payload _ _ _ _ (committed_trapdoor o m ws (words_length ws member))

private theorem actualSchemeCommit (o : Oracle) (m : Message) :
    o.run (Artifact.submission.scheme.commit m)=
      (do let ws←words;return ((node (cachedLevels o m ws) LOG_LENGTH 0,trapdoorOf o m ws),83886079)) :=
  commit_scheme_run o m
private theorem actualLength (t : Trapdoor) (p : Positions) :
    (Artifact.submission.readProof (Open.result t p)).length=Open.wireSize p.card := Open.read_length t p

theorem honest_distribution (o : Oracle) (m : Message) (p : Positions) :
    CommitGolf.Artifact.submission.scheme.honest o m p =
      (do let ws ← words
          let checks := actualEvaluation o (honestInput o m ws p)
          pure ⟨checks.1,83886079,0,checks.2,Open.wireSize p.card⟩) := by
  unfold Scheme.honest
  rw [actualSchemeCommit,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,open_scheme_run]
  rw [actualLength,proof_of_tape o m ws mem p]
  rfl

theorem proof_size : CommitGolf.Artifact.submission.scheme.ProofSize 69120 := by
  intro o m p batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reached
  rw [honest_distribution,mem_support_bind_iff] at reached
  obtain ⟨ws,_,h⟩ := reached
  rw [support_pure,Set.mem_singleton_iff] at h;subst r
  change Open.wireSize p.card≤69120;rw [batch];decide

theorem view_refinement : ViewRefinement := by
  intro o m p
  have first : view o (CommitGolf.Artifact.submission.scheme.commit m) =
      (do let ws ← words; pure (node (cachedLevels o m ws) LOG_LENGTH 0,trapdoorOf o m ws)) := by
    rw [view,actualSchemeCommit,map_bind];simp only [map_pure]
  have second (td : Trapdoor) : view o (CommitGolf.Artifact.submission.scheme.opening td p) =
      pure (CommitGolf.Artifact.submission.readProof (Open.result td p)) := by rw [view,open_scheme_run,map_pure]
  unfold transcript
  rw [view_bind,first,bind_assoc,view_bind,reference_commit_view,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,view_bind,second,view_pure]
  rw [proof_of_tape o m ws mem p]
  change _ = (view o (pure _ : OracleComp World Proof) >>= _)
  rw [view_pure,pure_bind]

end CommitGolfCandidate.Late
