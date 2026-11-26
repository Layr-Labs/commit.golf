import CommitGolfCandidate.LateOpenOutput
import CommitGolfCandidate.LateCheckModel

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv OracleComp

private theorem honestCode (m : Message) (p : Positions) : submission.honestMachine m p =
    (do let c ← submission.run .commit m
        let a ← submission.run .opening ((submission.readCommit c).2,p)
        pure ⟨c.exit == .success && submission.openingSucceeded a,c.cycles,a.cycles,(submission.readProof a).length⟩) := rfl

attribute [local irreducible] Open.result endCommit words cachedLevels lastParent readBuffer

theorem machine_run (o : Oracle) (m : Message) (p : Positions) :
    o.run (submission.honestMachine m p) =
      (do let _ ← words; pure (⟨true,911802772,Open.cycles p.card,Open.outputSize p.card⟩,83886079)) := by
  rw [honestCode,oracle_run_bind,full_commit_run,bind_assoc]
  apply bind_congr
  intro ws
  let c := endCommit o m ws
  let t := (submission.readCommit c).2
  simp only [pure_bind,Open.open_execution,oracle_run_pure,Nat.zero_add,Nat.add_zero]
  rw [Open.succeeded,Open.read_length]
  simp only [endCommit,Open.result,beq_self_eq_true,Bool.true_and]

theorem machine_success : submission.MachineSuccess := by
  intro o m p
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reached
  rw [machine_run,mem_support_bind_iff] at reached
  obtain ⟨ws,_,h⟩ := reached
  rw [support_pure,Set.mem_singleton_iff] at h;subst r;rfl

theorem prover_cycles : submission.ProverCycles 911802772 45875 := by
  intro o m p batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reached
  rw [machine_run,mem_support_bind_iff] at reached
  obtain ⟨ws,_,h⟩ := reached
  rw [support_pure,Set.mem_singleton_iff] at h;subst r
  change 911802772≤911802772 ∧ Open.cycles p.card≤45875
  rw [batch]; decide

theorem open_scheme_run (o : Oracle) (t : Trapdoor) (p : Positions) :
    o.run (submission.scheme.opening t p) = pure (submission.readProof (Open.result t p),0) := by
  change o.run (submission.readProof <$> submission.run .opening (t,p)) = _
  rw [Open.open_execution,map_pure,oracle_run_pure]

theorem open_terminates (o : Oracle) (t : Trapdoor) (p : Positions) :
    Pr{let e ← o.run (submission.run .opening (t,p))}[e.1.exit ≠ Exit.unfinished] = 1 := by
  rw [Open.open_execution,oracle_run_pure]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reach;rw [support_pure,Set.mem_singleton_iff] at reach;subst r
  unfold Open.result
  exact (by decide : Exit.success≠Exit.unfinished)

def honestInput (o : Oracle) (m : Message) (ws : List PairCoins) (p : Positions) : CheckInput :=
  let ls := cachedLevels o m ws
  ⟨node ls LOG_LENGTH 0,p,m.restrict p,opening ls (wordTape ws) p⟩

theorem proof_of_tape (o : Oracle) (m : Message) (ws : List PairCoins) (member : ws ∈ support words) (p : Positions) :
    submission.readProof (Open.result (trapdoorOf o m ws) p) = opening (cachedLevels o m ws) (wordTape ws) p := by
  unfold trapdoorOf cachedLevels
  exact Open.read_payload _ _ _ _ (committed_trapdoor o m ws (words_length ws member))

theorem honest_distribution (o : Oracle) (m : Message) (p : Positions) :
    submission.scheme.honest o m p =
      (do let ws ← words
          let checks := Check.evaluation o (honestInput o m ws p)
          pure ⟨checks.1,83886079,0,checks.2,Open.outputSize p.card⟩) := by
  unfold Scheme.honest
  rw [commit_scheme_run,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,open_scheme_run]
  rw [Open.read_length,proof_of_tape o m ws mem p]
  rfl

theorem proof_size : submission.scheme.ProofSize 72704 := by
  intro o m p batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r reached
  rw [honest_distribution,mem_support_bind_iff] at reached
  obtain ⟨ws,_,h⟩ := reached
  rw [support_pure,Set.mem_singleton_iff] at h;subst r
  change Open.outputSize p.card≤72704;rw [batch];decide

theorem view_refinement : ViewRefinement := by
  intro o m p
  have first : view o (submission.scheme.commit m) =
      (do let ws ← words; pure (node (cachedLevels o m ws) LOG_LENGTH 0,trapdoorOf o m ws)) := by
    rw [view,commit_scheme_run,map_bind];simp only [map_pure]
  have second (td : Trapdoor) : view o (submission.scheme.opening td p) =
      pure (submission.readProof (Open.result td p)) := by rw [view,open_scheme_run,map_pure]
  unfold transcript
  rw [view_bind,first,bind_assoc,view_bind,reference_commit_view,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,view_bind,second,view_pure]
  rw [proof_of_tape o m ws mem p]
  change _ = (view o (pure _ : OracleComp World Proof) >>= _)
  rw [view_pure,pure_bind]

end CommitGolfCandidate.Late
