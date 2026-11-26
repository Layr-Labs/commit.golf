import CommitGolfCandidate.LateTrapdoor
import CommitGolfCandidate.LateFixed
import CommitGolfCandidate.S4HidingTransfer

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv OracleComp

def cachedLevels (o : Oracle) (m : Message) (ws : List PairCoins) : Levels :=
  S4Hiding.tree o.compression m (wordTape ws)

def trapdoorOf (o : Oracle) (m : Message) (ws : List PairCoins) : Trapdoor :=
  (submission.readCommit (endCommit o m ws)).2

theorem commit_support (o : Oracle) (m : Message) (e : Execution × Nat)
    (reach : e ∈ support (o.run (submission.run .commit m))) :
    ∃ ws ∈ support words, e = (endCommit o m ws,78293686) := by
  rw [full_commit_run,mem_support_bind_iff] at reach
  simpa only [support_pure,Set.mem_singleton_iff] using reach

theorem commit_terminates (o : Oracle) (m : Message) :
    Pr{let e ← o.run (submission.run .commit m)}[e.1.exit ≠ Exit.unfinished] = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro e reach
  obtain ⟨ws,_,rfl⟩ := commit_support o m e reach
  exact (by decide : Exit.success ≠ Exit.unfinished)

attribute [local irreducible] List.range endCommit treeM node

theorem commit_scheme_run (o : Oracle) (m : Message) :
    o.run (submission.scheme.commit m) =
      (do let ws ← words; return ((node (cachedLevels o m ws) LOG_LENGTH 0,trapdoorOf o m ws),78293686)) := by
  change o.run (submission.readCommit <$> submission.run .commit m) = _
  rw [oracle_run_map,full_commit_run,map_bind]
  apply bind_congr_of_forall_mem_support
  intro ws member
  rw [map_pure]
  unfold cachedLevels
  exact congrArg (fun root => pure ((root,trapdoorOf o m ws),78293686))
    (committed_root o m ws (words_length ws member))

theorem sampled_tape_view (o : Oracle) :
    fixedOracleRun o sampleSalts=(do let ws←words;pure (wordTape ws)) := by
  have coins {α : Type} (x : ProbComp α) : view o (liftM x : OracleComp World α)=x := by
    simp only [view,oracle_run_coins,Functor.map_map];exact id_map _
  change view o _=_
  unfold sampleSalts words
  rw [lift_draws,view_bind,coins]
  exact bind_congr (fun ws=>view_pure o (wordTape ws))

end CommitGolfCandidate.Late
