import CommitGolfCandidate.S5BatchOpen
import CommitGolfCandidate.S5NormalOpen
import CommitGolfCandidate.S5CommittedTrapdoor
import CommitGolfCandidate.S5HidingTransfer
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (PairCoins Levels SaltTape node)
open Open (WireFits)
attribute [local irreducible] List.range readBuffer endCommit S5.opening S5Hiding.tree

structure Opened (td : Trapdoor) (ps : Positions) (e : Execution) : Prop where
  run : Artifact.submission.run .opening (td,ps)=pure e
  success : Artifact.submission.openingSucceeded e=true
  exit : e.exit=.success
  calls : e.oracleCalls=0
  price : ps.card=BATCH → e.cycles≤191023

theorem opening_exists (td : Trapdoor) (ps : Positions) : ∃ e,Opened td ps e := by
  let tree:=Open.rawLevels td
  let salt:=Open.rawSalts td
  have good:=Open.raw_agrees td
  by_cases b : ps.card=BATCH
  · obtain ⟨e,run,exit,ok,zero,cost,_⟩:=Open.batch_open td ps tree salt good b
    exact ⟨e,run,ok,exit,zero,fun _=>cost.trans_le (Writer.batch_bound (Open.indices ps) ((Finset.length_sort ..).trans b))⟩
  · obtain ⟨e,run,exit,ok,zero,_⟩:=Open.normal_open td ps tree salt good b
    exact ⟨e,run,ok,exit,zero,fun h=>False.elim (b h)⟩

noncomputable def opened (td : Trapdoor) (ps : Positions) := (opening_exists td ps).choose
theorem open_law (td : Trapdoor) (ps : Positions) : Opened td ps (opened td ps):=(opening_exists td ps).choose_spec

theorem open_output (td : Trapdoor) (ps : Positions) (tree : Levels) (salt : SaltTape) (agree : TrapdoorAgrees td tree salt)
    (fit : WireFits tree) : Artifact.submission.readProof (opened td ps)=S5.opening tree salt ps := by
  have real:=open_law td ps
  have identify {e : Execution} (run : Artifact.submission.run .opening (td,ps)=pure e) : opened td ps=e := by
    simpa only [pure_inj] using real.run.symm.trans run
  by_cases b : ps.card=BATCH
  · obtain ⟨e,run,_,_,_,_,out⟩:=Open.batch_open td ps tree salt agree b
    rw [identify run];exact out fit
  · obtain ⟨e,run,_,_,_,out⟩:=Open.normal_open td ps tree salt agree b
    rw [identify run];exact out

noncomputable def cachedLevels (o : Oracle) (m : Message) (ws : List PairCoins) := S5Hiding.tree o.compression m (wordTape ws)
noncomputable def trapdoorOf (o : Oracle) (m : Message) (ws : List PairCoins) := (Artifact.submission.readCommit (endCommit o m ws)).2

theorem proof_of_tape (o : Oracle) (m : Message) (ws : List PairCoins) (mem : ws∈support coinTape) (ps : Positions) :
    Artifact.submission.readProof (opened (trapdoorOf o m ws) ps)=S5.opening (cachedLevels o m ws) (wordTape ws) ps :=
  open_output _ _ _ _ (committed_trapdoor o m ws (words_length ws mem)) (Open.honest_fits o.compression m (wordTape ws))

theorem open_scheme (o : Oracle) (td : Trapdoor) (ps : Positions) :
    o.run (Artifact.submission.scheme.opening td ps)=pure (Artifact.submission.readProof (opened td ps),0) := by
  change o.run (Artifact.submission.readProof <$> Artifact.submission.run .opening (td,ps))=_
  rw [(open_law td ps).run,map_pure,oracle_run_pure]

theorem commit_scheme_run (o : Oracle) (m : Message) :
    o.run (Artifact.submission.scheme.commit m) =
      (do let ws←coinTape;return ((node (cachedLevels o m ws) LOG_LENGTH 0,trapdoorOf o m ws),78427694)) := by
  change o.run (Artifact.submission.readCommit <$> Artifact.submission.run .commit m)=_
  rw [oracle_run_map,full_commit_run,map_bind]
  apply bind_congr_of_forall_mem_support
  intro ws member
  rw [map_pure]
  exact congrArg (fun root=>pure ((root,trapdoorOf o m ws),78427694)) (committed_root o m ws (words_length ws member))

theorem salts_view (o : Oracle) : fixedOracleRun o Late.sampleSalts=(do let ws←coinTape;pure (wordTape ws)) := by
  unfold Late.sampleSalts coinTape
  rw [Late.lift_draws,LateHiding.run_coins_bind]
  exact bind_congr (fun ws=>fixed_oracle_run_pure o (wordTape ws))

theorem machine_hiding : Artifact.submission.scheme.Hiding HIDING_ERROR := by
  apply S5Hiding.machine_hiding Artifact.submission.scheme.check
  intro o m ps
  suffices eq : fixedOracleRun o (S5Hiding.transcript Artifact.submission.scheme m ps)=
      fixedOracleRun o (S5Hiding.transcript (S5.scheme Artifact.submission.scheme.check) m ps) by rw [eq]
  rw [S5Hiding.model_transcript_run,salts_view]
  unfold S5Hiding.transcript
  rw [LateHiding.run_bind]
  have first : fixedOracleRun o (Artifact.submission.scheme.commit m)=
      (do let ws←coinTape;pure (node (cachedLevels o m ws) LOG_LENGTH 0,trapdoorOf o m ws)) := by
    rw [fixedOracleRun,commit_scheme_run,map_bind];simp only [map_pure]
  rw [first,bind_assoc,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,LateHiding.run_bind,fixed_oracle_run_pure]
  have opening (td : Trapdoor) : fixedOracleRun o (Artifact.submission.scheme.opening td ps)=
      pure (Artifact.submission.readProof (opened td ps)):=by rw [fixedOracleRun,open_scheme,map_pure]
  rw [opening,pure_bind,proof_of_tape o m ws mem ps];rfl
end CommitGolfCandidate.S5Machine
