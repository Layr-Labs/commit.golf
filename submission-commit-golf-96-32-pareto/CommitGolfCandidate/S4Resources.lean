import CommitGolfCandidate.LateCommitFacts
import CommitGolfCandidate.S4HonestFields
import CommitGolfCandidate.S4CheckSystem
import CommitGolfCandidate.S4Binding
namespace CommitGolfCandidate.S4
open CommitGolf CommitGolf.Riscv OracleComp
open Late (Trapdoor TrapdoorAgrees Levels SaltTape words wordTape endCommit cachedLevels trapdoorOf)

structure OpeningLaw where
  result : Trapdoor→Positions→Execution
  run : ∀ td ps,Late.submission.run .opening (td,ps)=pure (result td ps)
  success : ∀ td ps,Late.submission.openingSucceeded (result td ps)=true
  exit : ∀ td ps,(result td ps).exit=.success
  priced : ∀ td (ps : Positions),ps.card=BATCH → (result td ps).cycles≤85548
  output : ∀ td t s ps,TrapdoorAgrees td t s → Late.submission.readProof (result td ps)=opening .byte t s ps

structure CheckLaw : Prop where
  terminates : ∀ o i, (Machine.checkEvaluation o (Late.submission.run .check i)).1.exit≠.unfinished
  valid : ∀ o i,accepted o i ↔ wireValid o.compression i
  calls : ∀ (o : Oracle) (i : CheckInput),
    (o.eval (Late.submission.scheme.check i.commitment i.positions i.values i.proof)).2≤CHECK_BUDGET i.positions.card

attribute [local irreducible] endCommit words readBuffer S4Hiding.tree

theorem openScheme (op : OpeningLaw) (o : Oracle) (t : Trapdoor) (ps : Positions) :
    o.run (Late.submission.scheme.opening t ps)=pure (Late.submission.readProof (op.result t ps),0) := by
  change o.run (Late.submission.readProof <$> Late.submission.run .opening (t,ps))=_
  rw [op.run,map_pure,oracle_run_pure]

theorem proofOfTape (op : OpeningLaw) (o : Oracle) (m : Message) (ws : List Late.PairCoins)
    (mem : ws∈support words) (ps : Positions) :
    Late.submission.readProof (op.result (trapdoorOf o m ws) ps)=opening .byte (cachedLevels o m ws) (wordTape ws) ps :=
  op.output _ _ _ _ (Late.committed_trapdoor o m ws (Late.words_length ws mem))

theorem machineHiding (op : OpeningLaw) : Late.submission.scheme.Hiding HIDING_ERROR := by
  apply S4Hiding.machine_hiding Late.submission.scheme.check
  intro o m p
  suffices same : fixedOracleRun o (S4Hiding.transcript Late.submission.scheme m p)=
      fixedOracleRun o (S4Hiding.transcript (scheme active Late.submission.scheme.check) m p) by rw [same]
  rw [S4Hiding.model_transcript_run,Late.sampled_tape_view]
  unfold S4Hiding.transcript
  change Late.view o _=_
  rw [Late.view_bind]
  have fromCommit : Late.view o (Late.submission.scheme.commit m)=
      (do let ws←words;pure (Late.node (cachedLevels o m ws) LOG_LENGTH 0,trapdoorOf o m ws)) := by
    rw [Late.view,Late.commit_scheme_run,map_bind];simp only [map_pure]
  rw [fromCommit,bind_assoc,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  simp only [pure_bind,Late.view_bind,Late.view_pure]
  have openView (td : Trapdoor) : Late.view o (Late.submission.scheme.opening td p)=
      pure (Late.submission.readProof (op.result td p)):=by rw [Late.view,openScheme op,map_pure]
  rw [openView,pure_bind,proofOfTape op o m ws mem p];rfl

end CommitGolfCandidate.S4
