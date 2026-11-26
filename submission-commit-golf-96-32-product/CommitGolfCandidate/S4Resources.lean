import CommitGolfCandidate.LateTrapdoor
import CommitGolfCandidate.S4HonestFields
import CommitGolfCandidate.S4CheckSystem
import CommitGolfCandidate.S4Binding
namespace CommitGolfCandidate.S4
open CommitGolf CommitGolf.Riscv OracleComp
open Late (Trapdoor TrapdoorAgrees Levels SaltTape)

structure OpeningLaw where
  result : Trapdoor→Positions→Execution
  run : ∀ td ps,Late.submission.run .opening (td,ps)=pure (result td ps)
  success : ∀ td ps,Late.submission.openingSucceeded (result td ps)=true
  exit : ∀ td ps,(result td ps).exit=.success
  priced : ∀ td (ps : Positions),ps.card=BATCH → (result td ps).cycles≤96415
  output : ∀ td t s ps,TrapdoorAgrees td t s → Late.submission.readProof (result td ps)=actualOpening t s ps

structure CheckLaw : Prop where
  terminates : ∀ o i, (Machine.checkEvaluation o (Late.submission.run .check i)).1.exit≠.unfinished
  valid : ∀ o i,accepted o i ↔ wireValid o.compression (wideInput i)
  calls : ∀ (o : Oracle) (i : CheckInput),
    (o.eval (Late.submission.scheme.check i.commitment i.positions i.values i.proof)).2≤CHECK_BUDGET i.positions.card

theorem openScheme (op : OpeningLaw) (o : Oracle) (t : Trapdoor) (ps : Positions) :
    o.run (Late.submission.scheme.opening t ps)=pure (Late.submission.readProof (op.result t ps),0) := by
  change o.run (Late.submission.readProof <$> Late.submission.run .opening (t,ps))=_
  rw [op.run,map_pure,oracle_run_pure]

end CommitGolfCandidate.S4
