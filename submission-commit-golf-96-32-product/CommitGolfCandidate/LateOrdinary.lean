import CommitGolfCandidate.LateHidingGame
import CommitGolfCandidate.LateOrdinaryCompare
import CommitGolfCandidate.LateContract

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem rows (o : Oracle) (x : CheckInput) (normal : x.positions.card≠BATCH) (remaining r : Nat)
    (total : r+remaining=x.positions.card) (s : MachineState) (row : RowState x r s) :
    ∃ n q ex, n≤1300*remaining+3 ∧ q≤28*remaining ∧ ex≠.unfinished ∧ Finishes o s n q ex ∧
      (ex=.success ↔ ∀ j, r≤j → j<x.positions.card → lower o.compression x j 24=x.commitment) := by
  induction remaining generalizing r s with
  | zero =>
    have done : r=x.positions.card := by omega
    have pc:=row.position.trans (if_pos done)
    refine ⟨3,0,.success,by decide,by decide,by decide,?_,?_⟩
    · intro f;unfold obs;rw [check_exit s true pc f false,check_evaluation_pure];rfl
    · exact ⟨fun _ j lo hi=>False.elim (by omega),fun _=>rfl⟩
  | succ n ih =>
    have hr : r<x.positions.card := by omega
    obtain ⟨t,a,ab,run,hash⟩:=hashed o x s r row hr normal
    have step:=compareRecord o x r t hash hr
    by_cases pass : lower o.compression x r 24=x.commitment
    · rw [if_pos pass] at step
      obtain ⟨u,cmp,next⟩:=step
      obtain ⟨b,q,ex,bb,qb,finite,finishes,success⟩:=ih (r+1) (by omega) u next
      refine ⟨a+17+b,28+0+q,ex,by omega,by omega,finite,(run.trans cmp).finish finishes,?_⟩
      rw [success]
      constructor
      · intro tail j lo hi
        by_cases current : j=r
        · exact current ▸ pass
        · exact tail j (by omega) hi
      · intro full j lo hi;exact full j (by omega) hi
    · rw [if_neg pass] at step
      refine ⟨a+17,28+0,.failure,by omega,by omega,by decide,run.finish step,?_⟩
      exact ⟨fun e=>by contradiction,fun all=>False.elim (pass (all r le_rfl hr))⟩

theorem normalEvaluation : NormalEvaluation := by
  intro o x normal size
  let s:=Micro.normalRows (initial x)
  have start:=rowStart x normal size
  obtain ⟨n,q,ex,nb,qb,finite,finish,good⟩:=rows o x normal x.positions.card 0 (by omega) s start
  have k : x.positions.card≤LENGTH := by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at k
  let budget:=submission.steps .check-15
  have below : n≤budget := by change n≤1099511627776-15;omega
  have result:=finish (budget-n)
  rw [show n+(budget-n)=budget by omega] at result
  have cost:=congrArg Prod.snd result
  have code:=congrArg Prod.fst result
  change (checkEvaluation o (execute checkerImage budget s false)).2=q at cost
  change (checkEvaluation o (execute checkerImage budget s false)).1.exit=ex at code
  dsimp only;rw [checker_image_eq]
  let out:=checkEvaluation o (execute checkerImage budget s false)
  change out.1.exit=ex at code
  change out.2=q at cost
  change out.1.exit≠.unfinished ∧ out.2≤28*x.positions.card ∧
    (out.1.exit=.success ↔ ∀ r<x.positions.card, lower o.compression x r 24=x.commitment)
  rw [code,cost]
  exact ⟨finite,qb,by simpa using good⟩

end CommitGolfCandidate.Late.Check.Normal

namespace CommitGolfCandidate.Late
open CommitGolf
theorem certificate_of_batch_and_hiding (batch : Check.BatchEvaluation) (late_hiding : HidingGoal) :
    Certificate submission 69120 919142619 100017 :=
  certificate_of_checker_runs batch Check.Normal.normalEvaluation late_hiding
theorem certificate_of_batch (batch : Check.BatchEvaluation) :
    Certificate submission 69120 919142619 100017 := certificate_of_batch_and_hiding batch late_hiding
end CommitGolfCandidate.Late
