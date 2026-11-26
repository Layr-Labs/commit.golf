import CommitGolfCandidate.S4OrdinaryJudge
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
def AllRows (o : Oracle) (x : CheckInput) (r : Nat) := ∀ j,r≤j → j<x.positions.card → rootOK o x j

structure Conclusion (o : Oracle) (s : MachineState) (steps calls : Nat) (criterion : Prop) : Prop where
  final : ∃ e,e≠.unfinished ∧ (e=.success ↔ criterion) ∧ Finishes o s steps calls e

theorem normalFinish (o : Oracle) (s : MachineState) (pc : s.pc=pcAt 2656) : Finishes o s 4 0 .success := by
  have j:=jump .check 2656 4852 s pc (by decide)
  exact (ofRuns o j).finish (verdict true _ o rfl)

private theorem normalTail (o : Oracle) (x : CheckInput) (normal : x.positions.card≠BATCH)
    (left : Nat) (r : Nat) (total : r+left=x.positions.card) (s : MachineState) (env : Env x s) (cur : Cursor x s r)
    (pc : s.pc=pcAt (if r<x.positions.card then rowStart false else endOfRows false)) :
    ∃ n q,n≤3000*left+4 ∧ q≤28*left ∧ Conclusion o s n q (AllRows o x r) := by
  induction left generalizing r s with
  | zero=>
    have eqv : r=x.positions.card:=by omega
    rw [if_neg (by omega)] at pc
    exact ⟨4,0,by decide,le_rfl,⟨⟨.success,by decide,⟨fun _ j h b=>False.elim (by omega),fun _=>rfl⟩,normalFinish o s pc⟩⟩⟩
  | succ k ih=>
    have br:r<x.positions.card:=by omega
    rw [if_pos br] at pc
    rcases ordinaryRecordStep o x s r br normal pc env cur with ⟨bad,n,hn,fail⟩|⟨yes,t,n,hn,go⟩
    · exact ⟨n,28,by omega,by omega,⟨⟨.failure,by decide,⟨(fun eq=>by cases eq),fun all=>False.elim (bad (all r le_rfl br))⟩,fail⟩⟩⟩
    · obtain ⟨m,q,hm,hq,⟨e,closed,eqv,fin⟩⟩:=ih (r+1) (by omega) t go.env go.cursor go.pc
      refine ⟨n+m,28+q,by omega,by omega,⟨⟨e,closed,?_,go.run.finish fin⟩⟩⟩
      apply eqv.trans;constructor
      · intro rest j lo hi;by_cases same:j=r
        · subst j;exact yes
        · exact rest j (by omega) hi
      · intro all j lo hi;exact all j (by omega) hi

def Evaluation (o : Oracle) (x : CheckInput) := ∃ n q,n≤1099511627776 ∧ q≤CHECK_BUDGET x.positions.card ∧
    Conclusion o (initial x) n q (wireValid o.compression x)
theorem ordinaryEvaluation (o : Oracle) (x : CheckInput) (normal : x.positions.card≠BATCH)
    (fits : x.proof.length≤Late.submission.sizes.proof) : Evaluation o x := by
  have count:=boundedCount x
  have equiv : wireValid o.compression x ↔ x.proof.length=824*x.positions.card ∧ AllRows o x 0 := by
    rw [wireValid,if_neg normal,Nat.mul_comm x.positions.card 824]
    simp only [AllRows,rootOK,Nat.zero_le,forall_const]
  rcases normalDispatch o x normal fits with ⟨bad,n,bn,fin⟩|⟨size,empty,n,bn,fin⟩|⟨s,ready,n,bn,go⟩
  · exact ⟨n,0,by omega,Nat.zero_le _,⟨⟨.failure,by decide,⟨(fun e=>by cases e),fun good=>False.elim (bad (equiv.mp good).1)⟩,fin⟩⟩⟩
  · have good:=equiv.mpr ⟨size,fun j _ b=>False.elim (by omega)⟩
    exact ⟨n,0,by omega,Nat.zero_le _,⟨⟨.success,by decide,⟨fun _=>good,fun _=>rfl⟩,fin⟩⟩⟩
  · have start : s.pc=pcAt (if 0<x.positions.card then rowStart false else endOfRows false):=by rw [if_pos ready.positive];exact ready.pc
    obtain ⟨m,q,mLimit,qLimit,⟨e,stop,correct,fin⟩⟩:=normalTail o x normal x.positions.card 0 (Nat.zero_add _) s ready.toEnv ready.toCursor start
    refine ⟨n+m,q,by omega,by unfold CHECK_BUDGET;omega,⟨⟨e,stop,?_,by simpa only [Nat.zero_add] using go.finish fin⟩⟩⟩
    exact correct.trans ⟨fun all=>equiv.mpr ⟨ready.len,all⟩,fun v=>(equiv.mp v).2⟩
end CommitGolfCandidate.S4.Machine
