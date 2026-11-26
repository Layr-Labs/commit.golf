import CommitGolfCandidate.S5CheckOrdinary
import CommitGolfCandidate.S5ReplaySound
import CommitGolfCandidate.S5Trials
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Open (W)
theorem valid_length (H : Compression) (x : CheckInput) (good : S5.wireValid H x) :
    x.proof.length=expectLen (decide (x.positions.card=BATCH)) x.positions.card := by
  unfold S5.wireValid at good;split at good
  next b=>simp only [b,decide_true,expectLen,ite_true];exact good.1
  next b=>simp only [decide_eq_false b,expectLen,Bool.false_eq_true,ite_false];exact good.1.trans (Nat.mul_comm ..)
private theorem valid_size (H : Compression) (x : CheckInput) (good : S5.wireValid H x) : x.proof.length≤17179869184 := by
  rw [valid_length H x good]
  have size : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at size;unfold expectLen;split <;> omega

def BatchChecker := ∀ (o : Oracle) (x : CheckInput) (s : MachineState) (ps : x.positions.card=BATCH) (len : x.proof.length=69396),
  s.pc=pcAt 233 → RecordRegs true x 0 s → s.mem=(initial x).mem →
  Outcome o s (S5.wireValid o.compression x) (68719476736-25) 12800

private theorem empty_outcome (o : Oracle) (x : CheckInput) (empty : x.positions.card=0) (fits : x.proof.length≤17179869184) :
    Outcome o (initial x) (S5.wireValid o.compression x) 68719476736 (100*x.positions.card) := by
  let accept:=decide (x.proof.length=0)
  have ex : (initial x).getReg .x16=0:=by change W x.positions.card=0;rw [empty];rfl
  have flag : ((initial x).getReg .x17==0)=accept:=word_eq x.proof.length 0 (by omega) (by decide)
  have halt:=empty_check_run (initial x) rfl ex accept flag
  have fin : Finished o (initial x) 14 0 (if accept then .success else .failure) := by
    intro fuel;rw [observation,Nat.add_comm 14 fuel,halt,check_evaluation_pure]
  have vacuous : (S5.wireValid o.compression x ↔ x.proof.length=0) := by
    unfold S5.wireValid
    rw [if_neg (by rw [empty];decide),empty,Nat.zero_mul]
    exact ⟨And.left,fun h=>⟨h,fun r hr=>by omega⟩⟩
  refine ⟨⟨14,0,_,by decide,Nat.zero_le _,?_,?_,fin⟩⟩
  · cases accept <;> decide
  · rw [vacuous];dsimp [accept];split <;> simp_all

theorem admitted_outcome (bat : BatchChecker) (o : Oracle) (x : CheckInput) (fit : x.proof.length≤17179869184) :
    Outcome o (initial x) (S5.wireValid o.compression x) 68719476736 (100*x.positions.card) := by
  by_cases empty : x.positions.card=0
  · exact empty_outcome o x empty fit
  let b:=decide (x.positions.card=BATCH)
  obtain ⟨s,n,lim,entry⟩:=dispatch o x (by omega) fit
  by_cases match_ : x.proof.length=expectLen b x.positions.card
  · have ready : Dispatched o x s b true n:=by simpa only [b,match_,decide_true] using entry
    have regs:=dispatch_regs o x s b n ready match_
    by_cases batch : x.positions.card=BATCH
    · have yes : b=true:=decide_eq_true batch
      rw [yes] at ready regs match_
      have tail:=bat o x s batch match_ ready.pc regs ready.mem
      exact (Outcome.prefix ready.run tail).weaken Iff.rfl (by omega) (by rw [batch];decide)
    · have no : b=false:=decide_eq_false batch
      rw [no] at ready regs match_
      have tail:=ordinary_rows o x 0 x.positions.card s (Nat.zero_add _) batch regs (ready.pc.trans (by rw [if_pos (by omega : 0<x.positions.card)];rfl))
      have law : rowsValid o.compression x 0 x.positions.card ↔ S5.wireValid o.compression x := by
        rw [S5.wireValid,if_neg batch]
        refine ⟨fun all=>⟨match_.trans (Nat.mul_comm ..),fun j hj=>all j (Nat.zero_le _) (by omega)⟩,?_⟩
        intro h j _ small;exact h.2 j (by omega)
      have bound : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
      change x.positions.card≤16777216 at bound
      exact (Outcome.prefix ready.run tail).weaken law (by omega) (by omega)
  · have bad : Dispatched o x s b false n:=by simpa only [b,match_,decide_false] using entry
    have fin:=verdict o s false bad.pc
    have reject : ¬S5.wireValid o.compression x:=fun good=>match_ (valid_length _ _ good)
    exact ⟨⟨n+3,0,.failure,by omega,Nat.zero_le _,by decide,reject_iff reject,bad.run.finish fin⟩⟩

private theorem abi (c : Submission) (x : CheckInput) (fit : x.proof.length≤c.sizes.proof) :
    c.run .check x=execute (c.image .check) (c.steps .check) (c.initialState .check x) false := by simp only [Submission.run,fit,decide_true,ite_true];rfl
theorem checker_result (bat : BatchChecker) (o : Oracle) (x : CheckInput) :
    let result:=checkEvaluation o (Artifact.submission.run .check x)
    result.1.exit≠.unfinished ∧ result.2≤CHECK_BUDGET x.positions.card ∧ (result.1.exit=.success ↔ S5.wireValid o.compression x) := by
  by_cases fit : x.proof.length≤Artifact.submission.sizes.proof
  · obtain ⟨⟨n,q,ex,limit,count,done_,law,run⟩⟩:=admitted_outcome bat o x fit
    let result:=checkEvaluation o (Artifact.submission.run .check x)
    have eq : (result.1.exit,result.2)=(ex,q):=by
      have same:=run (68719476736-n)
      rw [show n+(68719476736-n)=68719476736 by omega] at same
      dsimp only [result];rw [abi _ _ fit];exact same
    have left:=congrArg Prod.fst eq
    have right:=congrArg Prod.snd eq
    change result.1.exit≠_ ∧ result.2≤_ ∧ (result.1.exit=_ ↔ _)
    rw [show result.1.exit=ex from left,show result.2=q from right]
    exact ⟨done_,count,law⟩
  · simp only [Submission.run,decide_eq_false fit,Bool.false_eq_true,ite_false,check_evaluation_pure]
    exact ⟨by decide,Nat.zero_le _,⟨(fun h=>by contradiction),fun h=>False.elim (fit (valid_size _ _ h))⟩⟩

def checker_of_batch (bat : BatchChecker) : CheckerLaw where
  terminates o x:=(checker_result bat o x).1
  replay:=S5.Replay.replay_of_wire (fun o x h=>by
    rw [scheme_check_evaluation] at h
    exact (checker_result bat o x).2.2.mp (beq_iff_eq.mp h))
  honest o m ps salt:=by
    let x:=canonicalInput o m ps salt
    have good:=S5.canonical_valid o m ps salt
    have a:=checker_result bat o x
    change (checked o x).1=true ∧ (checked o x).2≤CHECK_BUDGET ps.card
    rw [checked,scheme_check_evaluation];exact ⟨beq_iff_eq.mpr (a.2.2.mpr good),a.2.1⟩
end CommitGolfCandidate.S5Machine.Check
