import CommitGolfCandidate.LateBatchEntry
import CommitGolfCandidate.LateGuards
import CommitGolfCandidate.LateCheckModel
import CommitGolfCandidate.LateResources2

namespace CommitGolfCandidate.Late.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Normal (checkEvaluation check_evaluation_map check_evaluation_pure)
set_option maxRecDepth 9000

/-- Word 207 follows the dispatch and the successful 72,704-byte gate. -/
def BatchEvaluation : Prop :=
  ∀ (o : Oracle) (input : CheckInput), input.positions.card=BATCH → input.proof.length=72704 →
    let first := Micro.initialRows (submission.initialState .check input)
    let out := checkEvaluation o (execute (submission.image .check) (submission.steps .check-17) first false)
    out.1.exit≠.unfinished ∧ out.2≤2815 ∧ (out.1.exit=.success ↔ BatchValid o.compression input)

def NormalEvaluation : Prop :=
  ∀ (o : Oracle) (input : CheckInput), input.positions.card≠BATCH → input.proof.length=input.positions.card*792 →
    let first := Micro.normalRows (submission.initialState .check input)
    let out := checkEvaluation o (execute (submission.image .check) (submission.steps .check-15) first false)
    out.1.exit≠.unfinished ∧ out.2≤28*input.positions.card ∧
      (out.1.exit=.success ↔ ∀ r < input.positions.card, lower o.compression input r 24=input.commitment)

private theorem bv_eq_iff (n m : Nat) (a : n<2^64) (b : m<2^64) :
    BitVec.ofNat 64 n=BitVec.ofNat 64 m ↔ n=m := by
  constructor
  · intro e;have p:=congrArg BitVec.toNat e;simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b] using p
  · intro e;rw [e]

private theorem regs (x : CheckInput) :
    let s:=submission.initialState .check x
    s.pc=4096 ∧ s.getReg .x16=BitVec.ofNat 64 x.positions.card ∧ s.getReg .x17=BitVec.ofNat 64 x.proof.length :=
  ⟨rfl,rfl,rfl⟩

private theorem rejected (e : Execution) (fail : e.exit=.failure) (cap : Nat) (goal : Prop) (bad : ¬goal) :
    e.exit≠.unfinished ∧ 0≤cap ∧ (e.exit=.success ↔ goal) := by simp [fail,bad]

attribute [local irreducible] execute checkEvaluation Micro.initialRows Micro.normalRows

theorem full_evaluation (batchEval : BatchEvaluation) (normalEval : NormalEvaluation) (o : Oracle) (x : CheckInput) :
    let out := checkEvaluation o (submission.run .check x)
    out.1.exit≠.unfinished ∧ out.2≤(if x.positions.card=BATCH then 2815 else 28*x.positions.card) ∧
      (out.1.exit=.success ↔ Valid o.compression x) := by
  dsimp only
  let s:=submission.initialState .check x
  obtain ⟨pc,rg16,rg17⟩ := regs x
  change s.pc=_ at pc;change s.getReg .x16=_ at rg16;change s.getReg .x17=_ at rg17
  have k : x.positions.card≤LENGTH := by simpa using Finset.card_le_univ x.positions
  change x.positions.card≤16777216 at k
  by_cases valid : x.proof.length≤submission.sizes.proof
  · have start : submission.run .check x=execute (submission.image .check) (submission.steps .check) s false := by
      simp only [Submission.run,valid,decide_true,if_true];rfl
    rw [start]
    have bound : x.proof.length≤13421772800 := valid
    by_cases batch : x.positions.card=BATCH
    · rw [if_pos batch,Valid,if_pos batch]
      have mode : s.getReg .x16=128 := by rw [rg16,batch];rfl
      by_cases size : x.proof.length=72704
      · have good := batchEval o x batch size
        have run := Micro.batchHeader s pc mode (by rw [rg17,size];rfl) (submission.steps .check-17)
        change execute (submission.image .check) _ s false = _ at run
        rw [show submission.steps .check=(submission.steps .check-17)+17 by decide,run,bind_pure_comp,check_evaluation_map]
        exact ⟨good.1,good.2.1,good.2.2⟩
      · have wrong : (72704 : Word)≠s.getReg .x17 := by
          rw [rg17];intro e;apply size
          exact (bv_eq_iff _ 72704 (by omega) (by decide)).mp e.symm
        obtain ⟨e,run,fail,_,_⟩ := batch_length_reject s pc mode wrong (submission.steps .check-14)
        change execute (submission.image .check) _ s false=pure e at run
        rw [show submission.steps .check=(submission.steps .check-14)+14 by decide,run,check_evaluation_pure]
        exact rejected e fail _ _ fun b=>size b.length
    · rw [if_neg batch,Valid,if_neg batch]
      have mode : s.getReg .x16≠128 := by
        rw [rg16];intro e;exact batch ((bv_eq_iff _ 128 (by omega) (by decide)).mp e)
      have mul : s.getReg .x16*792=BitVec.ofNat 64 (x.positions.card*792) := by rw [rg16];exact (BitVec.ofNat_mul x.positions.card 792).symm
      by_cases size : x.proof.length=x.positions.card*792
      · have good:=normalEval o x batch size
        have run:= (Micro.normalHeader s pc mode (by rw [mul,rg17,size])).1 (submission.steps .check-15)
        change execute (submission.image .check) _ s false = _ at run
        rw [show submission.steps .check=(submission.steps .check-15)+15 by decide,run,bind_pure_comp,check_evaluation_map]
        exact ⟨good.1,good.2.1,good.2.2.trans ⟨fun p=>⟨size,p⟩,And.right⟩⟩
      · have wrong : s.getReg .x16*792≠s.getReg .x17 := by
          rw [mul,rg17];intro e;apply size
          exact (bv_eq_iff _ _ (by omega) (by omega)).mp e.symm
        obtain ⟨e,run,fail,_,_⟩ := normal_length_reject s pc mode wrong (submission.steps .check-15)
        change execute (submission.image .check) _ s false=pure e at run
        rw [show submission.steps .check=(submission.steps .check-15)+15 by decide,run,check_evaluation_pure]
        exact rejected e fail _ _ fun v=>size v.1
  · have denied : submission.run .check x=pure ⟨.failure,initialMachine,0,0⟩ := by simp [Submission.run,valid]
    rw [denied,check_evaluation_pure]
    apply rejected _ rfl
    intro v;apply valid
    change x.proof.length≤13421772800
    unfold Valid at v
    split at v
    · rw [v.length];decide
    · rw [v.1];omega

theorem law_of_evaluations (batch : BatchEvaluation) (normal : NormalEvaluation) : MachineLaw := by
  intro o input
  obtain ⟨_,budget,criterion⟩ := full_evaluation batch normal o input
  unfold evaluation
  rw [Normal.scheme_check_evaluation]
  exact ⟨budget,beq_iff_eq.trans criterion⟩

theorem termination_of_evaluations (batch : BatchEvaluation) (normal : NormalEvaluation) : submission.Termination := by
  intro o prog input
  cases prog with
  | commit => exact commit_terminates o input
  | opening => exact open_terminates o input.1 input.2
  | check =>
    have deterministic : o.run (submission.run .check input) = pure (checkEvaluation o (submission.run .check input)) := by
      by_cases fit : input.proof.length≤submission.sizes.proof
      · simp only [Submission.run,fit,decide_true,if_true]
        exact Normal.execute_check_evaluation ..
      · simp only [Submission.run,fit,decide_false,Bool.false_eq_true,if_false,oracle_run_pure,check_evaluation_pure]
    rw [deterministic]
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro r reach
    rw [support_pure,Set.mem_singleton_iff] at reach;subst r
    exact (full_evaluation batch normal o input).1

end CommitGolfCandidate.Late.Check
