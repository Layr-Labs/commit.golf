import CommitGolfCandidate.TruncChecks
import CommitGolfCandidate.TruncBinding
import CommitGolfCandidate.LateHidingGame
import CommitGolfCandidate.TruncStatic
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv OracleComp
set_option maxRecDepth 12000
attribute [local irreducible] Late.actualEvaluation Late.words Late.treeM Late.node Late.wideOpening Trunc.pack Trunc.unpack

private theorem honestCheck (o : Oracle) (m : Message) (ws : List Late.PairCoins) (ps : Positions) :
    (Late.actualEvaluation o (Late.honestInput o m ws ps)).1=true := by
  let s:=Late.wordTape ws
  let t:=Late.cachedLevels o m ws
  let x:=Late.honestInput o m ws ps
  let y:=Late.Check.canonicalInput m ps t s
  unfold Late.actualEvaluation;rw [Late.Check.Normal.scheme_check_evaluation];apply beq_iff_eq.mpr
  change (Late.Check.Normal.checkEvaluation o (submission.run .check x)).1.exit=.success
  have len : x.proof.length=(if ps.card=BATCH then 69120 else 792*ps.card) := Late.opening_size t s ps
  by_cases hb : ps.card=BATCH
  · apply (batchEvaluation o x hb).2.2.mpr
    have back:=Late.Check.pack_canonical o.compression m s ps hb
    have e : wideInput x=y := by
      unfold wideInput;rw [if_pos (show x.positions.card=BATCH from hb)]
      change (⟨_,ps,_,unpack (Late.opening t s ps)⟩ : CheckInput)=y
      rw [Late.opening,if_pos hb];change (⟨_,ps,_,unpack (pack (Late.wideOpening t s ps))⟩ : CheckInput)=y
      rw [show unpack (pack (Late.wideOpening t s ps))=Late.wideOpening t s ps from back];rfl
    exact ⟨len.trans (if_pos hb),by rw [e];exact batchHonest o.compression m s ps hb⟩
  · apply (Normal.evaluate o x hb).2.2.mpr
    refine ⟨len.trans (if_neg hb),?_⟩
    have e : x=y := by
      change (⟨_,ps,_,Late.opening t s ps⟩ : CheckInput)=y
      rw [Late.opening,if_neg hb];rfl
    rw [e]
    intro r hr
    have dep : Late.Check.depth y=24 := by change (if ps.card=BATCH then 16 else 24)=_;rw [if_neg hb]
    have stride : Late.Check.start y r=792*r := by unfold Late.Check.start;rw [dep];omega
    have salt : recordSalt y r=Late.Check.salt y r := by unfold Late.Check.salt;rw [stride];rfl
    have sib : normalSibling y r=Late.Check.sibling y r := by
      funext l;unfold normalSibling Late.Check.sibling Late.Check.proofAt;rw [stride]
      change readBuffer _ (12079599648+792*r+24+32*l) 32=readBuffer _ (12079599648+(792*r+24+32*l)) 32
      rw [show 12079599648+792*r+24+32*l=12079599648+(792*r+24+32*l) by omega] <;> rfl
    have ref:=widePath o.compression m s ps r 24 hr (by decide) dep.ge
    have last : Late.Open.indexAbove (recordIndex y r) 24=0 := Nat.div_eq_of_lt (recordIndex y r).isLt
    change recordRoot o.compression (recordValue y r) (recordSalt y r) (recordIndex y r) (normalSibling y r)=_
    rw [salt,sib]
    exact ref.trans (congrArg (Late.node t LOG_LENGTH) last)

private theorem terminate : submission.Termination := by
  intro o prog input
  cases prog with
  | commit=>exact Late.commit_terminates o input
  | opening=>exact Late.open_terminates o input.1 input.2
  | check=>
    have det : o.run (submission.run .check input)=pure (Late.Check.Normal.checkEvaluation o (submission.run .check input)) := by
      by_cases h:input.proof.length≤submission.sizes.proof
      · simp only [Submission.run,h,decide_true,if_true];exact Late.Check.Normal.execute_check_evaluation ..
      · simp [Submission.run,h,oracle_run_pure,Late.Check.Normal.check_evaluation_pure]
    rw [det];apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro z mem;rw [support_pure,Set.mem_singleton_iff] at mem;subst z
    exact (checkResources o input).1

private theorem honestComplete : submission.scheme.Completeness := by
  intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro z mem;rw [Late.honest_distribution,mem_support_bind_iff] at mem
  obtain ⟨ws,_,e⟩:=mem;rw [support_pure,Set.mem_singleton_iff] at e;subst z
  exact honestCheck o m ws ps

private theorem honestBudgets : submission.scheme.HonestBudgets := by
  intro o m ps;apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro z mem;rw [Late.honest_distribution,mem_support_bind_iff] at mem
  obtain ⟨ws,_,e⟩:=mem;rw [support_pure,Set.mem_singleton_iff] at e;subst z
  let x:=Late.honestInput o m ws ps
  refine ⟨(by decide : 83886079≤COMMIT_BUDGET),Nat.zero_le _,?_⟩
  change (Late.actualEvaluation o x).2≤CHECK_BUDGET ps.card
  rw [Late.actualEvaluation,Late.Check.Normal.scheme_check_evaluation]
  exact (checkResources o x).2

theorem certificate : Certificate submission 69120 919142745 116041 where
  admission := admission
  machineSuccess := Late.machine_success
  termination := terminate
  completeness := honestComplete
  honestBudgets := honestBudgets
  proofSize := Late.proof_size
  proverCycles := Late.prover_cycles
  binding := trunc_submission_binding checkedSound
  hidingProperty := Late.machine_hiding Late.view_refinement Late.late_hiding
end CommitGolfCandidate.Trunc
