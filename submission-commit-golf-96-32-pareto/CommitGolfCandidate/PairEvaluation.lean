import CommitGolfCandidate.PairCertificate
import CommitGolfCandidate.PairHeader
import CommitGolfCandidate.PairHonest
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 300000

/-- Fixed-oracle checker behavior at word 232, immediately after the header
verifies the batch length and installs the record pointers. -/
def BatchEvaluation : Prop :=
  ∀ (o : Oracle) (input : CheckInput), input.positions.card=BATCH → input.proof.length=71680 →
    let first := Batch.initialRows (submission.initialState .check input)
    let out := checkEvaluation o (execute (submission.image .check) (submission.steps .check-17) first false)
    out.1.exit≠.unfinished ∧ out.2≤2815 ∧ (out.1.exit=.success ↔ BatchValid o.compression input)

attribute [local irreducible] execute checkEvaluation Batch.initialRows

private theorem allBatch (law : BatchEvaluation) (o : Oracle) (input : CheckInput) (b : input.positions.card=BATCH) :
    let out := checkEvaluation o (submission.run .check input)
    out.1.exit≠.unfinished ∧ out.2≤2815 ∧ (out.1.exit=.success ↔ BatchValid o.compression input) := by
  dsimp only
  let s := submission.initialState .check input
  have batch : s.getReg .x16 = 128 := by change BitVec.ofNat 64 input.positions.card = 128; rw [b]; rfl
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · have run : submission.run .check input = execute (submission.image .check) (submission.steps .check) s false := by
      simp only [Submission.run,valid,decide_true,if_true]; rfl
    rw [run]
    by_cases size : input.proof.length=71680
    · have good := law o input b size
      have ptr : s.getReg .x17 = 71680 := by change BitVec.ofNat 64 input.proof.length=71680; rw [size];rfl
      have splitFuel : submission.steps .check = 17 + (submission.steps .check-17) := by decide
      rw [splitFuel,Batch.headerRun s rfl batch ptr,bind_pure_comp,check_evaluation_map]
      exact ⟨good.1,good.2.1,good.2.2⟩
    · have wrong : s.getReg .x17≠71680 := by
        intro eqn;apply size
        change BitVec.ofNat 64 input.proof.length=71680 at eqn
        have h := congrArg BitVec.toNat eqn
        change input.proof.length ≤ 13153337344 at valid
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at h
        exact h.trans (by decide)
      rw [show submission.steps .check = 14 + (submission.steps .check-14) by decide,
        Batch.lengthReject s rfl batch wrong,check_evaluation_pure]
      exact ⟨(by decide : Exit.failure ≠ Exit.unfinished),(by decide : 0≤2815),⟨by intro bad;contradiction,fun h => False.elim (size h.length)⟩⟩
  · have oversized : submission.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by simp [Submission.run,valid]
    rw [oversized,check_evaluation_pure]
    exact ⟨(by decide : Exit.failure ≠ Exit.unfinished),(by decide : 0≤2815),⟨by intro bad;contradiction,fun h => False.elim (valid (h.length ▸ (by decide : 71680≤submission.sizes.proof)))⟩⟩

theorem checks_of_evaluation (law : BatchEvaluation) : BatchChecks where
  resources o i b := ⟨(allBatch law o i b).1,(allBatch law o i b).2.1⟩
  sound := by
    intro o i b accepted
    rw [scheme_check_evaluation] at accepted
    exact (allBatch law o i b).2.2.mp (beq_iff_eq.mp accepted)
  honest := by
    intro o m s correct ps b
    have hl := (allBatch law o (honestInput s m ps) b).2.2.mpr (honestModel o m s correct ps b)
    have result := scheme_check_evaluation o submission (honestInput s m ps)
    rw [show _ = _ from hl] at result
    exact (congrArg Prod.fst result).trans (by rfl)

theorem certificate_of_evaluation (law : BatchEvaluation) :
    Certificate submission 71680 959447084 40631 :=
  certificate_of_batchChecks (checks_of_evaluation law)
end CommitGolfCandidate.PairCap
