import CommitGolfCandidate.PairCheckManifest
import CommitGolfCandidate.PairCheckImage
import CommitGolfCandidate.TwoPermutationPackedTrustedInput

/-! The pair-heads submission whose check image the `PairCheck*` proofs execute: the frozen pair-heads programs
(`stack/image/programs-ph-frozen.json`) rendered by the verifier's `artifact.py` (namespace renamed to
`CommitGolf.PairCheckArtifact`). Its check image is `pairImage`; its sizes, layout, step allowance and (empty) check
data equal the A′ ones, so its check loader state is A′'s. -/
namespace TwoPermutationPrototype.PairChecker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

abbrev submission : Submission := PairCheckArtifact.submission

theorem artifact_image : submission.image .check = PairCk.Packed.Checker.pairImage := by
  unfold submission PairCheckArtifact.submission PairCk.Packed.Checker.pairImage
  rfl

theorem sizes_eq : submission.sizes = QAssembly.submission.sizes := rfl
theorem layout_eq : submission.layout = QAssembly.submission.layout := rfl
theorem steps_eq : submission.steps .check = QAssembly.submission.steps .check := rfl

theorem check_data_empty : (submission.image .check).data = [] := by
  unfold submission PairCheckArtifact.submission
  rfl

/-- The check loader reads a submission only through its sizes, layout and check data. -/
theorem initial_state_congr (s t : Submission) (sizes : s.sizes = t.sizes) (layout : s.layout = t.layout)
    (data : (s.image .check).data = (t.image .check).data) (input : CheckInput) :
    s.initialState .check input = t.initialState .check input := by
  cases s with | mk sz l im st =>
    cases t with | mk sz' l' im' st' =>
      change sz = sz' at sizes
      change l = l' at layout
      subst sz'; subst l'
      change (im .check).data = (im' .check).data at data
      unfold Submission.initialState
      simp only [Riscv.dataBase, data]
      rfl

private theorem quartet_check_data_empty : (QAssembly.submission.image .check).data = [] := by
  unfold QAssembly.submission QuartetArtifact.submission
  rfl

/-- The trusted loader reads only sizes, layout and the (empty) data image. -/
theorem initial_state (input : CheckInput) :
    submission.initialState .check input = QAssembly.submission.initialState .check input :=
  initial_state_congr _ _ sizes_eq layout_eq (check_data_empty.trans quartet_check_data_empty.symm) input

theorem check_run_admitted (input : CheckInput)
    (admitted : input.proof.length ≤ submission.sizes.proof) :
    submission.run .check input =
      execute (submission.image .check) 34359803904 (submission.initialState .check input) false := by
  simp only [Submission.run,admitted,decide_true,ite_true]
  rfl

theorem check_run_oversized (input : CheckInput)
    (oversized : submission.sizes.proof < input.proof.length) :
    submission.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
  have rejected := Nat.not_le.mpr oversized
  simp only [Submission.run,rejected,decide_false,Bool.false_eq_true,ite_false]

end TwoPermutationPrototype.PairChecker
