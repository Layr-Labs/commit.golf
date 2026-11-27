import CommitGolfCandidate.LateModel
namespace CommitGolfCandidate.Late
open CommitGolf OracleComp
theorem lift_draws (xs : List Nat) :
    xs.mapM (fun _ => drawPair) =
      (liftM (xs.mapM (fun _ => ($ᵗ PairCoins : ProbComp PairCoins))) : OracleComp World _) := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.mapM_cons, liftM_bind, liftM_pure]
    rw [ih]
    rfl

end CommitGolfCandidate.Late
