import CommitGolfCandidate.CheckEvaluation

namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
set_option autoImplicit false

theorem cap_check_evaluation_bind_value (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).1 =
      (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).1 := by
  rw [check_evaluation_bind]

end CommitGolfCandidate
