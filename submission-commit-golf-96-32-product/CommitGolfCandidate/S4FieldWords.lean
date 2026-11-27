import CommitGolfCandidate.S4FieldWords0
import CommitGolfCandidate.S4FieldWords1
import CommitGolfCandidate.S4FieldWords2
import CommitGolfCandidate.S4FieldWords3
import CommitGolfCandidate.S4FieldWords4
import CommitGolfCandidate.S4FieldWords5
import CommitGolfCandidate.S4FieldWords6
import CommitGolfCandidate.S4FieldWords7
import CommitGolfCandidate.S4FieldWords8
namespace CommitGolfCandidate.S4.Open
theorem fieldWords (b : Bool) (l q : Nat) (bl : l<8) (bq : q<fieldsIn b) (lane : b=true ∨ l=0) :
    fieldValid b l q := by
  cases b with
  | false=>
    have e : l=0:=lane.resolve_left (by decide)
    subst l;exact allWords8 ⟨q,bq⟩
  | true=>
    interval_cases l
    · exact allWords0 ⟨q,bq⟩
    · exact allWords1 ⟨q,bq⟩
    · exact allWords2 ⟨q,bq⟩
    · exact allWords3 ⟨q,bq⟩
    · exact allWords4 ⟨q,bq⟩
    · exact allWords5 ⟨q,bq⟩
    · exact allWords6 ⟨q,bq⟩
    · exact allWords7 ⟨q,bq⟩
end CommitGolfCandidate.S4.Open
