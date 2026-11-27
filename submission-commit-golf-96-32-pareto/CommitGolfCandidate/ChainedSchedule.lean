import CommitGolfCandidate.ChainedQueryGraph
set_option Elab.async false

/-! Parameters and resource arithmetic for the chained internal layout. -/
namespace CommitGolfCandidate.Chained
open scoped BigOperators
set_option exponentiation.threshold 520

def calls (h : Height) : Nat :=
  ([1,1,1,1,1,1,1,1,2,4,6,8,12,16,16,16,1,1,1,1,1,1,1,1] : List Nat)[h.val]?.getD 1
def width (h : Height) : Nat :=
  ([238,238,238,238,238,238,238,238,236,234,233,232,231,230,230,230,238,238,238,238,238,238,238,238] : List Nat)[h.val]?.getD 238
theorem density : ∀ h, 2^238 ≤ (calls h)^2*2^(width h) := by decide +kernel
theorem calls_bound : ∀ h, calls h≤16 := by decide +kernel
theorem normal_work : 4+(∑ h : Height, calls h)=100 := by decide +kernel
theorem lower_work : 4+(∑ h : Fin 15, calls ⟨h.val,by omega⟩)=76 := by decide +kernel
theorem batch_work : 128*76+128*16+255=12031 := rfl
theorem replay_room : 2*100*2^24<2^32 := by decide
theorem commit_calls : 4*2^24+(∑ h : Height, calls h*2^(23-h.val))=84087039 := by decide +kernel

end CommitGolfCandidate.Chained
