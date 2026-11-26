import CommitGolf.Parameters

/-! Descending binary heap induction for deferred truncation.
At cursor n, children of parents below n can still be raw. Slots above 2*n+1 have
been finalized. The projection may depend on the absolute heap index. -/
namespace CommitGolfCandidate.Chained.Native.Fast

def Frontier {α : Type} (view : Nat → α → α) (logical physical : Nat → α) (cursor : Nat) : Prop :=
  ∀ i, cursor<i → i<2^25 →
    (if i≤2*cursor+1 then view i (physical i) else physical i)=logical i

theorem frontier_init {α : Type} (view : Nat→α→α) (logical physical : Nat→α)
    (leaves : ∀ i, 2^24≤i → i<2^25 → view i (physical i)=logical i) :
    Frontier view logical physical (2^24-1) := by
  intro i lo hi
  rw [if_pos (by omega)]
  exact leaves i (by omega) hi

theorem frontier_step {α : Type} {view : Nat→α→α} {logical before after : Nat→α}
    {n : Nat} (pos : 0<n) (small : n<2^24) (prior : Frontier view logical before n)
    (node : view n (after n)=logical n)
    (left : after (2*n)=view (2*n) (before (2*n)))
    (right : after (2*n+1)=view (2*n+1) (before (2*n+1)))
    (unchanged : ∀ i, n<i → i<2^25 → i≠2*n → i≠2*n+1 → after i=before i) :
    Frontier view logical after (n-1) := by
  intro i lo hi
  by_cases same : i=n
  · subst i;rw [if_pos (by omega)];exact node
  have old:=prior i (by omega) hi
  by_cases l : i=2*n
  · subst i;rw [if_neg (by omega),left];simpa using old
  by_cases r : i=2*n+1
  · subst i;rw [if_neg (by omega),right];simpa using old
  rw [unchanged i (by omega) hi l r]
  by_cases under : i≤2*(n-1)+1
  · rw [if_pos under];simpa only [if_pos (show i≤2*n+1 by omega)] using old
  · rw [if_neg under];simpa only [if_neg (show ¬ i≤2*n+1 by omega)] using old

theorem frontier_handoff {α : Type} {view : Nat→α→α} {heap physical : Nat→α}
    (prior : Frontier view heap physical (2^16-1))
    (top : ∀ i, i<2^17 → view i (physical i)=physical i) :
    ∀ i, 2^16-1<i → i<2^25 → physical i=heap i := by
  intro i lo hi
  have known:=prior i lo hi
  by_cases active : i≤2*(2^16-1)+1
  · simpa only [if_pos active,top i (by omega)] using known
  · simpa only [if_neg active] using known

end CommitGolfCandidate.Chained.Native.Fast
