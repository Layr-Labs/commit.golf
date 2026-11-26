import CommitGolf.Statements
import CommitGolfCandidate.OpeningOutput

namespace CommitGolfCandidate.PairCap
open CommitGolf OracleComp

/-- The first index in a pair selects its level-8 sibling. A left index
precedes every right index in the same pair. -/
def overrideSlot {α : Type} (bucket : Nat → Nat) (replacement : Nat → α) (pair : Nat) :
    Nat → α → α
  | 0, fallback => fallback
  | n+1, fallback => overrideSlot bucket replacement pair n
      (if bucket n = pair then replacement n else fallback)

def slotOffset (positions : Positions) (pair : Nat) : Nat :=
  overrideSlot (fun n => openingIndex positions n / 131072) (fun n => 560*n+528) pair
    BATCH (71680 + 32*pair)

theorem map_overrideSlot {α β : Type} (f : α → β) (bucket : Nat → Nat)
    (replacement : Nat → α) (pair count : Nat) (fallback : α) :
    f (overrideSlot bucket replacement pair count fallback) =
    overrideSlot bucket (fun n => f (replacement n)) pair count (f fallback) := by
  induction count generalizing fallback with
  | zero => rfl
  | succ n ih =>
    simp only [overrideSlot, ih]
    split <;> rfl

def oldOffset (positions : Positions) (offset : Nat) : Nat :=
  if offset < 67584 then (offset / 528) * 560 + offset % 528
  else slotOffset positions ((offset - 67584) / 32) + offset % 32

def convert (positions : Positions) (proof : Proof) : Proof :=
  if positions.card = BATCH then
    (List.range 71680).map fun offset => proof[oldOffset positions offset]?.getD 0
  else proof

theorem convert_batch_length {positions : Positions} (h : positions.card = BATCH) (proof : Proof) :
    (convert positions proof).length = 71680 := by simp [convert, h]

theorem convert_normal {positions : Positions} (h : positions.card ≠ BATCH) (proof : Proof) :
    convert positions proof = proof := by simp [convert, h]

private def remember {S : Type} {k : Nat} (c : Hiding.HidingChallenge S k) :
    Hiding.HidingChallenge (S × Positions) k :=
  ⟨c.message₀, c.message₁, c.positions, c.size_eq, c.agree, c.aux, c.positions⟩

private def liftAdversary {S O : Type} {k : Nat} (a : Hiding.HidingAdversary S O k) :
    Hiding.HidingAdversary (S × Positions) O k where
  choose := remember <$> a.choose
  observe state root proof := a.observe state.1 root (convert state.2 proof)

private theorem liftBound {S O : Type} {k t : Nat} (a : Hiding.HidingAdversary S O k)
    (h : Hiding.QueryBound a t) : Hiding.QueryBound (liftAdversary a) t := by
  intro first member
  change first ∈ support (costDist (remember <$> a.choose) _) at member
  rw [costDist_map, support_map] at member
  obtain ⟨original, reached, rfl⟩ := member
  exact ⟨(h original reached).1, fun root proof => (h original reached).2 root
    (convert original.1.positions proof)⟩

def convertedScheme (s : Scheme) : Scheme :=
  { s with opening := fun td positions => convert positions <$> s.opening td positions }

private theorem sameExperiment {S O : Type} {k : Nat} (s : Scheme)
    (a : Hiding.HidingAdversary S O k) (b : Bool) :
    Hiding.hidingExperiment (convertedScheme s) a b =
    Hiding.hidingExperiment s (liftAdversary a) b := by
  simp [Hiding.hidingExperiment, convertedScheme, liftAdversary, remember, bind_map_left]

theorem hiding_of_conversion (s : Scheme) (h : s.Hiding HIDING_ERROR) :
    (convertedScheme s).Hiding HIDING_ERROR := by
  refine ⟨h.1, ?_⟩
  intro k t size S O a bounded
  rw [sameExperiment, sameExperiment]
  exact h.2 k t size (S × Positions) O (liftAdversary a) (liftBound a bounded)

end CommitGolfCandidate.PairCap
