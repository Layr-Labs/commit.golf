import CommitGolfCandidate.ReconstructedCap

namespace CommitGolfCandidate.Reconstruction

/-- Abstract routes deliberately leave the executable's index-to-route map as a parameter. -/
inductive Lane where | a | b | c | d
inductive Route : Nat → Type where
  | endpoint : Lane → Route 0
  | left {h : Nat} : Route h → Route (h + 1)
  | right {h : Nat} : Route h → Route (h + 1)

universe u
variable {α : Type u} {h : Nat}

def Block.mark (b : Block) : Lane → Block
  | .a => { b with a := true }
  | .b => { b with b := true }
  | .c => { b with c := true }
  | .d => { b with d := true }

private theorem mark_bound (b : Block) (lane : Lane) :
    (b.mark lane).endpoints ≤ b.endpoints + 1 := by
  cases lane <;> simp [Block.mark, Block.endpoints] <;> omega

def Cap.mark {h : Nat} : Cap h → Route h → Cap h
  | .block b, .endpoint e => .block (b.mark e)
  | .fork l r, .left path => .fork (l.mark path) r
  | .fork l r, .right path => .fork l (r.mark path)

private theorem mark_one (c : Cap h) (path : Route h) :
    (c.mark path).count.endpoints ≤ c.count.endpoints + 1 := by
  induction c with
  | block b => cases path with | endpoint e => exact mark_bound b e
  | fork l r hl hr =>
    cases path with
    | left p => have := hl p; simp only [Cap.mark, Cap.count]; omega
    | right p => have := hr p; simp only [Cap.mark, Cap.count]; omega

def Cap.empty : (h : Nat) → Cap h
  | 0 => .block ⟨false, false, false, false⟩
  | h + 1 => .fork (empty h) (empty h)

private theorem empty_count (h : Nat) : (Cap.empty h).count.endpoints = 0 := by
  induction h with
  | zero => rfl
  | succ h ih => simp [Cap.empty, Cap.count, ih]

def collect (route : α → Route h) : List α → Cap h
  | [] => Cap.empty h
  | x :: xs => (collect route xs).mark (route x)

theorem collect_bound (route : α → Route h) (xs : List α) :
    (collect route xs).count.endpoints ≤ xs.length := by
  induction xs with
  | nil => simp [collect, empty_count]
  | cons x xs ih =>
    have := mark_one (collect route xs) (route x)
    simp only [collect, List.length_cons]
    omega

theorem batch_format_bound (route : α → Route 7) (positions : List α)
    (batch : positions.length = 128) :
    alignedBytes (positions.length * recordBits + capBits (collect route positions).count)
      ≤ sameSize.proofBytes := by
  rw [batch]
  exact format_bound _ (batch ▸ collect_bound route positions)

/-- Eight-byte rounding still fits the declared proof buffer at every legal cardinality. -/
theorem all_openings_fit (route : α → Route 7) (positions : List α)
    (size : positions.length ≤ 2 ^ 24) :
    alignedBytes (positions.length * recordBits + capBits (collect route positions).count)
      ≤ 8355061248 := by
  have := cap_bound_all (collect route positions)
  rw [lower_record.2.2]
  unfold alignedBytes
  omega

end CommitGolfCandidate.Reconstruction
