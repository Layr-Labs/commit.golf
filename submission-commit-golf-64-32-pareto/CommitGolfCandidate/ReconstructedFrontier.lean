import CommitGolfCandidate.ReconstructedCap

namespace CommitGolfCandidate.Reconstruction.Frontier

/-- Scan consecutive heap pairs from left to right, as in the shared-cap loop.
The missing child of a singleton pair has heap index `k + left.toNat`. -/
def scan (k : Nat) : List Bool → List Bool × List Nat
  | l :: r :: rest =>
    let (parents, ids) := scan (k+2) rest
    ((l || r) :: parents, if l == r then ids else (k+l.toNat) :: ids)
  | _ => ([], [])

def active : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + active bs

private theorem active_le_length (bs : List Bool) : active bs ≤ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [active] <;> omega

private theorem scan_counts (k : Nat) (bs : List Bool) (even : bs.length % 2 = 0) :
    let p := (scan k bs).1
    let f := (scan k bs).2.length
    2*p.length = bs.length ∧ active p ≤ active bs ∧
    active bs + f = 2*active p ∧ f ≤ active bs := by
  match bs with
  | [] => simp [scan, active]
  | [_] => simp at even
  | l :: r :: rs =>
    have tail := scan_counts (k+2) rs (by simp at even; omega)
    dsimp only at tail ⊢
    cases l <;> cases r <;> simp [scan, active] <;> omega

/-- ABI leaf numbers are zero-based. After fifteen parent steps the opener
marks heap entry `512 + position / 32768`. The level starts at heap index 512. -/
def mark (flags : List Bool) (position : Fin (2^24)) :=
  flags.set (position.val / 32768) true

private theorem set_length (bs : List Bool) (i : Nat) : (bs.set i true).length = bs.length := by simp

private theorem set_active (bs : List Bool) (i : Nat) : active (bs.set i true) ≤ active bs + 1 := by
  induction bs generalizing i with
  | nil => simp [active]
  | cons b bs ih =>
    cases i with
    | zero => cases b <;> simp [active] <;> omega
    | succ i => simp only [List.set_cons_succ, active]; have := ih i; omega

def flags (positions : List (Fin (2^24))) := positions.foldl mark (List.replicate 512 false)

private theorem mark_fold (xs : List (Fin (2^24))) (bs : List Bool) :
    (xs.foldl mark bs).length = bs.length ∧ active (xs.foldl mark bs) ≤ active bs + xs.length := by
  induction xs generalizing bs with
  | nil => simp
  | cons p xs ih =>
    have h := ih (mark bs p)
    have b := set_active bs (p.val/32768)
    simp only [List.foldl_cons, List.length_cons]
    change active (mark bs p) ≤ active bs + 1 at b
    exact ⟨h.1.trans (set_length _ _), by omega⟩

/-- Cursor advancement at the seven ordinary levels, including levels with no missing siblings. -/
def ordinaryFields : Nat → List Bool → Nat
  | 0, _ => 0
  | d+1, bs =>
    let (next, ids) := scan (2^(d+1)) bs
    ids.length + ordinaryFields d next

private theorem ordinary_bound (d : Nat) (bs : List Bool) (len : bs.length = 2^d) :
    ordinaryFields d bs + active bs ≤ bs.length := by
  induction d generalizing bs with
  | zero => simpa [ordinaryFields] using active_le_length bs
  | succ d ih =>
    rw [Nat.pow_succ] at len
    have h := scan_counts (2^(d+1)) bs (by omega)
    dsimp only at h
    have tail :=  ih (scan (2^(d+1)) bs).1 (by omega)
    have small := active_le_length (scan (2^(d+1)) bs).1
    simp only [ordinaryFields]
    omega

def cursor (positions : List (Fin (2^24))) : Nat :=
  let (p8, f9) := scan 512 (flags positions)
  let (p7, f8) := scan 256 p8
  3633 * positions.length + 224*(f9.length+f8.length) +
    31*((f9.length+3)/4+(f8.length+3)/4) + 240*ordinaryFields 7 p7

theorem heap_endpoint (p : Fin (2^24)) :
    (2^24 + p.val)/2^15 = 512 + p.val/32768 ∧ p.val/32768 < 512 := by
  have := p.isLt
  omega

private theorem replicate_false (n : Nat) : active (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, active, ih]

/-- Bound the actual sequence of heap-level field counts for *every* list of
128 legal positions, including lists with repeated positions. -/
theorem cursor_bound (ps : List (Fin (2^24))) (batch : ps.length = 128) :
    cursor ps ≤ 524352 ∧ alignedBytes (cursor ps) ≤ 65544 := by
  have f := mark_fold ps (List.replicate 512 false)
  change (flags ps).length = _ ∧ active (flags ps) ≤ _ at f
  have empty := replicate_false 512
  rw [List.length_replicate, empty, Nat.zero_add, batch] at f
  have inner := scan_counts 512 (flags ps) (by omega)
  dsimp only at inner
  have outer := scan_counts 256 (scan 512 (flags ps)).1 (by omega)
  dsimp only at outer
  have cap := ordinary_bound 7 (scan 256 (scan 512 (flags ps)).1).1 (by omega)
  let n := (scan 512 (flags ps)).2.length
  let m := (scan 256 (scan 512 (flags ps)).1).2.length
  let b := active (scan 256 (scan 512 (flags ps)).1).1
  let ordinary := ordinaryFields 7 (scan 256 (scan 512 (flags ps)).1).1
  have h₁ : ordinary + b ≤ 128 := by dsimp [ordinary, b]; omega
  have h₂ : n + m ≤ 2*b := by dsimp [n,m,b]; omega
  have h₃ : n ≤ 128 := by dsimp [n]; omega
  have h₄ : m ≤ 128 := by dsimp [m]; omega
  have capBound : 240*ordinary + 224*(n+m) + 31*((n+3)/4+(m+3)/4) ≤ 59328 := by
    clear_value n m b ordinary
    omega
  change 3633 * ps.length + 224*(n+m)+31*((n+3)/4+(m+3)/4)+240*ordinary ≤ _ ∧ _
  change _ ∧ (3633 * ps.length + 224*(n+m)+31*((n+3)/4+(m+3)/4)+240*ordinary+63)/64*8 ≤ _
  omega

end CommitGolfCandidate.Reconstruction.Frontier
