import CommitGolfCandidate.ReconstructedFrontier

namespace CommitGolfCandidate.Reconstruction.HonestHeap
open Frontier

/-- Level `d` uses heap indices [2^d,2^(d+1)) and a single guard cell
immediately after the level. -/
def addr (d k : Nat) := 4294971424 + 32*(k+d)
def guard (d : Nat) := addr d (2^(d+1))

theorem guard_gap (d : Nat) :
    guard d + 32 = addr (d+1) (2^(d+1)) := by
  simp [addr, guard]
  omega

theorem children (d k : Nat) (lo : 2^d ≤ k) (hi : k < 2^(d+1)) :
    2^(d+1) ≤ 2*k ∧ 2*k+1 < 2^(d+2) ∧
      addr (d+1) (2*k+1) = addr (d+1) (2*k) + 32 ∧
      addr d k + 64 ≤ addr (d+1) (2^(d+1)) := by
  have p := Nat.pow_succ 2 d
  have q : 2^(d+2) = 2^(d+1)*2 := Nat.pow_succ 2 (d+1)
  unfold addr
  omega

/-- The forward leaf syscall writes 200 bytes even though only its low digest
is kept. Its last write fits below every generator query window. -/
theorem leaf_write_fits (p : Fin (2^24)) :
    4096 + 256*(p.val+1) ≤ 4294971392 ∧
    4294971424 ≤ addr 24 (2^24+p.val) ∧
    addr 24 (2^24+p.val) + 200 ≤ 5637148528 - 16*8 := by
  have := p.isLt
  unfold addr
  omega

/-- The only earlier leaf overwritten by the first permutation is already
consumed. Bytes 168..255 survive to the second call, including the 32-byte
overlap with the original first input. -/
theorem leaf_windows (p : Fin (2^24)) :
    let m := 4096 + 256*p.val
    m-32+200 = m+168 ∧ m+56+24 = m+80 ∧ m+80+88 = m+168 ∧
      m+168+88 = m+256 ∧ m-120+200 = m+80 ∧
      m-120+23*8 = m+64 ∧ m-120+24*8 = m+72 := by
  dsimp only
  omega

private theorem scan_lengths (k : Nat) (bs : List Bool) :
    (scan k bs).1.length = bs.length / 2 ∧ (scan k bs).2.length ≤ bs.length / 2 := by
  match bs with
  | [] | [_] => simp [scan]
  | l :: r :: rs =>
    have tail := scan_lengths (k+2) rs
    cases l <;> cases r <;> simp [scan] <;> omega

private theorem flags_length (ps : List (Fin (2^24))) : (flags ps).length = 512 := by
  have fold (xs : List (Fin (2^24))) (bs : List Bool) : (xs.foldl mark bs).length = bs.length := by
    induction xs generalizing bs with
    | nil => rfl
    | cons x xs ih => simp [ih, mark]
  unfold flags
  rw [fold, List.length_replicate]

private theorem ordinary_bound (d : Nat) (bs : List Bool) (size : bs.length = 2^d) :
    ordinaryFields d bs ≤ 2^d-1 := by
  induction d generalizing bs with
  | zero => simp [ordinaryFields]
  | succ d ih =>
    have p := Nat.pow_succ 2 d
    have nz := Nat.two_pow_pos d
    have h := scan_lengths (2^(d+1)) bs
    have sub := ih _ (show (scan (2^(d+1)) bs).1.length = 2^d by omega)
    simp only [ordinaryFields]
    omega

/-- Coarse all-cardinality cap cost. The all-128 frontier theorem is sharper. -/
theorem cursor_all (ps : List (Fin (2^24))) :
    cursor ps ≤ 3633 * ps.length + 119472 := by
  have f := flags_length ps
  have a := scan_lengths 512 (flags ps)
  have b := scan_lengths 256 (scan 512 (flags ps)).1
  have c := ordinary_bound 7 (scan 256 (scan 512 (flags ps)).1).1 (by omega)
  cases s : scan 512 (flags ps) with
  | mk parents ids =>
    cases t : scan 256 parents with
    | mk next missing =>
      simp only [cursor, s, t] at a b c ⊢
      omega

/-- The loader capacity accommodates the entire index set and any subset, with
enough room for the last full doubleword read or write. -/
theorem all_fit (ps : List (Fin (2^24))) (count : ps.length ≤ 2^24) :
    alignedBytes (cursor ps) ≤ 7618968152 ∧
    alignedBytes (cursor ps) ≤ 8355061248 ∧
    10334769248 + alignedBytes (cursor ps) ≤ 2^36 := by
  have bound := cursor_all ps
  simp only [alignedBytes]
  omega

end CommitGolfCandidate.Reconstruction.HonestHeap
