import CommitGolfCandidate.Programs

/-! Arithmetic of the gap heap: node `s` at byte offset `heapOffset s = 32*(s + s/2)`.
Pair `q` (nodes `2q, 2q+1`) occupies `[96q, 96q+64)`; `[96q+64, 96q+96)` is a zero gap. -/
namespace CommitGolfCandidate

theorem heap_offset_even (q : Nat) : heapOffset (2*q) = 96*q := by
  unfold heapOffset; omega

theorem heap_offset_odd (q : Nat) : heapOffset (2*q+1) = 96*q+32 := by
  unfold heapOffset; omega

theorem heap_offset_aligned (node : Nat) : heapOffset node % 8 = 0 := by
  unfold heapOffset; omega

theorem heap_offset_mod32 (node : Nat) : heapOffset node % 32 = 0 := by
  unfold heapOffset; omega

/-- Distinct nodes occupy disjoint 32-byte slots. -/
theorem heap_offset_disjoint (a b : Nat) (different : a ≠ b) :
    heapOffset a + 32 ≤ heapOffset b ∨ heapOffset b + 32 ≤ heapOffset a := by
  unfold heapOffset; omega

/-- Every node below `2m` lies inside the first `96m` bytes. -/
theorem heap_offset_bound (node m : Nat) (inside : node < 2*m) : heapOffset node + 32 ≤ 96*m := by
  unfold heapOffset; omega

/-- No node slot meets a pair's zero gap. -/
theorem heap_offset_gap (node q : Nat) :
    heapOffset node + 32 ≤ 96*q+64 ∨ 96*q+96 ≤ heapOffset node := by
  unfold heapOffset; omega

theorem heap_offset_mono (a b : Nat) (le : a ≤ b) : heapOffset a ≤ heapOffset b := by
  unfold heapOffset; omega

theorem heap_offset_sibling_half (s : Nat) : (s ^^^ 1) / 2 = s / 2 := by
  have h : (s ^^^ 1) >>> 1 = (s >>> 1) ^^^ (1 >>> 1) := Nat.shiftRight_xor_distrib
  simp only [Nat.shiftRight_eq_div_pow] at h
  rw [h]
  simp

/-- The sibling's offset, as computed by the opening: `t = s xor 1`, `32*(t + s/2)`. -/
theorem heap_offset_sibling (s : Nat) : heapOffset (s ^^^ 1) = 32*((s ^^^ 1) + s/2) := by
  unfold heapOffset
  rw [heap_offset_sibling_half]

end CommitGolfCandidate
