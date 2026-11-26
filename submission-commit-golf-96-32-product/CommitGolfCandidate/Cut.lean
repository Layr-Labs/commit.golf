import CommitGolf.Parameters

namespace CommitGolfCandidate

/-! ### 240-bit storage of the nodes of heights 3..17 (A96)
A stored node of height `h` with `3 ≤ h ≤ 17` keeps only the low 240 bits of its compression output
(its top two bytes are zero in memory). The leaves (height 0), heights 1 and 2 and the upper tree
(heights 18..24, including the root) keep full digests. -/

def low240 (digest : BitVec 256) : BitVec 240 := digest.extractLsb' 0 240

/-- A 30-byte (240-bit) field zero-extended to a stored digest. -/
def widen (low : BitVec 240) : BitVec 256 := (0 : BitVec 16) ++ low

@[simp] theorem low240_widen (low : BitVec 240) : low240 (widen low) = low :=
  BitVec.extractLsb'_append_eq_right

theorem widen_injective {a b : BitVec 240} (same : widen a = widen b) : a = b := by
  simpa only [low240_widen] using congrArg low240 same

/-- The heights whose stored digests are truncated. -/
def CutHeight (height : Nat) : Prop := 3 ≤ height ∧ height ≤ 17

instance (height : Nat) : Decidable (CutHeight height) := by unfold CutHeight; infer_instance

/-- The stored form of a digest computed at `height`. -/
def cut (height : Nat) (digest : BitVec 256) : BitVec 256 :=
  if CutHeight height then widen (low240 digest) else digest

theorem cut_of_cut {height : Nat} (inside : CutHeight height) (digest : BitVec 256) :
    cut height digest = widen (low240 digest) := by unfold cut; simp [inside]

theorem cut_of_not {height : Nat} (outside : ¬ CutHeight height) (digest : BitVec 256) :
    cut height digest = digest := by unfold cut; simp [outside]

@[simp] theorem low240_cut (height : Nat) (digest : BitVec 256) : low240 (cut height digest) = low240 digest := by
  unfold cut; split <;> simp

theorem cut_widen (height : Nat) (low : BitVec 240) (inside : CutHeight height) :
    cut height (widen low) = widen low := by
  rw [cut_of_cut inside, low240_widen]

@[simp] theorem cut_cut (height : Nat) (digest : BitVec 256) : cut height (cut height digest) = cut height digest := by
  unfold cut; split <;> simp

/-- Equal stored digests at a truncated height have equal low 240 bits; elsewhere they are equal. -/
theorem cut_eq_cases (height : Nat) {a b : BitVec 256} (same : cut height a = cut height b) :
    (CutHeight height ∧ low240 a = low240 b) ∨ (¬ CutHeight height ∧ a = b) := by
  by_cases inside : CutHeight height
  · left; exact ⟨inside, by simpa only [low240_cut] using congrArg low240 same⟩
  · right; rw [cut_of_not inside, cut_of_not inside] at same; exact ⟨inside, same⟩

end CommitGolfCandidate
