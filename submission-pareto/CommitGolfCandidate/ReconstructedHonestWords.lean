import CommitGolfCandidate.ReconstructedProfile

namespace CommitGolfCandidate.Reconstruction.HonestWords

/-- Every non-root child has 192 unmodified low bits and a depth-dependent top word. -/
abbrev ChildDepth := Fin 24
def width (d : ChildDepth) := sameSize.widths[d.val+1]?.getD 0 - 192
def low (d : ChildDepth) := sameSize.lows[d.val+1]?.getD 0 - 192
def radix (d : ChildDepth) := sameSize.bases[d.val+1]?.getD 0
def modulus (d : ChildDepth) := sameSize.moduli[d.val+1]?.getD 0

private theorem table :
    ∀ d : ChildDepth,
      low d ≤ width d ∧ width d ≤ 48 ∧
      (if modulus d = 0 then 2 ^ width d else modulus d) = radix d * 2 ^ low d ∧
      (if modulus d = 0 then 2 ^ width d else modulus d) ≤ 2 ^ width d := by decide

/-- The canonical top word used by the checker. -/
def top (d : ChildDepth) (reply : Nat) :=
  reply % (if modulus d = 0 then 2 ^ width d else modulus d)

private theorem top_bounds (d : ChildDepth) (reply : Nat) :
    top d reply < radix d * 2 ^ low d ∧ top d reply < 2 ^ width d := by
  obtain ⟨_, _, equation, bound⟩ := table d
  have pos : ∀ d : ChildDepth, 0 < (if modulus d = 0 then 2 ^ width d else modulus d) := by decide
  have h := Nat.mod_lt reply (pos d)
  exact ⟨equation ▸ h, Nat.lt_of_lt_of_le h bound⟩

/-- Intermediate padding fills bits above the canonical width. The top 16 bits
are assigned separately when constructing the compression operand. -/
def padding (bits : Nat) := 2^64 - 2^bits
def tag (d : ChildDepth) := if d.val+1 = 24 then 65535 else d.val+1
def placeTag (d : ChildDepth) (word : Nat) := tag d * 2^48 + word % 2^48

def treeWord (d : ChildDepth) (right : Bool) (reply : Nat) :=
  if modulus d = 0 then placeTag d (reply ||| padding (width d))
  else if right then placeTag d (top d reply) else top d reply

def getTop (d : ChildDepth) (stored : Nat) := stored &&& (2 ^ width d - 1)

private theorem unmixed_pad (d : ChildDepth) :
    padding (width d) % 2 ^ width d = 0 := by
  exact (by decide : ∀ e : ChildDepth, padding (width e) % 2 ^ width e = 0) d

private theorem untag (d : ChildDepth) (word : Nat) :
    placeTag d word % 2 ^ width d = word % 2 ^ width d := by
  have nested := Nat.pow_dvd_pow 2 (table d).2.1
  have multiple : 2^width d ∣ tag d * 2^48 := Nat.dvd_trans nested (Nat.dvd_mul_left _ _)
  unfold placeTag
  simp only [Nat.add_mod, Nat.mod_eq_zero_of_dvd multiple, Nat.zero_add,
    Nat.mod_mod_of_dvd _ nested, Nat.mod_mod]

/-- The opener recovers the canonical word from every stored child, including any
right child whose marker has already been added in place. -/
theorem reader_word (d : ChildDepth) (r : Bool) (reply : Nat) :
    getTop d (treeWord d r reply) = top d reply := by
  have bounded := (top_bounds d reply).2
  unfold getTop treeWord
  rw [Nat.and_two_pow_sub_one_eq_mod]
  by_cases h : modulus d = 0
  · simp [h, untag, Nat.or_mod_two_pow, unmixed_pad, top]
  · cases r <;> simp [h, untag, Nat.mod_eq_of_lt bounded]

/-- The low field and radix digit used in both the lower records and shared cap. -/
def splitWord (d : ChildDepth) (stored : Nat) :=
  (stored &&& (2 ^ low d - 1), getTop d stored >>> low d)

private theorem low_mask (d : ChildDepth) (r : Bool) (reply : Nat) :
    treeWord d r reply % 2 ^ low d = top d reply % 2 ^ low d := by
  have same := reader_word d r reply
  rw [getTop, Nat.and_two_pow_sub_one_eq_mod] at same
  rw [← same, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (table d).1)]

/-- Every transmitted digit fits its declared base and decodes to the original
canonical top word for every compression or permutation reply. -/
theorem split_roundtrip (d : ChildDepth) (r : Bool) (reply : Nat) :
    let fields := splitWord d (treeWord d r reply)
    fields.2 < radix d ∧ fields.1 ||| (fields.2 <<< low d) = top d reply := by
  simp only [splitWord, reader_word, Nat.and_two_pow_sub_one_eq_mod, low_mask,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have b := (top_bounds d reply).1
  have m := Nat.mod_lt (top d reply) (Nat.two_pow_pos (low d))
  refine ⟨(Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 b, ?_⟩
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt m]
  exact Nat.div_add_mod _ _

/-- If the low-width projection and the padded word have the same low bits,
replacing all high bits by ones gives the same compression operand. -/
private theorem pad_id (d : ChildDepth) (reply : BitVec 64) :
    ((reply.toNat % 2^width d) ||| padding (width d)) = reply.toNat ||| padding (width d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have bound := (table d).2.1
  have mask : (padding (width d)).testBit i =
      (decide (i < 64) && !decide (i < width d)) := by
    have pw : 2 ^ width d = 2 ^ width d - 1 + 1 :=
      (Nat.sub_add_cancel (Nat.two_pow_pos _)).symm
    have small : 2 ^ width d - 1 < 2^64 := by
      have : 2^width d ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by omega)
      have := Nat.two_pow_pos (width d)
      omega
    unfold padding
    conv => lhs; rw [pw, Nat.testBit_two_pow_sub_succ small, Nat.testBit_two_pow_sub_one]
  by_cases large : 64 ≤ i
  · have beyond := Nat.pow_le_pow_right (n := 2) (by decide) large
    have zero := Nat.testBit_lt_two_pow (x := reply.toNat) (i := i) (Nat.lt_of_lt_of_le reply.isLt beyond)
    simp [Nat.testBit_or, Nat.testBit_mod_two_pow, zero]
  · by_cases included : i < width d <;> simp [Nat.testBit_or, Nat.testBit_mod_two_pow, mask,
      included, show i < 64 by omega]

def checkerWord (d : ChildDepth) (right : Bool) (word : Nat) :=
  if modulus d = 0 then placeTag d (word ||| padding (width d))
  else if right then placeTag d word else word

/-- The checker and commitment supply identical full 64-bit child words to the
binary compression. This includes the ordinary children of paid parents. -/
theorem parent_input (d : ChildDepth) (r : Bool) (reply : BitVec 64) :
    checkerWord d r (top d reply.toNat) = treeWord d r reply.toNat := by
  by_cases h : modulus d = 0
  · simp only [checkerWord, treeWord, top, h, ite_true, pad_id]
  · simp [checkerWord, treeWord, h]

end CommitGolfCandidate.Reconstruction.HonestWords
