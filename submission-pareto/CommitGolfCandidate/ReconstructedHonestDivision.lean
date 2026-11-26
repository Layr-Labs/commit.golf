import CommitGolfCandidate.ReconstructedRadix

namespace CommitGolfCandidate.Reconstruction.HonestDivision

/-- The checker stores its 102-bit record header in four unsigned 32-bit limbs. -/
def limb : Nat := 2^32

/-- Interpret the limbs in the order visited by the checker's high-to-low division loop. -/
def assemble (start : Nat) : List Nat → Nat
  | [] => start
  | x :: xs => assemble (start*limb+x) xs

/-- Divide each 64-bit intermediate, write its low 32-bit quotient digit and
carry the remainder to the next limb. -/
def divide (base rem : Nat) : List Nat → List Nat × Nat
  | [] => ([],rem)
  | x :: xs =>
    let part := rem*limb+x
    let tail := divide base (part%base) xs
    ((part/base)%limb :: tail.1, tail.2)

private theorem column_bounds (base rem x : Nat) (small : base ≤ limb)
    (carry : rem < base) (word : x < limb) :
    rem*limb+x < 2^64 ∧ (rem*limb+x)/base < limb := by
  have bound : rem*limb+x < base*limb := by
    calc
      _ < rem*limb+limb := Nat.add_lt_add_left word _
      _ = (rem+1)*limb := (Nat.succ_mul rem limb).symm
      _ ≤ _ := Nat.mul_le_mul_right _ carry
  exact ⟨Nat.lt_of_lt_of_le bound (Nat.mul_le_mul_right _ small),
    (Nat.div_lt_iff_lt_mul (by omega)).2 (Nat.mul_comm base limb ▸ bound)⟩

private theorem shift_div (n x b : Nat) (pos : 0<b) :
    (n*limb+x)/b = (n/b)*limb+(n%b*limb+x)/b ∧
    (n*limb+x)%b = (n%b*limb+x)%b := by
  have expand : n*limb+x = (n%b*limb+x)+b*((n/b)*limb) := by
    calc
      _ = (n%b+b*(n/b))*limb+x := by rw [Nat.mod_add_div]
      _ = _ := by simp only [Nat.add_mul,Nat.mul_assoc]; ac_rfl
  rw [expand, Nat.add_mul_div_left _ _ pos, Nat.add_mul_mod_self_left]
  exact ⟨Nat.add_comm _ _, rfl⟩

/-- The whole machine-word loop simultaneously computes the true quotient and
remainder of the full header. The bounds justify every 64-bit intermediate
and 32-bit quotient write, including the most significant limb. -/
theorem divide_correct (base n : Nat) (xs : List Nat) (pos : 0 < base)
    (small : base ≤ limb) (words : ∀ x ∈ xs, x < limb) :
    let out := divide base (n%base) xs
    assemble (n/base) out.1 = (assemble n xs)/base ∧ out.2 = (assemble n xs)%base := by
  induction xs generalizing n with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    have limit := column_bounds base (n%base) x small (Nat.mod_lt _ pos) (words x (by simp))
    obtain ⟨quot,rem⟩ := shift_div n x base pos
    have tail := ih (n*limb+x) (fun y hy => words y (List.mem_cons_of_mem _ hy))
    simp only [quot,rem] at tail
    simpa only [divide,assemble,Nat.mod_eq_of_lt limit.2] using tail

/-- The four assignments to hdr[3..0] implement one mixed-radix extraction. -/
theorem four_limbs (base : Nat) (d3 d2 d1 d0 : Fin (2^32))
    (pos : 0 < base) (small : base ≤ limb) :
    let digits := [d3.val,d2.val,d1.val,d0.val]
    let out := divide base 0 digits
    assemble 0 out.1 = assemble 0 digits/base ∧ out.2 = assemble 0 digits%base := by
  have words : ∀ x ∈ [d3.val,d2.val,d1.val,d0.val], x < limb := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    all_goals exact Fin.isLt _
  simpa only [Nat.zero_div,Nat.zero_mod] using divide_correct base 0 _ pos small words


private theorem divide_bounds (base rem : Nat) (xs : List Nat) :
    ∀ x ∈ (divide base rem xs).1, x < limb := by
  induction xs generalizing rem with
  | nil => simp [divide]
  | cons word xs ih =>
    intro x hx
    simp only [divide,List.mem_cons] at hx
    rcases hx with rfl|mem
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ _ mem

/-- Each successful stage records one remainder in increasing significance order. -/
def extract : List Nat → List Nat → List Nat × List Nat
  | [], words => ([],words)
  | b :: bs, words =>
    let stage := divide b 0 words
    let result := extract bs stage.1
    (stage.2 :: result.1,result.2)

def digitList {bs : List Nat} : Digits bs → List Nat
  | .nil => []
  | .cons x tail => x.val :: digitList tail

theorem extract_packed {bs : List Nat} (ds : Digits bs) (words : List Nat)
    (wide : ∀ b ∈ bs, b ≤ limb) (fits : ∀ x ∈ words, x < limb)
    (packed : assemble 0 words = ds.pack.val) :
    (extract bs words).1 = digitList ds ∧ assemble 0 (extract bs words).2 = 0 := by
  induction ds generalizing words with
  | nil => exact ⟨rfl,packed⟩
  | @cons b bs d ds ih =>
    have pos : 0 < b := Nat.zero_lt_of_lt d.isLt
    have stage := divide_correct b 0 words pos (wide b (by simp)) fits
    simp only [Nat.zero_div,Nat.zero_mod,packed,Digits.pack, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt d.isLt, Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt d.isLt,
      Nat.zero_add] at stage
    have next := ih _ (fun r h => wide r (List.mem_cons_of_mem _ h)) (divide_bounds b 0 words) stage.1
    exact ⟨by simp only [extract,digitList,stage.2,next.1],next.2⟩

/-- The checker initializes four 32-bit words from the two serialized fields
`lo` (64 bits) and `hi` (38 bits). The result is in division traversal order. -/
def fromFields (lo hi : Nat) := [hi/limb%limb, hi%limb, lo/limb%limb, lo%limb]

private theorem field_bounds (lo hi : Nat) : ∀ x ∈ fromFields lo hi, x < limb := by
  intro x hx
  simp only [fromFields,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> exact Nat.mod_lt _ (by decide)

private theorem assemble_fields (n : Nat) (bound : n < 2^102) :
    assemble 0 (fromFields (n%2^64) (n/2^64)) = n := by
  simp only [assemble,fromFields,limb,Nat.zero_mul,Nat.zero_add]
  omega

/-- The ten successive hardware-style long divisions recover exactly the digits
sent by the opener. The terminal four-word header passes its zero check. -/
theorem record_roundtrip (digits : Digits sameSize.recordBases) :
    let header := (lowerHeader digits).val
    let words := fromFields (header%2^64) (header/2^64)
    let out := extract sameSize.recordBases words
    out.1 = digitList digits ∧ assemble 0 out.2 = 0 := by
  apply extract_packed digits
  · intro base member
    have small : sameSize.recordBases.all (· ≤ limb) = true := by decide
    simpa using (List.all_eq_true.mp small) base member
  · exact field_bounds _ _
  · exact assemble_fields _ (lowerHeader digits).isLt

end CommitGolfCandidate.Reconstruction.HonestDivision
