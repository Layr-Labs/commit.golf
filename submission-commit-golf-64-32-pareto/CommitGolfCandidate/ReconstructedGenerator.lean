import Std

namespace CommitGolfCandidate.Reconstruction.Generator

/-- The first nonzero word moves within the query window. Group numbers are local to a tile. -/
def marker (group : Fin 342) := 1 + group.val % 16

def counter (tile : Fin 4096) (group : Fin 342) :=
  3896 + 256 * (4096 * tile.val + 192 * (group.val / 16))

abbrev Key := Fin 3 → BitVec 64

def inputWord (tile : Fin 4096) (group : Fin 342) (key : Key) (i : Nat) : BitVec 64 :=
  if i = marker group then -1
  else if i = marker group + 1 then BitVec.ofNat 64 (counter tile group)
  else if h : marker group + 4 ≤ i ∧ i < marker group + 7 then
    key ⟨i - (marker group + 4), by omega⟩
  else 0

theorem zero_before (t : Fin 4096) (g : Fin 342) (k : Key) (i : Nat) (h : i < marker g) :
    inputWord t g k i = 0 := by
  simp [inputWord, show i ≠ marker g by omega, show i ≠ marker g + 1 by omega,
    show ¬ (marker g + 4 ≤ i ∧ i < marker g + 7) by omega]

theorem separated_from_second_leaf (t : Fin 4096) (g : Fin 342) (k : Key) (i : Fin (2^24)) :
    inputWord t g k 0 ≠ BitVec.ofNat 64 (4152 + 256*i.val) := by
  rw [zero_before _ _ _ _ (by unfold marker; omega)]
  intro eq
  have := congrArg BitVec.toNat eq
  have hi := i.isLt
  have bound : 4152 + 256*i.val < 2^64 := by omega
  change 0 = (4152 + 256*i.val) % (2^64) at this
  rw [Nat.mod_eq_of_lt bound] at this
  omega

/-- Distinct block queries cannot alias, even for an all-zero private key. -/
theorem input_injective (t u : Fin 4096) (g h : Fin 342) (a b : Key)
    (eq : ∀ i < 25, inputWord t g a i = inputWord u h b i) : t = u ∧ g = h ∧ a = b := by
  have mg : marker g ≤ 16 := by unfold marker; omega
  have mh : marker h ≤ 16 := by unfold marker; omega
  have markers : marker g = marker h := by
    rcases Nat.lt_trichotomy (marker g) (marker h) with lt|same|gt
    · have e := eq (marker g) (by omega)
      rw [zero_before _ _ _ _ lt] at e
      simp [inputWord] at e
    · exact same
    · have e := eq (marker h) (by omega)
      rw [zero_before _ _ _ _ gt] at e
      simp [inputWord] at e
  have atCounter (v : Fin 4096) (w : Fin 342) (k : Key) :
      inputWord v w k (marker w + 1) = BitVec.ofNat 64 (counter v w) := by
    simp [inputWord]
  have e := eq (marker g + 1) (by omega)
  rw [atCounter, markers, atCounter] at e
  have counterBound (v : Fin 4096) (w : Fin 342) : counter v w < 2^64 := by
    have ht := v.isLt
    have hg := w.isLt
    have hb : w.val / 16 ≤ 21 := by omega
    unfold counter
    omega
  have ec := congrArg BitVec.toNat e
  change (counter t g) % (2^64) = (counter u h) % (2^64) at ec
  rw [Nat.mod_eq_of_lt (counterBound _ _), Nat.mod_eq_of_lt (counterBound _ _)] at ec
  have splitCounter (v : Fin 4096) (w : Fin 342) :
      (counter v w - 3896) / 256 / 4096 = v.val := by
    have bound := w.isLt
    have small : 192*(w.val/16) < 4096 := by omega
    simp [counter, Nat.mul_add_div (by decide : 0 < 4096), Nat.div_eq_of_lt small]
  have tiles : t.val = u.val := by rw [← splitCounter t g, ec, splitCounter u h]
  have groups : g.val = h.val := by
    unfold marker at markers
    unfold counter at ec
    rw [tiles] at ec
    omega
  have et := Fin.ext tiles
  have eg := Fin.ext groups
  subst u
  subst h
  refine ⟨rfl, rfl, ?_⟩
  funext j
  have hj := j.isLt
  have ek := eq (marker g + 4 + j.val) (by omega)
  simpa [inputWord, show marker g + 4 + j.val ≠ marker g by omega,
    show marker g + 4 + j.val ≠ marker g + 1 by omega,
    show marker g + 4 + j.val < marker g + 7 by omega] using ek

/-- Each 120-bit salt occupies two words, with eight high bits of the second word unused. -/
def saltBit (lane : Fin 12) (bit : Fin 120) : Nat :=
  (if lane.val = 0 then 23 else 2*(lane.val-1))*64 + bit.val

theorem salt_coordinates (i j : Fin 12) (x y : Fin 120) :
    saltBit i x < 1600 ∧ (saltBit i x = saltBit j y → i = j ∧ x = y) := by
  have hi := i.isLt
  have hj := j.isLt
  have hx := x.isLt
  have hy := y.isLt
  simp only [saltBit, Fin.ext_iff]
  split <;> split <;> omega

def tileOf (i : Fin (2^24)) : Fin 4096 := ⟨i.val / 4096, by have := i.isLt; omega⟩
def groupOf (i : Fin (2^24)) : Fin 342 := ⟨(i.val % 4096) / 12, by omega⟩
def laneOf (i : Fin (2^24)) : Fin 12 := ⟨(i.val % 4096) % 12, by omega⟩

theorem position_decomposition (i : Fin (2^24)) :
    4096*(tileOf i).val + 12*(groupOf i).val + (laneOf i).val = i.val := by
  simp only [tileOf, groupOf, laneOf]
  omega

/-- The opener derives the same address as the commitment's counter at every position,
including the four occupied lanes of the final group of each tile. -/
theorem opening_counter (i : Fin (2^24)) :
    4096 + 256*(i.val - (laneOf i).val - 12*((groupOf i).val % 16)) - 200 =
      counter (tileOf i) (groupOf i) := by
  have split := position_decomposition i
  unfold counter
  omega

/-- At a fixed key, the generator query and output coordinate determine both the position
and the selected bit of its salt. -/
theorem position_bit_injective (i j : Fin (2^24)) (x y : Fin 120) (k : Key)
    (sameQuery : ∀ n < 25, inputWord (tileOf i) (groupOf i) k n =
      inputWord (tileOf j) (groupOf j) k n)
    (sameBit : saltBit (laneOf i) x = saltBit (laneOf j) y) : i = j ∧ x = y := by
  obtain ⟨tiles, groups, _⟩ := input_injective _ _ _ _ _ _ sameQuery
  obtain ⟨lanes, bits⟩ := (salt_coordinates _ _ _ _).2 sameBit
  refine ⟨Fin.ext ?_, bits⟩
  calc i.val = _ := (position_decomposition i).symm
       _ = _ := by rw [tiles, groups, lanes]
       _ = j.val := position_decomposition j

theorem residual_bits : 1600 - 12*120 = 160 := by decide

end CommitGolfCandidate.Reconstruction.Generator
