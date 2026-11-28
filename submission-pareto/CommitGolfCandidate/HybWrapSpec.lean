import CommitGolfCandidate.PentaWrapLoader
import CommitGolfCandidate.QuadCertificate

/-! The hybrid checker wrapper's expansion of a compact proof (720-byte records, then the 164
level-13 nodes) into the donor's 2072-byte records, at the level of doublewords.

Donor word `v` (record `r = v / 259`, offset `e = v % 259`) is: the two salt words of compact
record `r` (`e < 2`); the virtual index of the record's position (`e = 2`); for the 5-ary levels
`k < 2` the compact rotation words; for the 4-ary level `k = 2` (digit `d`, virtual digit `d + 1`)
the four other slots `(d + j + 2) % 5` in rotation order: slot 0 is zero, slot `s ≥ 1` is compact
sibling `(s + 6 - d) % 4`; for the binary levels `3 ≤ k < 13` four sibling words at block words
`0-3` (even node, slot 3) or `12-15` (odd, slot 4) and zeros elsewhere; for the 5-ary levels
`13 ≤ k < 17` the four other slots of the record's group in rotation order, from `up`, the level
13-16 nodes recomputed from the table (`upNode`). -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 (memoryView wordAddress)
open TwoPermutationPrototype.PentaWrap (WrapLayout proofWord PENTA_PROOF_BASE proof_word loader_word
  lower_input_byte)

/-- Little-endian doubleword `u` of a byte list (zero past its end). -/
def packWord (proof : Proof) (u : Nat) : Word :=
  BitVec.ofNat 64 (∑ j ∈ Finset.range 8, ((proof[8*u+j]?).getD 0).toNat * 2^(8*j))

/-- Little-endian 32-byte digest at byte `off`. -/
def digestAt (proof : Proof) (off : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (∑ j ∈ Finset.range 32, ((proof[off+j]?).getD 0).toNat * 2^(8*j))

/-- Level-12 node `j` of a compact proof for `positions`. -/
def tableNode (positions : Positions) (proof : Proof) (j : Nat) : BitVec 256 :=
  digestAt proof (720*positions.card+32*j)

/-- The nodes of levels `12 + m`, recomputed from the table with the permutation `π`. -/
def upNode (π : Block → Block) (positions : Positions) (proof : Proof) : Nat → Nat → BitVec 256
  | 0, j => if j < pentaCount 12 then tableNode positions proof j else 0
  | m+1, j => if j < pentaCount (12+m+1) then
      pentaFunction π (fun t => upNode π positions proof m (5*j+t.val)) else 0

/-- Donor doubleword `v`. -/
def expandedWord (positions : Positions) (proof : Proof) (up : Nat → Nat → BitVec 256) (v : Nat) : Word :=
  let r := v/259
  let e := v%259
  let i := sortedIndex positions r
  if e < 2 then packWord proof (90*r+e)
  else if e = 2 then BitVec.ofNat 64 (virtIndex i)
  else
    let k := (e-3)/16
    let m := (e-3)%16
    if k < 3 then packWord proof (90*r+2+16*k+m)
    else
      let n := i/placeValue k
      if k = 3 then
        (if (n%3+m/4+3)%5 < 2 then 0 else packWord proof (90*r+50+4*(((n%3+m/4+3)%5+6-n%3)%3)+m%4))
      else if k < 12 then
        (if m/4 = 3*(n%2) then packWord proof (90*r+58+4*(k-4)+m%4) else 0)
      else (up (k-12) (5*(n/5)+(n%5+m/4+1)%5)).extractLsb' (64*(m%4)) 64

def expandProof (positions : Positions) (proof : Proof) (up : Nat → Nat → BitVec 256) : Proof :=
  (List.range (259*positions.card)).flatMap fun v => wordBytes (expandedWord positions proof up v)

theorem expand_proof_length (positions : Positions) (proof : Proof) (up : Nat → Nat → BitVec 256) :
    (expandProof positions proof up).length = 2072*positions.card := by
  unfold expandProof
  simp only [List.length_flatMap, wordBytes, List.length_ofFn, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  ring

/-- The donor's input after the wrapper, for the oracle `o`. -/
def expandInput (o : Oracle) (input : CheckInput) : CheckInput :=
  { input with proof := (expandProof input.positions input.proof (upNode o.permutation input.positions input.proof)) }

/-- Exact length of a compact proof. -/
def compactLength (positions : Positions) : Nat :=
  720*positions.card + (if positions.card = 0 then 0 else 5600)

/-! ### Words of byte lists -/

theorem word_bytes_length (w : Word) : (wordBytes w).length = 8 := by simp [wordBytes]

private theorem sum_digits (value count : Nat) :
    ∑ j ∈ Finset.range count, value / 2^(8*j) % 256 * 2^(8*j) = value % 2^(8*count) := by
  induction count with
  | zero => simp [Nat.mod_one]
  | succ c ih =>
    rw [Finset.sum_range_succ, ih, show 8*(c+1) = 8*c+8 by ring, pow_add, Nat.mod_mul,
      Nat.mul_comm (2^(8*c)) (value / 2^(8*c) % 2^8), show (2:Nat)^8 = 256 by norm_num]

theorem pack_word_bytes (w : Word) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (((wordBytes w)[j]?).getD 0).toNat * 2^(8*j)) = w := by
  apply BitVec.eq_of_toNat_eq
  have term : ∀ j ∈ Finset.range 8, (((wordBytes w)[j]?).getD 0).toNat * 2^(8*j) =
      w.toNat / 2^(8*j) % 256 * 2^(8*j) := by
    intro j hj
    have hj8 := Finset.mem_range.mp hj
    simp only [wordBytes, List.getElem?_ofFn, hj8, dite_true, Option.getD_some, BitVec.extractLsb'_toNat]
    congr 1
    rw [Nat.shiftRight_eq_div_pow]
  rw [Finset.sum_congr rfl term, sum_digits, BitVec.toNat_ofNat]
  have := w.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt this]

/-- Indexing a flattening of equal-length chunks. -/
theorem flat_map_chunk {α β : Type} (f : α → List β) (c : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = c) → ∀ i j, j < c →
      (l.flatMap f)[c*i + j]? = (l[i]?).bind (fun x => (f x)[j]?)
  | [], _, i, j, _ => by simp
  | x :: rest, same, i, j, hj => by
    have hx := same x (by simp)
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero, Option.bind_some]
      rw [List.getElem?_append_left (by omega)]
    | succ i =>
      simp only [List.flatMap_cons, List.getElem?_cons_succ]
      rw [Nat.mul_succ, List.getElem?_append_right (by omega), hx, show c*i+c+j-c = c*i+j by omega]
      exact flat_map_chunk f c rest (fun y hy => same y (by simp [hy])) i j hj

theorem flat_map_length {α β : Type} (f : α → List β) (c : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = c) → (l.flatMap f).length = c*l.length
  | [], _ => by simp
  | x :: rest, same => by
    rw [List.flatMap_cons, List.length_append, same x (by simp),
      flat_map_length f c rest (fun y hy => same y (by simp [hy]))]
    simp [Nat.mul_succ]; omega

/-- Doubleword `v` of a flattening of doublewords. -/
theorem pack_flat (f : Nat → Word) (count v : Nat) (inside : v < count) :
    packWord ((List.range count).flatMap fun x => wordBytes (f x)) v = f v := by
  unfold packWord
  have chunk (j : Nat) (hj : j < 8) :
      (((List.range count).flatMap fun x => wordBytes (f x))[8*v+j]?) = ((wordBytes (f v))[j]?) := by
    have h := flat_map_chunk (fun x => wordBytes (f x)) 8 (List.range count)
      (fun x _ => word_bytes_length _) v j hj
    rw [h, List.getElem?_range inside]
    rfl
  rw [Finset.sum_congr rfl (fun j hj => by rw [chunk j (Finset.mem_range.mp hj)])]
  exact pack_word_bytes (f v)

/-! ### The loader state of the expanded input -/

/-- On aligned words, the loader state of the expansion is the loader state of the compact input
below the proof buffer, the donor words over the records and zero after them. -/
theorem expanded_loader {sub : Submission} (lay : WrapLayout sub) (o : Oracle) (input : CheckInput)
    (w : Nat) (small : w < 2^33) :
    memoryView (sub.initialState .check (expandInput o input)) w =
      if w < proofWord then memoryView (sub.initialState .check input) w
      else if w < proofWord + 259*input.positions.card then
        expandedWord input.positions input.proof (upNode o.permutation input.positions input.proof) (w - proofWord)
      else 0 := by
  have card : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  by_cases low : w < proofWord
  · rw [if_pos low, loader_word _ w small, loader_word _ w small]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj8 := Finset.mem_range.mp hj
    rw [show expandInput o input = { input with proof := (expandInput o input).proof } from rfl,
      lower_input_byte lay input _ _ (by unfold proofWord at low; unfold PENTA_PROOF_BASE; omega)]
  · obtain ⟨u, rfl⟩ : ∃ u, w = proofWord + u := ⟨w - proofWord, by omega⟩
    rw [proof_word lay (expandInput o input) u small, if_neg (by omega)]
    by_cases area : u < 259*input.positions.card
    · rw [if_pos (by omega), show proofWord + u - proofWord = u by omega]
      have := pack_flat (expandedWord input.positions input.proof (upNode o.permutation input.positions input.proof))
        (259*input.positions.card) u area
      exact this
    · rw [if_neg (by omega)]
      have past : ∀ j < 8, (expandInput o input).proof[8*u+j]? = none := by
        intro j hj
        apply List.getElem?_eq_none
        rw [show (expandInput o input).proof = expandProof input.positions input.proof _ from rfl,
          expand_proof_length]
        omega
      rw [Finset.sum_congr rfl (fun j hj => by rw [past j (Finset.mem_range.mp hj)])]
      simp

end TwoPermutationPrototype.HybWrap
