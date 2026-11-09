import CommitGolf.Parameters
import Mathlib.Data.List.GetD

/-! # Packed delivered images

The manifest renderer stores at most 256 bytes per natural-number payload and joins chunks in
a balanced tree. The element-count index includes zero and final partial chunks. Decoding has the
same ordinary `List (BitVec bits)` representation as submitted images, without elaborating one
source constructor per byte. No native decoder or unchecked equality is used.

For large concrete images, simplify record projections with `simp only` before applying
`length_decode` or `getD_decode`. This avoids asking elaboration to reduce the materialized list
while matching a theorem's expected type. -/

namespace CommitGolf.ArtifactEncoding

/-- A little-endian chunk or concatenation, indexed by its exact number of elements. -/
inductive Packed : Nat → Type where
  | chunk (count payload : Nat) : Packed count
  | join {leftCount rightCount : Nat}
      (left : Packed leftCount) (right : Packed rightCount) : Packed (leftCount + rightCount)

/-- Read one fixed-width element. Branch counts guide the lookup; a chunk's low bits come first. -/
def Packed.get (bits : Nat) : {count : Nat} → Packed count → Fin count → BitVec bits
  | _, .chunk _ payload, index => BitVec.ofNat bits (payload >>> (bits * index.val))
  | _, @Packed.join leftCount rightCount left right, index =>
    if h : index.val < leftCount then left.get bits ⟨index.val, h⟩
    else right.get bits ⟨index.val - leftCount, by omega⟩

/-- Materialize the exact counted list. `List.ofFn` keeps length and indexed-read proofs small. -/
def decode (bits : Nat) {count : Nat} (packed : Packed count) : List (BitVec bits) :=
  List.ofFn (packed.get bits)

@[simp] theorem length_decode (bits : Nat) {count : Nat} (packed : Packed count) :
    (decode bits packed).length = count := by
  simp [decode]

/-- The list's indexed view is the same pure tree lookup, including boundary indices. -/
theorem getD_decode (bits : Nat) {count : Nat} (packed : Packed count)
    (index : Nat) (inside : index < count) :
    (decode bits packed).getD index 0 = packed.get bits ⟨index, inside⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using inside)]
  simp [decode]

@[simp] theorem get_chunk (bits count payload : Nat) (index : Fin count) :
    (Packed.chunk count payload).get bits index =
      BitVec.ofNat bits (payload >>> (bits * index.val)) := rfl

theorem get_join_left (bits : Nat) {leftCount rightCount : Nat}
    (left : Packed leftCount) (right : Packed rightCount) (index : Fin (leftCount + rightCount))
    (inside : index.val < leftCount) :
    (Packed.join left right).get bits index = left.get bits ⟨index.val, inside⟩ := by
  simp [Packed.get, inside]

theorem get_join_right (bits : Nat) {leftCount rightCount : Nat}
    (left : Packed leftCount) (right : Packed rightCount) (index : Fin (leftCount + rightCount))
    (outside : ¬ index.val < leftCount) :
    (Packed.join left right).get bits index =
      right.get bits ⟨index.val - leftCount, by omega⟩ := by
  simp [Packed.get, outside]

end CommitGolf.ArtifactEncoding
