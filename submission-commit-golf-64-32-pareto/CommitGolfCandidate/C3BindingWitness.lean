import CommitGolfCandidate.C3LeafModel
import CommitGolfCandidate.TwoPermutationBindingBridge

/-! # Binding evidence for the 3c1p leaf

`C3LeafRows` is what one accepted check records for one opened position: the three
compression rows and the permutation row of the leaf. `c3_leaf_rows_conflict` is the
deterministic part of binding: two leaf computations at one position with different entries and
equal digests contain either a compression collision (`CompressionWitness`) or the
cross-oracle permutation event `C3PermWitness`. The probability of `C3PermWitness` is the
theorem `c3_perm_witness_bound` (module `C3PermWitnessBound`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp TwoPermutationPrototype.RV64

set_option autoImplicit false

/-- Two recorded permutation rows with different inputs and equal 256-bit output prefixes,
where the `t3` field (bits `1344..1600`) of each input is the reply of a recorded compression row.
Rows record the input and reply of a call in either direction. -/
def C3PermWitness (rows : List PublicRow) : Prop :=
  ∃ (input₀ input₁ reply₀ reply₁ : Block) (source₀ source₁ : BitVec 512),
    PublicRow.permutation input₀ reply₀ ∈ rows ∧ PublicRow.permutation input₁ reply₁ ∈ rows ∧
    PublicRow.compression source₀ (c3T3Field input₀) ∈ rows ∧
    PublicRow.compression source₁ (c3T3Field input₁) ∈ rows ∧
    input₀ ≠ input₁ ∧ outputDigest reply₀ = outputDigest reply₁

def C3ReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ C3PermWitness rows

theorem C3PermWitness.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (witness : C3PermWitness earlier) : C3PermWitness later := by
  obtain ⟨x₀, x₁, y₀, y₁, a₀, a₁, h₀, h₁, c₀, c₁, different, equal⟩ := witness
  exact ⟨x₀, x₁, y₀, y₁, a₀, a₁, contained _ h₀, contained _ h₁, contained _ c₀, contained _ c₁,
    different, equal⟩

theorem C3ReplayEvidence.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : C3ReplayEvidence earlier) : C3ReplayEvidence later := by
  rcases evidence with ⟨x, y, a, b, left, right, different, equal⟩ | witness
  · exact Or.inl ⟨x, y, a, b, contained _ left, contained _ right, different, equal⟩
  · exact Or.inr (witness.mono contained)

/-- The four rows of one leaf computation under the compression function `compress` and the
forward permutation `perm`. -/
structure C3LeafRows (rows : List PublicRow) (compress : Compression) (perm : Block → Block)
    (index : Index) (nonce : Words 2) (v : Words 32) : Prop where
  first : PublicRow.compression (c3FirstInput v) (c3T1 compress v) ∈ rows
  second : PublicRow.compression (c3SecondInput compress v) (c3T2 compress v) ∈ rows
  third : PublicRow.compression (c3ThirdInput compress v) (c3T3 compress v) ∈ rows
  final : PublicRow.permutation (c3PermInput compress index nonce v)
    (perm (c3PermInput compress index nonce v)) ∈ rows

theorem C3LeafRows.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    {compress : Compression} {perm : Block → Block} {index : Index} {nonce : Words 2} {v : Words 32}
    (leaf : C3LeafRows earlier compress perm index nonce v) : C3LeafRows later compress perm index nonce v :=
  ⟨contained _ leaf.first, contained _ leaf.second, contained _ leaf.third, contained _ leaf.final⟩

private theorem full_collision {rows : List PublicRow} {x y : BitVec 512} {a b : BitVec 256}
    (left : PublicRow.compression x a ∈ rows) (right : PublicRow.compression y b ∈ rows)
    (different : x ≠ y) (same : a = b) : CompressionWitness rows :=
  ⟨x, y, a, b, left, right, different, congrArg low240 same⟩

private theorem words8_congr {w₀ w₁ : Words 8} (same : packWords8 w₀ = packWords8 w₁) (k : Fin 8) :
    w₀ k = w₁ k := congrFun (pack_words8_injective same) k

theorem c3_leaf_rows_conflict (rows : List PublicRow) (compress : Compression) (perm : Block → Block)
    (index : Index) (nonce₀ nonce₁ : Words 2) (v₀ v₁ : Words 32)
    (left : C3LeafRows rows compress perm index nonce₀ v₀)
    (right : C3LeafRows rows compress perm index nonce₁ v₁)
    (digest : c3LeafDigest compress perm index nonce₀ v₀ = c3LeafDigest compress perm index nonce₁ v₁)
    (conflict : v₀ ≠ v₁) :
    C3ReplayEvidence rows := by
  by_cases samePerm : c3PermInput compress index nonce₀ v₀ = c3PermInput compress index nonce₁ v₁
  · -- equal permutation inputs: walk the compression chain
    have words := packBuffer_injective samePerm
    have low (k : Nat) (hk : k < 18) : v₀ ⟨k, by omega⟩ = v₁ ⟨k, by omega⟩ := by
      have := congrFun words ⟨k, by omega⟩
      simpa [c3PermWords, hk] using this
    have t3Words : digestWords (c3T3 compress v₀) = digestWords (c3T3 compress v₁) := by
      funext k
      have := congrFun words ⟨21 + k.val, by omega⟩
      have a : ¬ (21 + k.val < 18) := by omega
      have b : ¬ (21 + k.val = 18) := by omega
      have c : ¬ (21 + k.val < 21) := by omega
      simpa [c3PermWords, a, b, c] using this
    have t3 := digest_words_injective t3Words
    by_cases sameThird : c3ThirdInput compress v₀ = c3ThirdInput compress v₁
    · have third := pack_words8_injective sameThird
      have mid (k : Nat) (hk : k < 3) : v₀ ⟨18 + k, by omega⟩ = v₁ ⟨18 + k, by omega⟩ := by
        have := congrFun third ⟨k, by omega⟩
        simpa [c3ThirdWords, hk] using this
      have t2Words : digestWords (c3T2 compress v₀) = digestWords (c3T2 compress v₁) := by
        funext k
        have := congrFun third ⟨3 + k.val, by omega⟩
        have a : ¬ (3 + k.val < 3) := by omega
        have b : 3 + k.val < 7 := by omega
        simpa [c3ThirdWords, a, b] using this
      have t2 := digest_words_injective t2Words
      by_cases sameSecond : c3SecondInput compress v₀ = c3SecondInput compress v₁
      · have second := pack_words8_injective sameSecond
        have upper (k : Nat) (hk : k < 4) : v₀ ⟨20 + k, by omega⟩ = v₁ ⟨20 + k, by omega⟩ := by
          have := congrFun second ⟨k, by omega⟩
          simpa [c3SecondWords, hk] using this
        have t1Words : digestWords (c3T1 compress v₀) = digestWords (c3T1 compress v₁) := by
          funext k
          have := congrFun second ⟨4 + k.val, by omega⟩
          have a : ¬ (4 + k.val < 4) := by omega
          simpa [c3SecondWords, a] using this
        have t1 := digest_words_injective t1Words
        by_cases sameFirst : c3FirstInput v₀ = c3FirstInput v₁
        · have first := pack_words8_injective sameFirst
          have top (k : Nat) (hk : k < 8) : v₀ ⟨24 + k, by omega⟩ = v₁ ⟨24 + k, by omega⟩ := by
            have := congrFun first ⟨k, by omega⟩
            simpa [c3FirstWords] using this
          exfalso
          apply conflict
          funext k
          by_cases a : k.val < 18
          · exact low k.val a
          by_cases b : k.val < 20
          · have := mid (k.val - 18) (by omega)
            simpa [show 18 + (k.val - 18) = k.val by omega] using this
          by_cases c : k.val < 24
          · have := upper (k.val - 20) (by omega)
            simpa [show 20 + (k.val - 20) = k.val by omega] using this
          · have := top (k.val - 24) (by omega)
            simpa [show 24 + (k.val - 24) = k.val by omega] using this
        · exact Or.inl (full_collision left.first right.first sameFirst t1)
      · exact Or.inl (full_collision left.second right.second sameSecond t2)
    · exact Or.inl (full_collision left.third right.third sameThird t3)
  · -- different permutation inputs: the cross-oracle event
    refine Or.inr ⟨_, _, _, _, c3ThirdInput compress v₀, c3ThirdInput compress v₁,
      left.final, right.final, ?_, ?_, samePerm, digest⟩
    · rw [c3_t3_field_input]; exact left.third
    · rw [c3_t3_field_input]; exact right.third

end TwoPermutationPrototype.Sampling
