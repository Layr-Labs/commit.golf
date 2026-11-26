import CommitGolfCandidate.C3PLeafModel
import CommitGolfCandidate.C3BindingWitness

/-! # Binding evidence for the paired 3c1p leaf

`C3PLeafRows` is what one accepted check records for one opened position: the three compression
rows and the permutation row of the leaf. `c3p_leaf_rows_conflict` is the deterministic part of
binding: two leaf computations at one position with different entries and equal digests contain
a compression collision (`CompressionWitness`) or a cross-oracle event of the position's window
shape (`C3PPermWitness`). Both leaves of a conflict sit at one position, so they have one parity.

`C3PShapeWitness zField digest` generalizes the unpaired `C3PermWitness`, which is the shape
`(c3T3Field, outputDigest)`. The paired leaf has two shapes:

* even: `zField` bits 1088..1344 of the input (`c3pEvenZField`), digest bits 1344..1600 of the
  reply (`c3pEvenDigest`);
* odd: `zField` bits 256..512 of the input (`c3pOddZField`), digest bits 0..256 (`outputDigest`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp TwoPermutationPrototype.RV64

set_option autoImplicit false

/-- Two recorded permutation rows with different inputs and equal `digest` windows of their
replies, where the `zField` of each input is the reply of a recorded compression row. -/
def C3PShapeWitness (zField digest : Block → BitVec 256) (rows : List PublicRow) : Prop :=
  ∃ (input₀ input₁ reply₀ reply₁ : Block) (source₀ source₁ : BitVec 512),
    PublicRow.permutation input₀ reply₀ ∈ rows ∧ PublicRow.permutation input₁ reply₁ ∈ rows ∧
    PublicRow.compression source₀ (zField input₀) ∈ rows ∧
    PublicRow.compression source₁ (zField input₁) ∈ rows ∧
    input₀ ≠ input₁ ∧ digest reply₀ = digest reply₁

/-- The cross-oracle event of the paired leaf: one of its two window shapes. -/
def C3PPermWitness (rows : List PublicRow) : Prop :=
  C3PShapeWitness c3pEvenZField c3pEvenDigest rows ∨ C3PShapeWitness c3pOddZField outputDigest rows

def C3PReplayEvidence (rows : List PublicRow) : Prop :=
  CompressionWitness rows ∨ C3PPermWitness rows

theorem C3PShapeWitness.mono {zField digest : Block → BitVec 256} {earlier later : List PublicRow}
    (contained : ∀ row ∈ earlier, row ∈ later)
    (witness : C3PShapeWitness zField digest earlier) : C3PShapeWitness zField digest later := by
  obtain ⟨x₀, x₁, y₀, y₁, a₀, a₁, h₀, h₁, c₀, c₁, different, equal⟩ := witness
  exact ⟨x₀, x₁, y₀, y₁, a₀, a₁, contained _ h₀, contained _ h₁, contained _ c₀, contained _ c₁,
    different, equal⟩

theorem C3PPermWitness.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (witness : C3PPermWitness earlier) : C3PPermWitness later := by
  rcases witness with even | odd
  · exact Or.inl (even.mono contained)
  · exact Or.inr (odd.mono contained)

theorem C3PReplayEvidence.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    (evidence : C3PReplayEvidence earlier) : C3PReplayEvidence later := by
  rcases evidence with ⟨x, y, a, b, left, right, different, equal⟩ | witness
  · exact Or.inl ⟨x, y, a, b, contained _ left, contained _ right, different, equal⟩
  · exact Or.inr (witness.mono contained)

/-- The four rows of one paired-leaf computation under the compression function `compress` and
the forward permutation `perm`. -/
structure C3PLeafRows (rows : List PublicRow) (compress : Compression) (perm : Block → Block)
    (index : Index) (nonce : Words 2) (v : Words 32) : Prop where
  q : PublicRow.compression (c3pQInput v) (c3pQ compress v) ∈ rows
  r : PublicRow.compression (c3pRInput v) (c3pR compress v) ∈ rows
  z : PublicRow.compression (c3pZInput compress v) (c3pZ compress v) ∈ rows
  final : PublicRow.permutation (c3pPermInput compress index nonce v)
    (perm (c3pPermInput compress index nonce v)) ∈ rows

theorem C3PLeafRows.mono {earlier later : List PublicRow} (contained : ∀ row ∈ earlier, row ∈ later)
    {compress : Compression} {perm : Block → Block} {index : Index} {nonce : Words 2} {v : Words 32}
    (leaf : C3PLeafRows earlier compress perm index nonce v) : C3PLeafRows later compress perm index nonce v :=
  ⟨contained _ leaf.q, contained _ leaf.r, contained _ leaf.z, contained _ leaf.final⟩

private theorem full_collision {rows : List PublicRow} {x y : BitVec 512} {a b : BitVec 256}
    (left : PublicRow.compression x a ∈ rows) (right : PublicRow.compression y b ∈ rows)
    (different : x ≠ y) (same : a = b) : CompressionWitness rows :=
  ⟨x, y, a, b, left, right, different, congrArg low240 same⟩

/-- Equal `z` inputs with equal `q` and `r` inputs give equal entry words outside `v[lo..hi)`;
otherwise a full compression collision. -/
private theorem c3p_outer_words (rows : List PublicRow) (compress : Compression) (perm : Block → Block)
    (index : Index) (nonce₀ nonce₁ : Words 2) (v₀ v₁ : Words 32)
    (left : C3PLeafRows rows compress perm index nonce₀ v₀)
    (right : C3PLeafRows rows compress perm index nonce₁ v₁)
    (sameZ : c3pZ compress v₀ = c3pZ compress v₁) :
    CompressionWitness rows ∨
      ((∀ k : Nat, (hk : k < 8) → v₀ ⟨k, by omega⟩ = v₁ ⟨k, by omega⟩) ∧
        (∀ k : Nat, (hk : k < 8) → v₀ ⟨24 + k, by omega⟩ = v₁ ⟨24 + k, by omega⟩)) := by
  by_cases sameZInput : c3pZInput compress v₀ = c3pZInput compress v₁
  · have zWords := pack_words8_injective sameZInput
    have qWords : digestWords (c3pQ compress v₀) = digestWords (c3pQ compress v₁) := by
      funext k
      have := congrFun zWords ⟨k.val, by omega⟩
      simpa [c3pZWords, k.isLt] using this
    have rWords : digestWords (c3pR compress v₀) = digestWords (c3pR compress v₁) := by
      funext k
      have := congrFun zWords ⟨4 + k.val, by omega⟩
      have a : ¬ (4 + k.val < 4) := by omega
      simpa [c3pZWords, a] using this
    have sameQ := digest_words_injective qWords
    have sameR := digest_words_injective rWords
    by_cases sameQInput : c3pQInput v₀ = c3pQInput v₁
    · by_cases sameRInput : c3pRInput v₀ = c3pRInput v₁
      · have qIn := pack_words8_injective sameQInput
        have rIn := pack_words8_injective sameRInput
        refine Or.inr ⟨fun k hk => ?_, fun k hk => ?_⟩
        · have := congrFun qIn ⟨k, hk⟩
          simpa [c3pQWords] using this
        · have := congrFun rIn ⟨k, hk⟩
          simpa [c3pRWords] using this
      · exact Or.inl (full_collision left.r right.r sameRInput sameR)
    · exact Or.inl (full_collision left.q right.q sameQInput sameQ)
  · exact Or.inl (full_collision left.z right.z sameZInput sameZ)

theorem c3p_leaf_rows_conflict (rows : List PublicRow) (compress : Compression) (perm : Block → Block)
    (index : Index) (nonce₀ nonce₁ : Words 2) (v₀ v₁ : Words 32)
    (left : C3PLeafRows rows compress perm index nonce₀ v₀)
    (right : C3PLeafRows rows compress perm index nonce₁ v₁)
    (digest : c3pLeafDigest compress perm index nonce₀ v₀ = c3pLeafDigest compress perm index nonce₁ v₁)
    (conflict : v₀ ≠ v₁) :
    C3PReplayEvidence rows := by
  by_cases samePerm : c3pPermInput compress index nonce₀ v₀ = c3pPermInput compress index nonce₁ v₁
  · have words := packBuffer_injective samePerm
    by_cases even : c3pEven index
    · have mid (k : Nat) (hk : k < 17) : v₀ ⟨7 + k, by omega⟩ = v₁ ⟨7 + k, by omega⟩ := by
        have := congrFun words ⟨k, by omega⟩
        simpa [c3pPermWords, even, c3pEvenWords, hk] using this
      have zWords : digestWords (c3pZ compress v₀) = digestWords (c3pZ compress v₁) := by
        funext k
        have := congrFun words ⟨17 + k.val, by omega⟩
        have a : ¬ (17 + k.val < 17) := by omega
        have b : 17 + k.val < 21 := by omega
        simpa [c3pPermWords, even, c3pEvenWords, a, b] using this
      rcases c3p_outer_words rows compress perm index nonce₀ nonce₁ v₀ v₁ left right
        (digest_words_injective zWords) with collision | ⟨low, high⟩
      · exact Or.inl collision
      · exfalso
        apply conflict
        funext k
        by_cases a : k.val < 8
        · exact low k.val a
        by_cases b : k.val < 24
        · have := mid (k.val - 7) (by omega)
          simpa [show 7 + (k.val - 7) = k.val by omega] using this
        · have := high (k.val - 24) (by omega)
          simpa [show 24 + (k.val - 24) = k.val by omega] using this
    · have mid (k : Nat) (hk : 8 ≤ k) (hk' : k < 25) : v₀ ⟨k, by omega⟩ = v₁ ⟨k, by omega⟩ := by
        have := congrFun words ⟨k, by omega⟩
        have a : ¬ (k < 2) := by omega
        have b : ¬ (k = 2) := by omega
        have c : ¬ (k = 3) := by omega
        have d : ¬ (k < 8) := by omega
        simpa [c3pPermWords, even, c3pOddWords, a, b, c, d] using this
      have zWords : digestWords (c3pZ compress v₀) = digestWords (c3pZ compress v₁) := by
        funext k
        have := congrFun words ⟨4 + k.val, by omega⟩
        have a : ¬ (4 + k.val < 2) := by omega
        have b : ¬ (4 + k.val = 2) := by omega
        have c : ¬ (4 + k.val = 3) := by omega
        have d : 4 + k.val < 8 := by omega
        simpa [c3pPermWords, even, c3pOddWords, a, b, c, d] using this
      rcases c3p_outer_words rows compress perm index nonce₀ nonce₁ v₀ v₁ left right
        (digest_words_injective zWords) with collision | ⟨low, high⟩
      · exact Or.inl collision
      · exfalso
        apply conflict
        funext k
        by_cases a : k.val < 8
        · exact low k.val a
        by_cases b : k.val < 25
        · exact mid k.val (by omega) b
        · have := high (k.val - 24) (by omega)
          simpa [show 24 + (k.val - 24) = k.val by omega] using this
  · by_cases even : c3pEven index
    · refine Or.inr (Or.inl ⟨_, _, _, _, c3pZInput compress v₀, c3pZInput compress v₁,
        left.final, right.final, ?_, ?_, samePerm, ?_⟩)
      · rw [c3p_even_z_field compress index even]; exact left.z
      · rw [c3p_even_z_field compress index even]; exact right.z
      · simpa [c3pLeafDigest, c3pDigestWindow, even] using digest
    · refine Or.inr (Or.inr ⟨_, _, _, _, c3pZInput compress v₀, c3pZInput compress v₁,
        left.final, right.final, ?_, ?_, samePerm, ?_⟩)
      · rw [c3p_odd_z_field compress index even]; exact left.z
      · rw [c3p_odd_z_field compress index even]; exact right.z
      · simpa [c3pLeafDigest, c3pDigestWindow, even] using digest

end TwoPermutationPrototype.Sampling
