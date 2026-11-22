import CommitGolfCandidate.Layout2Tables
import CommitGolfCandidate.GroupOpenModel

/-! # Opener Bridge: `Layout2.oldProofBytes` ↔ `GroupedOpening.proofFromTrapdoor`

Connects the pure field-level Layout 2 V1 description (`CommitGolfCandidate.Layout2`) directly to
the existing opener specification (`TwoPermutationPrototype.GroupedOpening.physicalRecord` and
`proofFromTrapdoor`), and derives the high-bit zero facts (`BandBClean`, Band-B all-8 clean, and
Band-A all-4 clean) from `upperHeap` so M3 can compose `convert_enc_oldProofBytes` without any
impedance mismatch. -/

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.Sampling
open TwoPermutationPrototype
open TwoPermutationPrototype.Opening (trapdoorHeap)

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by
  split
  · rfl
  · contradiction

private theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  split
  · contradiction
  · rfl

private theorem dite_pos {α : Sort _} {c : Prop} [Decidable c] {a : c → α} {b : ¬ c → α} (h : c) :
    (if hc : c then a hc else b hc) = a h := by
  split
  · rfl
  · contradiction

private theorem dite_neg {α : Sort _} {c : Prop} [Decidable c] {a : c → α} {b : ¬ c → α} (h : ¬ c) :
    (if hc : c then a hc else b hc) = b h := by
  split
  · contradiction
  · rfl

/-- Extract the logical `RecordFields` for one position from `(leaf, heap, quad, index, salt)`. -/
def recordFieldsOf (leaf heap : Nat → BitVec 256) (quad : BitVec 256) (index : Index)
    (salt : BitVec 128) : RecordFields where
  salt  := salt
  mate  := fun j => leaf (index.val ^^^ (j.val + 1))
  sib0  := quad
  sib1  := heap (upperNode index 1 ^^^ 1)
  bandA := fun a => heap (upperNode index (2 + a.val) ^^^ 1)
  bandB := fun j => heap (upperNode index (6 + j.val) ^^^ 1)

private def zeroRecordFields : RecordFields where
  salt  := 0
  mate  := fun _ => 0
  sib0  := 0
  sib1  := 0
  bandA := fun _ => 0
  bandB := fun _ => 0

/-- The `k`-th sorted position's `RecordFields` read from `trapdoor`. -/
def trapdoorRecordFields {s : Submission} (t : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (k : Nat) : RecordFields :=
  let ordered := positions.sort (· ≤ ·)
  if h : k < ordered.length then
    let i := ordered[k]
    recordFieldsOf (trapdoorLeaf (s := s) t) (trapdoorHeap (s := s) t)
      (trapdoorQuad (s := s) t i) i (trapdoorSalt (s := s) t i)
  else
    zeroRecordFields

private theorem getElem_append_nat {α : Type} (xs ys : List α) (i : Nat) (d : α) :
    (xs ++ ys)[i]?.getD d = if i < xs.length then xs[i]?.getD d else ys[i - xs.length]?.getD d := by
  by_cases h : i < xs.length
  · rw [ite_pos h, List.getElem?_append_left h]
  · rw [ite_neg h, List.getElem?_append_right (by omega)]

private theorem digestBytes_len (v : BitVec 256) : (digestBytes v).length = 32 := by
  simp [digestBytes]

private theorem saltBytes_len (v : BitVec 128) : (saltBytes v).length = 16 := by
  simp [saltBytes]

private theorem digestBytes_getD (v : BitVec 256) (i : Nat) (hi : i < 32) :
    (digestBytes v)[i]?.getD 0 = v.extractLsb' (8 * i) 8 := by
  unfold digestBytes; rw [List.getElem?_ofFn, dif_pos hi]; rfl

private theorem saltBytes_getD (v : BitVec 128) (i : Nat) (hi : i < 16) :
    (saltBytes v)[i]?.getD 0 = v.extractLsb' (8 * i) 8 := by
  unfold saltBytes; rw [List.getElem?_ofFn, dif_pos hi]; rfl

private theorem proofDigestBytes_false (v : BitVec 256) :
    proofDigestBytes false v = digestBytes v := by
  simp [proofDigestBytes]

private theorem proofDigestBytes_true (v : BitVec 256) :
    proofDigestBytes true v = (digestBytes v).take 30 := by
  simp [proofDigestBytes]

private theorem take_getD {α : Type} (xs : List α) (m i : Nat) (d : α) (hi : i < m) :
    (xs.take m)[i]?.getD d = xs[i]?.getD d := by
  rw [List.getElem?_take_of_lt hi]

private theorem foldSlot_getD (s top : BitVec 256) (k u : Nat) (hu : u < 30) :
    (foldSlot s top k)[u]?.getD 0 =
      if u < 28 then s.extractLsb' (8 * u) 8
      else (v1FoldHalf s top k).extractLsb' (8 * (u - 28)) 8 := by
  unfold foldSlot
  rw [getElem_append_nat]
  have hlen : ((digestBytes s).take 28).length = 28 := by simp [digestBytes]
  rw [hlen]
  by_cases h28 : u < 28
  · rw [ite_pos h28, ite_pos h28, take_getD _ _ _ _ h28, digestBytes_getD _ _ (by omega)]
  · rw [ite_neg h28, ite_neg h28]
    have hedge : u = 28 ∨ u = 29 := by omega
    rcases hedge with rfl | rfl <;> rfl

private theorem flatMap_const_len_getD {α : Type} (f : Nat → List α) (w : Nat)
    (hlen : ∀ j, (f j).length = w) :
    ∀ (m i : Nat) (d : α), i < w * m →
      ((List.range m).flatMap f)[i]?.getD d = (f (i / w))[i % w]?.getD d
  | 0, _, _, hi => absurd hi (by omega)
  | m + 1, i, d, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, getElem_append_nat]
    have hpre : ((List.range m).flatMap f).length = w * m := by
      rw [List.length_flatMap, List.map_congr_left (fun j _ => hlen j)]
      simp [Nat.mul_comm]
    rw [hpre]
    by_cases h : i < w * m
    · rw [ite_pos h]
      exact flatMap_const_len_getD f w hlen m i d h
    · rw [ite_neg h]
      have hdiv : i / w = m :=
        Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.mul_comm]; exact hi)
      have hmod : i % w = i - w * m := by
        have hq := Nat.div_add_mod i w
        rw [hdiv] at hq
        omega
      rw [hdiv, hmod]

private theorem physicalRecord_length (leaf heap : Nat → BitVec 256) (quad : BitVec 256)
    (index : Index) (salt : BitVec 128) :
    (physicalRecord leaf heap quad index salt).length = 534 := by
  unfold physicalRecord
  simp only [List.length_append, saltBytes_len, foldPack8_length, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, digestBytes_len]
  have hr6 : (List.range 6) = [0, 1, 2, 3, 4, 5] := by decide
  rw [hr6]
  simp [proofDigestBytes, digestBytes]

private theorem physical_split (leaf heap : Nat → BitVec 256) (quad : BitVec 256) (index : Index)
    (salt : BitVec 128) :
    physicalRecord leaf heap quad index salt =
      saltBytes salt ++ (digestBytes (leaf (index.val ^^^ 1)) ++ (digestBytes (leaf (index.val ^^^ 2)) ++
      (digestBytes (leaf (index.val ^^^ 3)) ++ (digestBytes quad ++ (digestBytes (heap (upperNode index 1 ^^^ 1)) ++
      ((digestBytes (heap (upperNode index 2 ^^^ 1))).take 30 ++ ((digestBytes (heap (upperNode index 3 ^^^ 1))).take 30 ++
      ((digestBytes (heap (upperNode index 4 ^^^ 1))).take 30 ++ ((digestBytes (heap (upperNode index 5 ^^^ 1))).take 30 ++
      ((List.range 7).flatMap (fun k => foldSlot (heap (upperNode index (6+k) ^^^ 1)) (heap (upperNode index (6+7) ^^^ 1)) k) ++
        (digestBytes (heap (upperNode index (6+7) ^^^ 1))).take 28)))))))))) := by
  unfold physicalRecord foldPack8
  rw [show (List.range 6)=[0, 1, 2, 3, 4, 5] by decide]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, proofDigestBytes,
    if_pos, if_neg]
  simp (config := {decide := true}) only [ite_true, ite_false, List.append_assoc, Nat.reduceAdd]

private theorem take_len (v : BitVec 256) (n : Nat) (h : n ≤ 32) : ((digestBytes v).take n).length=n := by
  rw [List.length_take, digestBytes_len]; omega

private theorem heap_byte (heap : Nat → BitVec 256) (n m i j : Nat) (hn : n=m) (hi : i=j) :
    (heap n).extractLsb' (8*i) 8=(heap m).extractLsb' (8*j) 8 := by subst hn; subst hi; rfl

/-- `oldRecordBytes` of `recordFieldsOf` is byte-for-byte identical to `GroupedOpening.physicalRecord`. -/
theorem oldRecordBytes_eq_physicalRecord (leaf heap : Nat → BitVec 256) (quad : BitVec 256)
    (index : Index) (salt : BitVec 128) :
    oldRecordBytes (recordFieldsOf leaf heap quad index salt) =
      physicalRecord leaf heap quad index salt := by
  apply List.ext_getElem
  · rw [oldRecordBytes_length, physicalRecord_length]
  · intro b h1 h2
    have hb : b < 534 := by simpa using h1
    have hget : (oldRecordBytes (recordFieldsOf leaf heap quad index salt))[b]?.getD 0 =
        (physicalRecord leaf heap quad index salt)[b]?.getD 0 := by
      have f7 : ((List.range 7).flatMap (fun k => foldSlot (heap (upperNode index (6+k) ^^^ 1))
          (heap (upperNode index (6+7) ^^^ 1)) k)).length=210 := by
        rw [List.length_flatMap, List.map_congr_left (fun _ _ => foldSlot_length _ _ _)]
        decide
      rw [physical_split]
      simp only [oldRecordBytes, List.getElem?_ofFn, hb, dite_true, Option.getD_some]
      simp only [getElem_append_nat, saltBytes_len, digestBytes_len, take_len _ 30 (by decide), f7]
      unfold oldRecordByte recordFieldsOf
      dsimp only
      by_cases c0 : b<16
      · simp only [c0, ite_true]; rw [saltBytes_getD _ _ c0]
      by_cases c1 : b<48
      · simp only [c0, c1, ite_true, ite_false, show b-16<32 by omega]
        rw [digestBytes_getD _ _ (by omega)]; rfl
      by_cases c2 : b<80
      · simp only [c0, c1, c2, ite_true, ite_false, show ¬ b-16<32 by omega, show b-16-32<32 by omega]
        rw [digestBytes_getD _ _ (by omega), show b-16-32=b-48 by omega]; rfl
      by_cases c3 : b<112
      · simp only [c0, c1, c2, c3, ite_true, ite_false, show ¬ b-16<32 by omega, show ¬ b-16-32<32 by omega,
          show b-16-32-32<32 by omega]
        rw [digestBytes_getD _ _ (by omega), show b-16-32-32=b-80 by omega]; rfl
      have n1 : ¬ b-16<32 := by omega
      have n2 : ¬ b-16-32<32 := by omega
      have n3 : ¬ b-16-32-32<32 := by omega
      by_cases c4 : b<144
      · simp only [c0, c1, c2, c3, c4, n1, n2, n3, ite_true, ite_false, show b-16-32-32-32<32 by omega]
        rw [digestBytes_getD _ _ (by omega), show b-16-32-32-32=b-112 by omega]
      have n4 : ¬ b-16-32-32-32<32 := by omega
      by_cases c5 : b<176
      · simp only [c0, c1, c2, c3, c4, c5, n1, n2, n3, n4, ite_true, ite_false, show b-16-32-32-32-32<32 by omega]
        rw [digestBytes_getD _ _ (by omega), show b-16-32-32-32-32=b-144 by omega]
      have n5 : ¬ b-16-32-32-32-32<32 := by omega
      have e6 : b-16-32-32-32-32-32=b-176 := by omega
      by_cases cA : b<296
      · simp only [c0, c1, c2, c3, c4, c5, cA, n1, n2, n3, n4, n5, ite_true, ite_false, dite_true, e6]
        rcases (show b-176<30 ∨ (30 ≤ b-176 ∧ b-176<60) ∨ (60 ≤ b-176 ∧ b-176<90) ∨ (90 ≤ b-176 ∧ b-176<120) by omega)
          with r|r|r|r
        · simp only [r, ite_true]
          rw [take_getD _ 30 _ _ r, digestBytes_getD _ _ (by omega)]
          exact heap_byte heap _ _ _ _ (by rw [show (b-176)/30=0 by omega]) (by omega)
        · simp only [show ¬ b-176<30 by omega, show b-176-30<30 by omega, ite_true, ite_false]
          rw [take_getD _ 30 _ _ (by omega), digestBytes_getD _ _ (by omega)]
          exact heap_byte heap _ _ _ _ (by rw [show (b-176)/30=1 by omega]) (by omega)
        · simp only [show ¬ b-176<30 by omega, show ¬ b-176-30<30 by omega, show b-176-30-30<30 by omega,
            ite_true, ite_false]
          rw [take_getD _ 30 _ _ (by omega), digestBytes_getD _ _ (by omega)]
          exact heap_byte heap _ _ _ _ (by rw [show (b-176)/30=2 by omega]) (by omega)
        · simp only [show ¬ b-176<30 by omega, show ¬ b-176-30<30 by omega, show ¬ b-176-30-30<30 by omega,
            show b-176-30-30-30<30 by omega, ite_true, ite_false]
          rw [take_getD _ 30 _ _ (by omega), digestBytes_getD _ _ (by omega)]
          exact heap_byte heap _ _ _ _ (by rw [show (b-176)/30=3 by omega]) (by omega)
      have e7 : b-176-30-30-30-30=b-296 := by omega
      simp only [c0, c1, c2, c3, c4, c5, cA, n1, n2, n3, n4, n5, ite_true, ite_false, dite_false, e6,
        show ¬ b-176<30 by omega, show ¬ b-176-30<30 by omega, show ¬ b-176-30-30<30 by omega,
        show ¬ b-176-30-30-30<30 by omega, e7]
      by_cases cB : b<506
      · simp only [cB, dite_true, show b-296<210 by omega, ite_true]
        rw [flatMap_const_len_getD _ 30 (fun _ => foldSlot_length _ _ _) 7 (b-296) 0 (by omega),
          foldSlot_getD _ _ _ _ (Nat.mod_lt _ (by decide))]
        rfl
      · simp only [cB, dite_false, show ¬ b-296<210 by omega, ite_false]
        rw [show b-296-210=b-506 by omega, take_getD _ 28 _ _ (by omega), digestBytes_getD _ _ (by omega)]
        rfl
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hget
    simpa using hget

private theorem flatMap_range_eq {α β : Type} (l : List α) (g : α → List β) (G : Nat → List β)
    (h : ∀ k (hk : k < l.length), G k = g l[k]) : (List.range l.length).flatMap G = l.flatMap g := by
  induction l generalizing G with
  | nil => rfl
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    congr 1
    · exact h 0 (by simp)
    · exact ih (fun k => G (k+1)) (fun k hk => h (k+1) (by simp; omega))

/-- `oldProofBytes` of `trapdoorRecordFields` and `foldNodes` equals `GroupedOpening.proofFromTrapdoor`. -/
theorem oldProofBytes_eq_proofFromTrapdoor {s : Submission} (t : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) :
    oldProofBytes positions.card (trapdoorRecordFields (s := s) t positions)
      (foldNodes ((Opening.openingNodes positions).map (trapdoorHeap (s := s) t))) =
      proofFromTrapdoor (s := s) t positions := by
  unfold oldProofBytes oldBlockBytes proofFromTrapdoor
  congr 1
  have hlen : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  rw [← hlen]
  apply flatMap_range_eq
  intro k hk
  unfold trapdoorRecordFields
  dsimp only
  rw [dif_pos hk]
  exact oldRecordBytes_eq_physicalRecord _ _ _ _ _

/-! ### High-Bit Zero Facts on Honest `upperHeap` (Band A and Band B) -/

private theorem sibling_bounds (u lo hi : Nat) (hlo : 2 * lo ≤ u) (hhi : u < 2 * hi) :
    2 * lo ≤ u ^^^ 1 ∧ u ^^^ 1 < 2 * hi := by
  rw [Quartet.xor_one_cases]
  split_ifs <;> omega

/-- Every stored node of depth `17..20` (`2^17 ≤ n < 2^21`) has bits `240..255` zero. -/
theorem upper_heap_high_240 (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) (n : Nat) (low : 2 ^ 17 ≤ n) (high : n < 2 ^ 21) :
    (Quartet.upperHeap lookup compress leaves n).extractLsb' 240 16 = 0 := by
  have stored := (Quartet.upper_heap_parent lookup compress leaves n (by omega) (by omega)).trans
    (node_keep_240 low high _)
  rw [stored]
  unfold CommitGolfCandidate.ShortTree.padLow
  exact BitVec.extractLsb'_append_eq_left

/-- When bits `240..255` of a 256-bit Band-A digest are zero, loading its top 64-bit dword
(`ld t6, 24(t2)`) directly equals the zero-extended 48-bit tail without masking. -/
theorem tail48_eq_word64 (v : BitVec 256) (clean : v.extractLsb' 240 16 = 0) :
    (v.extractLsb' 192 48).zeroExtend 64 = v.extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  by_cases h48 : i < 48
  · simp [hi, h48]
  · simp only [hi, h48, decide_false, Bool.false_and, decide_true, Bool.true_and]
    have hbit := congrArg (fun w : BitVec 16 => w.getLsbD (i - 48)) clean
    have hz : (0 : BitVec 16).getLsbD (i - 48) = false := by simp
    rw [BitVec.getLsbD_extractLsb', hz] at hbit
    simp only [show i - 48 < 16 by omega,
      decide_true, Bool.true_and, show 240 + (i - 48) = 192 + i by omega] at hbit
    exact hbit.symm

/-- Heap index range for Band-A siblings (`l = 2 + a`, `a < 4`): `[2^17, 2^21)`. -/
theorem bandA_sibling_range (index : Index) (a : Fin 4) :
    2 ^ 17 ≤ upperNode index (2 + a.val) ^^^ 1 ∧ upperNode index (2 + a.val) ^^^ 1 < 2 ^ 21 := by
  have hi : index.val < 16777216 := index.isLt
  rw [upper_node_heap_index]
  have ha : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 := by omega
  rcases ha with h | h | h | h <;> rw [h] <;> simp only [Nat.reducePow, Nat.reduceAdd] <;>
    exact sibling_bounds _ 65536 1048576 (by omega) (by omega)

/-- Heap index range for all 8 Band-B siblings (`l = 6 + j`, `j < 8`): `(0, 2^17)`. -/
theorem bandB_sibling_range (index : Index) (j : Fin 8) :
    0 < upperNode index (6 + j.val) ^^^ 1 ∧ upperNode index (6 + j.val) ^^^ 1 < 2 ^ 17 := by
  have hi : index.val < 16777216 := index.isLt
  rw [upper_node_heap_index]
  have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
      j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 := by omega
  rcases hj with h | h | h | h | h | h | h | h <;> rw [h] <;> simp only [Nat.reducePow, Nat.reduceAdd] <;>
    exact ⟨lt_of_lt_of_le (by decide : 0 < 2*1) (sibling_bounds _ 1 65536 (by omega) (by omega)).1,
      (sibling_bounds _ 1 65536 (by omega) (by omega)).2⟩

/-- On an honest `upperHeap`, all 4 Band-A siblings have bits `240..255` zero. -/
theorem bandAClean_of_upperHeap (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) (leaf : Nat → BitVec 256) (quad : BitVec 256) (index : Index)
    (salt : BitVec 128) (a : Fin 4) :
    ((recordFieldsOf leaf (Quartet.upperHeap lookup compress leaves) quad index salt).bandA a).extractLsb' 240 16 = 0 := by
  have hr := bandA_sibling_range index a
  exact upper_heap_high_240 lookup compress leaves _ hr.1 hr.2

/-- On an honest `upperHeap`, all 8 Band-B siblings have bits `238..255` zero. -/
theorem bandBAllClean_of_upperHeap (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) (leaf : Nat → BitVec 256) (quad : BitVec 256) (index : Index)
    (salt : BitVec 128) (j : Fin 8) :
    ((recordFieldsOf leaf (Quartet.upperHeap lookup compress leaves) quad index salt).bandB j).extractLsb' 238 18 = 0 := by
  have hr := bandB_sibling_range index j
  exact upper_heap_high lookup compress leaves _ hr.1 hr.2

/-- On an honest `upperHeap`, `BandBClean` holds directly (discharging the cleanliness hypothesis of
`convert_enc_oldProofBytes`). -/
theorem bandBClean_of_upperHeap (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) (leaf : Nat → BitVec 256) (quad : BitVec 256) (index : Index)
    (salt : BitVec 128) :
    BandBClean (recordFieldsOf leaf (Quartet.upperHeap lookup compress leaves) quad index salt) :=
  fun j => bandBAllClean_of_upperHeap lookup compress leaves leaf quad index salt ⟨j.val, by omega⟩

/-- Headline opener bridge: on any trapdoor whose Band-B siblings satisfy `BandBClean`,
`convert encTables positions.card (proofFromTrapdoor t positions)` equals the explicit
phase-by-phase Layout 2 V1 bytes `newProofBytes` followed by the unchanged `foldNodes` cap. -/
theorem convert_enc_proofFromTrapdoor {s : Submission} (t : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions)
    (clean : ∀ i < positions.card, BandBClean (trapdoorRecordFields (s := s) t positions i)) :
    convert encTables positions.card (proofFromTrapdoor (s := s) t positions) =
      newProofBytes positions.card (trapdoorRecordFields (s := s) t positions)
        (foldNodes ((Opening.openingNodes positions).map (trapdoorHeap (s := s) t))) := by
  rw [← oldProofBytes_eq_proofFromTrapdoor (s := s) t positions]
  exact convert_enc_oldProofBytes positions.card (trapdoorRecordFields (s := s) t positions) _ clean

end CommitGolfCandidate.Layout2
