import CommitGolfCandidate.PentaWrapExtend
import CommitGolfCandidate.PentaCapFacts
import CommitGolfCandidate.PentaGroupedContent
import CommitGolfCandidate.QuadCheckPentaInput

/-! The reconstruction of an honest level-7-table proof is the honest old-format cap proof: the hash
phase recomputes exactly the honest nodes of levels 8, 9 and 10.

Doubled-table word `x` (group `x / 40`, copy-independent slot `hSlotOf x`, word `(x % 40) % 20 % 4`)
of an honest proof holds word `(x % 40) % 20 % 4` of the honest node in slot `hSlotOf x`: slots
`0 … 214` are level 7, `215 … 259` level 8, `260 … 269` level 9 and `270 … 274` level 10. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuadCertificate (capCheckInput capCheckInputOld)

set_option maxRecDepth 100000

def hSlotOf (x : Nat) : Nat := 5*(x/40) + (x%40)%20/4
def hWordOf (x : Nat) : Nat := (x%40)%20%4
def lvlOf (s : Nat) : Nat := if s < 215 then 7 else if s < 260 then 8 else if s < 270 then 9 else 10
def idxOf (s : Nat) : Nat := if s < 215 then s else if s < 260 then s - 215 else if s < 270 then s - 260 else s - 270

def honestWord (penta : PentaFunction) (leaves : DigestTape) (x : Nat) : Word :=
  (pentaNode penta leaves (lvlOf (hSlotOf x)) (idxOf (hSlotOf x))).extractLsb' (64*hWordOf x) 64

def written (n s : Nat) : Prop := s ∈ (List.range n).map hashSlot

instance (n s : Nat) : Decidable (written n s) := by unfold written; infer_instance

theorem written_succ (n s : Nat) : written (n+1) s ↔ written n s ∨ s = hashSlot n := by
  unfold written
  simp only [List.range_succ, List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false]

theorem extract_extract {w : Nat} (x : BitVec w) (a b c d : Nat) (h : c + d ≤ b) :
    (x.extractLsb' a b).extractLsb' c d = x.extractLsb' (a+c) d := by
  ext k hk
  have : c + k < b := by omega
  simp [BitVec.getElem_extractLsb', this, Nat.add_assoc]

/-! ### Finite index facts -/

/-- The slots of a hash's destination words. -/
theorem dst_slots : ∀ i < 54, ∀ m < 4, hSlotOf (dstOff i + m) = hashSlot i ∧ hSlotOf (dstOff i + 20 + m) = hashSlot i ∧
    hWordOf (dstOff i + m) = m ∧ hWordOf (dstOff i + 20 + m) = m := by decide

/-- Source group `i` of hash `i`: its slot `5i + t` is level 7, already hashed, or a zero slot. -/
def zeroSlot (s : Nat) : Prop := s = 258 ∨ s = 259 ∨ s = 269 ∨ s = 272 ∨ s = 273 ∨ s = 274

instance (s : Nat) : Decidable (zeroSlot s) := by unfold zeroSlot; infer_instance

theorem source_ready : ∀ i < 54, ∀ t < 5, 5*i+t < 215 ∨ written i (5*i+t) ∨ zeroSlot (5*i+t) := by decide

theorem all_slots : ∀ s < 275, s < 215 ∨ written 54 s ∨ zeroSlot s := by decide

/-- The source group of hash `i` is the group of children of its destination node. -/
theorem hash_shape : ∀ i < 54, lvlOf (hashSlot i) = lvlOf (5*i) + 1 ∧
    (∀ t < 5, lvlOf (5*i+t) = lvlOf (5*i) ∧ idxOf (5*i+t) = 5*idxOf (hashSlot i) + t) ∧
    idxOf (hashSlot i) < pentaCount (lvlOf (hashSlot i)) := by decide

theorem zero_slot_node (penta : PentaFunction) (leaves : DigestTape) (s : Nat) (z : zeroSlot s) :
    pentaNode penta leaves (lvlOf s) (idxOf s) = 0 := by
  have counts : pentaCount 8 = 43 ∧ pentaCount 9 = 9 ∧ pentaCount 10 = 2 := by decide
  unfold zeroSlot at z
  rcases z with h | h | h | h | h | h <;> subst h <;>
    simp [lvlOf, idxOf, pentaNode, counts]

theorem written_mono (n s : Nat) (le : n ≤ 54) (h : written n s) : written 54 s := by
  unfold written at *
  simp only [List.mem_map, List.mem_range] at *
  obtain ⟨i, hi, e⟩ := h
  exact ⟨i, by omega, e⟩

theorem zero_never : ∀ s < 275, zeroSlot s → ¬ written 54 s := by decide

theorem zero_not_written (s : Nat) (hs : s < 275) (z : zeroSlot s) (n : Nat) (le : n ≤ 54) : ¬ written n s :=
  fun h => zero_never s hs z (written_mono n s le h)

/-! ### The hashed table of an honest proof -/

theorem slot_source (i r : Nat) (hr : r < 20) : hSlotOf (40*i + r) = 5*i + r/4 ∧ hWordOf (40*i + r) = r % 4 := by
  unfold hSlotOf hWordOf; constructor <;> omega

theorem slot_ne (i x : Nat) (hx : x < 2200)
    (lo : ¬(dstOff i ≤ x ∧ x < dstOff i + 4)) (hi : ¬(dstOff i + 20 ≤ x ∧ x < dstOff i + 24)) :
    hSlotOf x ≠ hashSlot i := by
  unfold hSlotOf dstOff at *
  omega

/-- The reply of hash `i` on a table whose source group is honest. -/
theorem honest_reply (o : Oracle) (leaves : DigestTape) (T : Nat → Word) (i : Nat) (hi : i < 54)
    (source : ∀ r < 20, T (40*i + r) = honestWord (pentaFunction (fun B => o.permutation B)) leaves (40*i + r))
    (m : Nat) (hm : m < 4) :
    replyWords (hashReply o T i) ⟨m, by omega⟩ =
      (pentaNode (pentaFunction (fun B => o.permutation B)) leaves (lvlOf (hashSlot i)) (idxOf (hashSlot i))).extractLsb'
        (64*m) 64 := by
  let P := pentaFunction (fun B => o.permutation B)
  obtain ⟨lv, shape, count⟩ := hash_shape i hi
  let c : Fin 5 → BitVec 256 := fun t => pentaNode P leaves (lvlOf (5*i)) (5*idxOf (hashSlot i) + t.val)
  have input : hashInput T i = replyWords (pentaInput c) := by
    funext j
    simp only [hashInput, replyWords]
    erw [Quad.Checker.penta_input_word c j]
    unfold Quad.Checker.pentaInputWords
    by_cases low : j.val < 5
    · rw [if_pos low, dif_pos low]
    · rw [if_neg low, dif_neg low, source _ (by have := j.isLt; omega)]
      obtain ⟨sl, wd⟩ := slot_source i (j.val - 5) (by have := j.isLt; omega)
      unfold honestWord
      rw [sl, wd]
      obtain ⟨l₁, i₁⟩ := shape ((j.val - 5)/4) (by have := j.isLt; omega)
      rw [l₁, i₁]
  have node : pentaNode P leaves (lvlOf (hashSlot i)) (idxOf (hashSlot i)) = P c := by
    rw [lv]
    rw [penta_node_succ P leaves _ _ (by rw [← lv]; exact count)]
    rfl
  rw [node]
  simp only [replyWords, hashReply, input, P, pentaFunction]
  erw [PentaGrouped.reply_pack]
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]
  rfl

theorem hash_table_honest (o : Oracle) (leaves : DigestTape) (T : Nat → Word)
    (base : ∀ x < 2200, T x = if hSlotOf x < 215 then honestWord (pentaFunction (fun B => o.permutation B)) leaves x else 0) :
    ∀ n ≤ 54, ∀ x < 2200, hashTable o T n x =
      if hSlotOf x < 215 ∨ written n (hSlotOf x) then honestWord (pentaFunction (fun B => o.permutation B)) leaves x
      else 0 := by
  let P := pentaFunction (fun B => o.permutation B)
  intro n
  induction n with
  | zero =>
    intro _ x hx
    show T x = _
    rw [base x hx]
    simp [written]
  | succ n ih =>
    intro le x hx
    have src : ∀ r < 20, hashTable o T n (40*n + r) = honestWord P leaves (40*n + r) := by
      intro r hr
      rw [ih (by omega) _ (by omega)]
      obtain ⟨sl, _⟩ := slot_source n r hr
      rw [sl]
      rcases source_ready n (by omega) (r/4) (by omega) with h | h | h
      · rw [if_pos (Or.inl h)]
      · rw [if_pos (Or.inr h)]
      · rw [if_neg (by
          intro c
          rcases c with c | c
          · unfold zeroSlot at h; omega
          · exact zero_not_written _ (by unfold zeroSlot at h; omega) h n (by omega) c)]
        unfold honestWord
        rw [sl, zero_slot_node P leaves _ h]
        simp
    obtain ⟨d₁, d₂, d₃⟩ := dst_facts n (by omega)
    show hashStep o (hashTable o T n) n x = _
    unfold hashStep
    by_cases lo : dstOff n ≤ x ∧ x < dstOff n + 4
    · rw [dif_pos lo]
      obtain ⟨s₁, _, w₁, _⟩ := dst_slots n (by omega) (x - dstOff n) (by omega)
      rw [show dstOff n + (x - dstOff n) = x by omega] at s₁ w₁
      rw [if_pos (Or.inr ((written_succ n _).mpr (Or.inr s₁))), honest_reply o leaves _ n (by omega) src _ (by omega)]
      unfold honestWord
      rw [s₁, w₁]
    · rw [dif_neg lo]
      by_cases hi : dstOff n + 20 ≤ x ∧ x < dstOff n + 24
      · rw [dif_pos hi]
        obtain ⟨_, s₂, _, w₂⟩ := dst_slots n (by omega) (x - dstOff n - 20) (by omega)
        rw [show dstOff n + 20 + (x - dstOff n - 20) = x by omega] at s₂ w₂
        rw [if_pos (Or.inr ((written_succ n _).mpr (Or.inr s₂))), honest_reply o leaves _ n (by omega) src _ (by omega)]
        unfold honestWord
        rw [s₂, w₂]
      · rw [dif_neg hi, ih (by omega) x hx]
        have ne := slot_ne n x hx lo hi
        have iff : written (n+1) (hSlotOf x) ↔ written n (hSlotOf x) := by
          rw [written_succ]; constructor
          · rintro (h | h); exact h; exact absurd h ne
          · exact Or.inl
        simp only [iff]

/-! ### Bytes and words of honest digests -/

theorem digest_byte (d : BitVec 256) (e : Nat) (he : e < 32) :
    (digestBytes d)[e]? = some (d.extractLsb' (8*e) 8) := by
  unfold digestBytes
  rw [List.getElem?_ofFn]
  simp only [List.ofFnNthVal, he, dite_true]

theorem pack_digest (d : BitVec 256) (m : Nat) (hm : m < 4) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8, (((digestBytes d)[8*m+j]?).getD 0).toNat * 2^(8*j)) =
      d.extractLsb' (64*m) 64 := by
  conv_rhs => rw [← pack_word_bytes (d.extractLsb' (64*m) 64)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [digest_byte d _ (by omega)]
  simp only [wordBytes, List.getElem?_ofFn, hj', dite_true, Option.getD_some]
  rw [extract_extract _ _ _ _ _ (by omega), show 64*m + 8*j = 8*(8*m+j) by ring]

theorem cap_level_byte (P : PentaFunction) (leaves : DigestTape) (k j e : Nat) (hj : j < capSlots k) (he : e < 32) :
    (capLevel P leaves k)[32*j+e]? = (digestBytes (pentaNode P leaves k j))[e]? := by
  unfold capLevel
  rw [flat_map_chunk _ 32 _ (fun x _ => digest_length _) j e he, List.getElem?_range hj, Option.bind_some]

theorem cap_level_length' (P : PentaFunction) (leaves : DigestTape) (k : Nat) :
    (capLevel P leaves k).length = 32 * capSlots k := by
  unfold capLevel
  rw [flat_map_length _ 32 _ (fun x _ => digest_length _)]
  simp

/-! ### The honest reconstruction -/

theorem ext_honest {sub : Submission} (lay : WrapLayout sub) (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) (nonempty : positions.card ≠ 0) :
    extInput oracle sub (capCheckInput oracle message positions salts) =
      capCheckInputOld oracle message positions salts := by
  let P := pentaFunction (fun B => oracle.permutation B)
  let leaves := pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts
  let input := capCheckInput oracle message positions salts
  let k := positions.card
  have card : k ≤ 16777216 := card_bound' positions
  have hP : pentaFunction (BiPermutation.equiv Block oracle.permutation).forward = P := rfl
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  let records := ordered.flatMap (fun index => capRecord P leaves index.val (salts index.val))
  have recLen : records.length = 912*k := by
    rw [flat_map_length _ 912 _ (fun x _ => cap_record_length _ _ _ _)]
    simp [ordered, k]
  have proofEq : input.proof = records ++ capLevel P leaves 7 := by
    show (capTranscriptBuilder _ _ _ _).2 = _
    simp only [capTranscriptBuilder, hP, if_neg nonempty]
    rfl
  have s7 := cap_slots_values
  -- the loader's doubled table is the honest level-7 table
  have base : ∀ x < 2200, initialTable sub input x = if hSlotOf x < 215 then honestWord P leaves x else 0 := by
    intro x hx
    unfold initialTable
    by_cases low : x < 1720
    · rw [if_pos low, if_pos (by unfold hSlotOf; omega)]
      unfold tableWord sourceWord
      rw [show input.positions.card = k from rfl, proof_word lay _ _ (by unfold proofWord; omega)]
      unfold honestWord
      rw [show hSlotOf x = 5*(x/40) + (x%40)%20/4 by unfold hSlotOf; rfl,
        show hWordOf x = (x%40)%20%4 by unfold hWordOf; rfl]
      simp only [lvlOf, idxOf, if_pos (show 5*(x/40) + (x%40)%20/4 < 215 by omega)]
      rw [← pack_digest _ _ (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [proofEq, List.getElem?_append_right (by rw [recLen]; omega), recLen,
        show 8*(114*k + 20*(x/40) + (x%40)%20) + j - 912*k = 32*(5*(x/40) + (x%40)%20/4) + (8*((x%40)%20%4) + j)
          by omega,
        cap_level_byte P leaves 7 _ _ (by rw [s7.1]; omega) (by omega)]
    · rw [if_neg low, if_neg (by unfold hSlotOf; omega)]
  have table : ∀ x < 2200, hashedTable oracle sub input x = honestWord P leaves x := by
    intro x hx
    rw [hashedTable, hash_table_honest oracle leaves _ base 54 le_rfl x hx]
    split
    · rfl
    · rename_i no
      rcases all_slots (hSlotOf x) (by unfold hSlotOf; omega) with a | a | a
      · exact absurd (Or.inl a) no
      · exact absurd (Or.inr a) no
      · unfold honestWord; rw [zero_slot_node P leaves _ a]; simp
  -- the reconstructed tail is levels 8, 9 and the first two slots of level 10
  have key : ∀ b < 1824, (tailBytes oracle sub input)[b]? =
      (digestBytes (pentaNode P leaves (lvlOf (215 + b/32)) (idxOf (215 + b/32))))[b%32]? := by
    intro b hb
    unfold tailBytes
    conv_lhs => rw [show b = 8*(b/8) + b%8 by omega]
    rw [flat_map_chunk _ 8 _ (fun x _ => word_bytes_length _) _ _ (by omega), List.getElem?_range (by omega),
      Option.bind_some]
    unfold tailWord
    rw [table _ (by omega)]
    unfold honestWord
    obtain ⟨sl, wd⟩ := slot_source (43 + b/8/20) (b/8%20) (by omega)
    rw [sl, wd, digest_byte _ _ (by omega)]
    simp only [wordBytes, List.getElem?_ofFn, show b%8 < 8 by omega, dite_true]
    rw [extract_extract _ _ _ _ _ (by omega), show 5*(43 + b/8/20) + b/8%20/4 = 215 + b/32 by omega,
      show 64*(b/8%20%4) + 8*(b%8) = 8*(b%32) by omega]
  have tail : tailBytes oracle sub input =
      capLevel P leaves 8 ++ capLevel P leaves 9 ++ (capLevel P leaves 10).take 64 := by
    obtain ⟨c8, c9, c10, c11⟩ : capSlots 7 = 215 ∧ capSlots 8 = 45 ∧ capSlots 9 = 10 ∧ capSlots 10 = 5 := s7
    have l9 := cap_level_length' P leaves 8
    have l10 := cap_level_length' P leaves 9
    rw [c9] at l9
    rw [c10] at l10
    apply List.ext_getElem?
    intro b
    by_cases inside : b < 1824
    · rw [key b inside]
      by_cases a8 : b < 1440
      · rw [List.append_assoc, List.getElem?_append_left (by omega)]
        conv_rhs => rw [show b = 32*(b/32) + b%32 by omega]
        rw [cap_level_byte P leaves 8 _ _ (by rw [c9]; omega) (by omega)]
        congr 3
        · simp only [lvlOf]; split_ifs <;> omega
        · simp only [idxOf]; split_ifs <;> omega
      · by_cases a9 : b < 1760
        · rw [List.append_assoc, List.getElem?_append_right (by omega), l9, List.getElem?_append_left (by omega)]
          conv_rhs => rw [show b - 32*45 = 32*((b-1440)/32) + (b-1440)%32 by omega]
          rw [cap_level_byte P leaves 9 _ _ (by rw [c10]; omega) (by omega), show (b - 1440) % 32 = b % 32 by omega]
          congr 3
          · simp only [lvlOf]; split_ifs <;> omega
          · simp only [idxOf]; split_ifs <;> omega
        · rw [List.append_assoc, List.getElem?_append_right (by omega), l9, List.getElem?_append_right (by omega),
            l10, List.getElem?_take, if_pos (by omega)]
          conv_rhs => rw [show b - 32*45 - 32*10 = 32*((b-1760)/32) + (b-1760)%32 by omega]
          rw [cap_level_byte P leaves 10 _ _ (by rw [c11]; omega) (by omega), show (b - 1760) % 32 = b % 32 by omega]
          congr 3
          · simp only [lvlOf]; split_ifs <;> omega
          · simp only [idxOf]; split_ifs <;> omega
    · rw [List.getElem?_eq_none (by rw [tail_bytes_length]; omega), List.getElem?_eq_none]
      simp only [List.length_append, List.length_take, l9, l10, cap_level_length', c11]
      omega
  -- assemble
  have oldProof : (capCheckInputOld oracle message positions salts).proof =
      records ++ (capTable P leaves).take 8704 := by
    show (capTranscriptBuilderOld _ _ _ _).2 = _
    simp only [capTranscriptBuilderOld, hP, if_neg nonempty]
    rfl
  have takeEq : (capTable P leaves).take 8704 =
      capLevel P leaves 7 ++ (capLevel P leaves 8 ++ capLevel P leaves 9 ++ (capLevel P leaves 10).take 64) := by
    have l7 := cap_level_length' P leaves 7
    have l8 := cap_level_length' P leaves 8
    have l9 := cap_level_length' P leaves 9
    rw [s7.1] at l7
    rw [s7.2.1] at l8
    rw [s7.2.2.1] at l9
    unfold capTable
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp [List.take_append, l7, l8, l9, List.take_of_length_le, List.append_assoc]
  show ({ input with proof := input.proof ++ tailBytes oracle sub input } : CheckInput) = _
  rw [tail, proofEq]
  have e : capCheckInputOld oracle message positions salts =
      { input with proof := (capCheckInputOld oracle message positions salts).proof } := rfl
  rw [e, oldProof, takeEq, List.append_assoc]

end TwoPermutationPrototype.PentaWrap
