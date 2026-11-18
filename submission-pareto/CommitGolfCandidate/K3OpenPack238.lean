import CommitGolfCandidate.QuartetConcrete

/-!
# The T238 packed sibling block, writer side (K3-DESIGN §9.2, §9.5)

Specification (GQ, `Quartet.packEight`): eight nodes take 238 bytes; slot `k < 7` is the 30 little-endian bytes of
`low238 s_k` with bits `224+2k, 225+2k` of `s_7` at bits 238, 239 (`Quartet.packedSlot`), then the 28 low bytes of
`s_7`. The opener writes it as plain 30-byte node copies, then ORs two bits of `s_7` into each slot's halfword 14
(`foldPack8`). `fold_pack8`: for nodes whose bits `238..255` are zero the two agree.
-/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

/-- Halfword 14 of slot `k` after the writer's `lhu; slli 14; or; sh`. -/
def foldHalf (s top : BitVec 256) (k : Nat) : BitVec 16 :=
  s.extractLsb' 224 16 ||| ((top.extractLsb' 224 16 >>> (2*k)) <<< 14)

/-- Slot `k` as the writer leaves it. -/
def foldSlot (s top : BitVec 256) (k : Nat) : List Byte :=
  (digestBytes s).take 28 ++ [(foldHalf s top k).extractLsb' 0 8, (foldHalf s top k).extractLsb' 8 8]

/-- The block as the writer leaves it. -/
def foldPack8 (s : Nat → BitVec 256) : List Byte :=
  (List.range 7).flatMap (fun k => foldSlot (s k) (s 7) k) ++ (digestBytes (s 7)).take 28

theorem foldSlot_length (s top : BitVec 256) (k : Nat) : (foldSlot s top k).length = 30 := by
  simp [foldSlot, digestBytes]

theorem foldPack8_length (s : Nat → BitVec 256) : (foldPack8 s).length = 238 := by
  simp [foldPack8, List.length_flatMap, foldSlot_length, digestBytes]

private theorem slot_bytes (v : BitVec 256) : proofDigestBytes true v = (digestBytes v).take 30 := by
  simp [proofDigestBytes]

/-- Bits of a specified slot word (GQ's `packedSlot` text, read at its natural width). -/
theorem slot_getLsbD (c : BitVec 2) (s : BitVec 256) (i : Nat) :
    @BitVec.getLsbD 256 ((0 : BitVec 16) ++ (c ++ s.extractLsb' 0 238)) i =
      if i < 238 then s.getLsbD i else if i < 240 then c.getLsbD (i - 238) else false := by
  change @BitVec.getLsbD (16 + (2 + 238)) ((0 : BitVec 16) ++ (c ++ s.extractLsb' 0 238)) i = _
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases low : i < 238
  · simp [low, show i < 240 by omega]
  · by_cases mid : i < 240
    · simp [low, mid]
    · simp [low, mid]

/-- With bits `238..255` of `s` zero, the writer's slot `k` is the specified slot. -/
theorem fold_slot (s top : BitVec 256) (k : Nat) (hk : k < 7) (high : s.extractLsb' 238 18 = 0) :
    foldSlot s top k = Quartet.packedSlot s (top.extractLsb' (224 + 2*k) 2) := by
  have top0 : s.getLsbD 238 = false := by
    have bit := congrArg (fun v : BitVec 18 => v.getLsbD 0) high
    simpa [BitVec.getLsbD_extractLsb'] using bit
  have top1 : s.getLsbD 239 = false := by
    have bit := congrArg (fun v : BitVec 18 => v.getLsbD 1) high
    simpa [BitVec.getLsbD_extractLsb'] using bit
  have top0e : s[238] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact top0
  have top1e : s[239] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact top1
  have spare0 : 2 * k < 16 := by omega
  have spare1 : 2 * k + 1 < 16 := by omega
  unfold Quartet.packedSlot foldSlot
  rw [slot_bytes]
  apply List.ext_getElem (by simp [digestBytes])
  intro i h₁ h₂
  have i30 : i < 30 := by simpa [digestBytes] using h₁
  by_cases low : i < 28
  · rw [List.getElem_append_left (by simpa [digestBytes] using low)]
    simp only [List.getElem_take, digestBytes, List.getElem_ofFn]
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [BitVec.getElem_extractLsb', BitVec.getElem_extractLsb', slot_getLsbD]
    have inside : 8 * i + j < 238 := by omega
    simp [inside]
  · have edge : i = 28 ∨ i = 29 := by omega
    rcases edge with rfl | rfl
    · rw [List.getElem_append_right (by simp [digestBytes])]
      simp only [List.getElem_take, digestBytes, List.getElem_ofFn, List.length_take, List.length_ofFn]
      apply BitVec.eq_of_getElem_eq
      intro j hj
      rw [BitVec.getElem_extractLsb', slot_getLsbD]
      simp only [show 28 - min 28 32 = 0 from rfl, List.getElem_cons_zero]
      rw [BitVec.getElem_extractLsb']
      interval_cases j <;>
        simp [foldHalf, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_ushiftRight]
    · rw [List.getElem_append_right (by simp [digestBytes])]
      simp only [List.getElem_take, digestBytes, List.getElem_ofFn, List.length_take, List.length_ofFn]
      apply BitVec.eq_of_getElem_eq
      intro j hj
      rw [BitVec.getElem_extractLsb', slot_getLsbD]
      simp only [show 29 - min 28 32 = 1 from rfl, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [BitVec.getElem_extractLsb']
      interval_cases j <;>
        simp [foldHalf, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_ushiftRight, top0, top1, top0e, top1e, spare0, spare1, Nat.add_assoc]

/-- The writer's block is GQ's `packEight` of the eight nodes, when bits `238..255` of nodes `0..6` are zero. -/
theorem fold_pack8 (s : Nat → BitVec 256) (high : ∀ k < 7, (s k).extractLsb' 238 18 = 0) :
    foldPack8 s = Quartet.packEight ((List.range 8).map s) := by
  have last : ((List.range 8).map s).getD 7 0 = s 7 := by simp
  have node : ∀ k < 8, ((List.range 8).map s).getD k 0 = s k := by
    intro k hk
    simp [hk]
  unfold foldPack8 Quartet.packEight
  simp only [last]
  have each : ∀ k ∈ List.range 7,
      foldSlot (s k) (s 7) k = Quartet.packedSlot (((List.range 8).map s).getD k 0) ((s 7).extractLsb' (224 + 2*k) 2) := by
    intro k member
    have small := List.mem_range.1 member
    rw [node k (by omega)]
    exact fold_slot (s k) (s 7) k small (high k small)
  rw [List.flatMap_congr each]

/-- A trailing partial-group node is a plain 30-byte copy. -/
theorem partial_slot (x : BitVec 256) (high : x.extractLsb' 238 18 = 0) :
    (digestBytes x).take 30 = Quartet.packedSlot x 0 := by
  unfold Quartet.packedSlot
  rw [slot_bytes]
  apply congrArg (fun v : BitVec 256 => (digestBytes v).take 30)
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem, slot_getLsbD]
  by_cases low : j < 238
  · simp [low]
  · have bit := congrArg (fun v : BitVec 18 => v.getLsbD (j - 238)) high
    simp only [BitVec.getLsbD_extractLsb', show j - 238 < 18 by omega, show 238 + (j - 238) = j by omega,
      decide_true, Bool.true_and, BitVec.getLsbD_zero] at bit
    by_cases mid : j < 240 <;> simp [low, mid, bit]

/-- The writer's halfword step: `lhu x28; slli x29,x31,14; or x28,x28,x29; sh x28` with
`x31 = zeroExtend x >>> 2k` stores `h ||| ((x >>> 2k) <<< 14)`. -/
theorem fold_half_bytes (h x : BitVec 16) (k : Nat) :
    ((h.zeroExtend 64 ||| ((x.zeroExtend 64 >>> (2*k)) <<< 14)).truncate 16) =
      h ||| ((x >>> (2*k)) <<< 14) := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  by_cases shifted : j < 14
  · simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, shifted]
  · by_cases wide : 2 * k + (j - 14) < 64
    · simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, shifted, wide]
    · have beyond : x.getLsbD (2 * k + (j - 14)) = false := BitVec.getLsbD_of_ge x _ (by omega)
      simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight, shifted, wide, beyond]

end TwoPermutationPrototype.GroupedOpening
