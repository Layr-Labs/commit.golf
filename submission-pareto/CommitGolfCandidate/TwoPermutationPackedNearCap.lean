import CommitGolfCandidate.TwoPermutationPackedNearHonest
import CommitGolfCandidate.QuartetConcrete
import Mathlib.Tactic.IntervalCases

/-! # One-byte search: the near-honest V1 input

The one-byte checker reads a truncated honest proof as the honest V1 input whose last frontier digest has bits
230..237 cleared (`nearCheckInput`): the records are the honest ones, and the cap is `packNodes` of the honest
frontier digests with the last one cleared. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)

/-- Bits 230..237 cleared. -/
def clearTop (v : BitVec 256) : BitVec 256 := (v.extractLsb' 238 18 ++ (0 : BitVec 8)) ++ v.extractLsb' 0 230

/-- The list with its last element's bits 230..237 cleared. -/
def clearLast (nodes : List (BitVec 256)) : List (BitVec 256) :=
  nodes.set (nodes.length-1) (clearTop (nodes.getD (nodes.length-1) 0))

/-- The honest frontier digests of a position set. -/
def honestNodes (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    List (BitVec 256) :=
  (capFrontierNodes (Opening.groupsBefore positions positions.card) 1 8).map (PackedHonest.honestHeap oracle message salts)

/-- What the one-byte checker decodes from a truncated honest proof. -/
def nearCheckInput (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) :
    CheckInput :=
  let h := honestCheckInput oracle message positions salts
  { h with proof := h.proof.take (534*positions.card) ++
      Quartet.packNodes (clearLast (honestNodes oracle message positions salts)) }

theorem clear_last_length (nodes : List (BitVec 256)) : (clearLast nodes).length = nodes.length := by
  simp [clearLast]

theorem clear_last_take (nodes : List (BitVec 256)) (long : 9 ≤ nodes.length) :
    (clearLast nodes).take 8 = nodes.take 8 := by
  unfold clearLast
  rw [List.take_set_of_le (by omega)]

theorem pack_nodes_length' (nodes : List (BitVec 256)) :
    (Quartet.packNodes nodes).length = 30*nodes.length-2*(nodes.length/8) := by
  have := Quartet.pack_nodes_length nodes
  omega

/-! ### Clearing the last digest masks four cap bytes -/

theorem flatmap_fixed {α : Type} (f : Nat → List α) (w : Nat) (hw : ∀ k, (f k).length = w) :
    ∀ n c, ((List.range n).flatMap f)[c]? = if c < w*n then (f (c/w))[c%w]? else none := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have len : ((List.range n).flatMap f).length = w*n := by
      rw [List.length_flatMap]; simp [hw]; ring
    by_cases a : c < w*n
    · rw [List.getElem?_append_left (by omega), ih, if_pos a, if_pos (by rw [Nat.mul_succ]; omega)]
    · rw [List.getElem?_append_right (by omega), len]
      by_cases b : c < w*(n+1)
      · rw [if_pos b]
        have wpos : 0 < w := by
          rcases Nat.eq_zero_or_pos w with h | h
          · subst h; simp at b
          · exact h
        have q : c/w = n := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.mul_comm]; rw [Nat.mul_succ] at b; omega)
        have r : c%w = c - w*n := by
          have := Nat.div_add_mod c w
          rw [q] at this
          omega
        rw [q, r]
      · rw [if_neg b, List.getElem?_eq_none]
        rw [hw]; rw [Nat.mul_succ] at b; omega

theorem slot_byte (x : BitVec 256) (carry : BitVec 2) (r : Nat) (hr : r < 30) :
    (Quartet.packedSlot x carry)[r]? = some (((0 : BitVec 16) ++ (carry ++ x.extractLsb' 0 238)).extractLsb' (8*r) 8) := by
  unfold Quartet.packedSlot proofDigestBytes digestBytes
  rw [if_pos rfl, List.getElem?_take_of_lt hr, List.getElem?_ofFn]
  simp [show r < 32 by omega]

theorem app_bit (c : BitVec 2) (y : BitVec 238) (t : Nat) :
    ((0 : BitVec 16) ++ (c ++ y)).getLsbD t = if t < 238 then y.getLsbD t else if t < 240 then c.getLsbD (t-238) else false := by
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases a : t < 238
  · simp [a, show t < 240 by omega]
  · by_cases b : t < 240
    · simp [a, b]
    · simp [a, b]

theorem slot_low (x : BitVec 256) (a b : BitVec 2) (r : Nat) (hr : r < 29) :
    (Quartet.packedSlot x a)[r]? = (Quartet.packedSlot x b)[r]? := by
  rw [slot_byte _ _ _ (by omega), slot_byte _ _ _ (by omega)]
  apply congrArg some
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', app_bit, app_bit, if_pos (by omega), if_pos (by omega)]

theorem slot_top (x : BitVec 256) (a : BitVec 2) :
    (Quartet.packedSlot x 0)[29]? = (Quartet.packedSlot x a)[29]?.map (fun v => v &&& 63#8) := by
  rw [slot_byte _ _ _ (by omega), slot_byte _ _ _ (by omega), Option.map_some]
  apply congrArg some
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', app_bit, app_bit]
  interval_cases i <;> simp

theorem clear_bit (v : BitVec 256) (t : Nat) (ht : t < 256) :
    (clearTop v).getLsbD t = (decide (t < 230 ∨ 238 ≤ t) && v.getLsbD t) := by
  unfold clearTop
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases a : t < 230
  · simp [a, show t < 256 by omega]
  · by_cases b : t < 238
    · simp [a, b, show t - 230 < 8 by omega]
    · simp [a, b, show ¬ t - 230 < 8 by omega, show t - 230 - 8 < 18 by omega, show 238 + (t - 230 - 8) = t by omega]
      omega

theorem clear_carry (v : BitVec 256) (k : Nat) :
    (clearTop v).extractLsb' (224+2*k) 2 = if k < 3 ∨ 7 ≤ k then v.extractLsb' (224+2*k) 2 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases big : 224+2*k+i < 256
  · split
    · rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', clear_bit _ _ big]
      simp [hi]; omega
    · rw [BitVec.getLsbD_extractLsb', clear_bit _ _ big]
      simp [hi]; omega
  · split
    · simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_of_ge _ _ (by omega), BitVec.getLsbD_of_ge _ _ (by omega)]
    · simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_of_ge _ _ (by omega)]
      simp

def masked (c : Nat) (v : BitVec 8) : BitVec 8 := if c = 119 ∨ c = 149 ∨ c = 179 ∨ c = 209 then v &&& 63#8 else v

theorem pack_eight_clear (l : List (BitVec 256)) (len : l.length = 8) :
    ∀ c, (Quartet.packEight (l.set 7 (clearTop (l.getD 7 0))))[c]? = (Quartet.packEight l)[c]?.map (masked c) := by
  intro c
  have get (k : Nat) : (l.set 7 (clearTop (l.getD 7 0))).getD k 0 = if k = 7 then clearTop (l.getD 7 0) else l.getD k 0 := by
    by_cases e : k = 7
    · subst e; simp [List.getD_eq_getElem?_getD, List.getElem?_set, len]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_set, e, Ne.symm e]
  unfold Quartet.packEight
  simp only [get, ↓reduceIte]
  have slots := flatmap_fixed (fun k => Quartet.packedSlot (if k = 7 then clearTop (l.getD 7 0) else l.getD k 0)
    ((clearTop (l.getD 7 0)).extractLsb' (224+2*k) 2)) 30 (fun k => Quartet.packed_slot_length _ _) 7
  have slots0 := flatmap_fixed (fun k => Quartet.packedSlot (l.getD k 0) ((l.getD 7 0).extractLsb' (224+2*k) 2)) 30
    (fun k => Quartet.packed_slot_length _ _) 7
  have len7 : ∀ (f : Nat → List (BitVec 8)), (∀ k, (f k).length = 30) → ((List.range 7).flatMap f).length = 210 := by
    intro f hf; rw [List.length_flatMap]; simp [hf]
  by_cases low : c < 210
  · rw [List.getElem?_append_left (by rw [len7 _ (fun k => Quartet.packed_slot_length _ _)]; exact low),
      List.getElem?_append_left (by rw [len7 _ (fun k => Quartet.packed_slot_length _ _)]; exact low)]
    have k7 : c/30 < 7 := by omega
    have c210 : c < 30*7 := by omega
    have n7 : ¬ c/30 = 7 := by omega
    rw [slots, slots0]
    simp only [c210, n7, ↓reduceIte]
    rw [clear_carry]
    by_cases r29 : c%30 = 29
    · rw [r29]
      by_cases early : c/30 < 3
      · rw [if_pos (Or.inl early)]
        rw [slot_byte _ _ _ (by omega), Option.map_some]
        unfold masked
        simp only [show ¬ (c = 119 ∨ c = 149 ∨ c = 179 ∨ c = 209) by omega, ↓reduceIte]
      · rw [if_neg (by omega), slot_top _ ((l.getD 7 0).extractLsb' (224+2*(c/30)) 2)]
        unfold masked
        simp only [show (c = 119 ∨ c = 149 ∨ c = 179 ∨ c = 209) by omega, ↓reduceIte]
    · rw [slot_low _ _ ((l.getD 7 0).extractLsb' (224+2*(c/30)) 2) _ (by omega), slot_byte _ _ _ (by omega),
        Option.map_some]
      unfold masked
      simp only [show ¬ (c = 119 ∨ c = 149 ∨ c = 179 ∨ c = 209) by omega, ↓reduceIte]
  · rw [List.getElem?_append_right (by rw [len7 _ (fun k => Quartet.packed_slot_length _ _)]; omega),
      List.getElem?_append_right (by rw [len7 _ (fun k => Quartet.packed_slot_length _ _)]; omega),
      len7 _ (fun k => Quartet.packed_slot_length _ _), len7 _ (fun k => Quartet.packed_slot_length _ _)]
    have mid : masked c = id := by funext v; unfold masked; rw [if_neg (by omega)]; rfl
    rw [mid, Option.map_id]
    simp only [id]
    by_cases in28 : c-210 < 28
    · unfold digestBytes
      rw [List.getElem?_take_of_lt in28, List.getElem?_take_of_lt in28, List.getElem?_ofFn, List.getElem?_ofFn]
      simp only [show c-210 < 32 by omega, dif_pos]
      apply congrArg some
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', clear_bit _ _ (by omega)]
      simp [hi]; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem pack_split (l : List (BitVec 256)) (h : 8 ≤ l.length) :
    Quartet.packNodes l = Quartet.packEight (l.take 8) ++ Quartet.packNodes (l.drop 8) := by
  rw [Quartet.packNodes, if_pos h]

theorem pack_eight_only (l : List (BitVec 256)) (len : l.length = 8) : Quartet.packNodes l = Quartet.packEight l := by
  have nil : Quartet.packNodes ([] : List (BitVec 256)) = [] := by rw [Quartet.packNodes]; simp
  rw [pack_split l (by omega), List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), nil,
    List.append_nil]

theorem pack_nodes_clear : ∀ m (l : List (BitVec 256)), l.length = 8*(m+1) →
    ∀ c, (Quartet.packNodes (clearLast l))[c]? = (Quartet.packNodes l)[c]?.map (masked (c-238*m)) := by
  intro m
  induction m with
  | zero =>
    intro l len c
    have cl : clearLast l = l.set 7 (clearTop (l.getD 7 0)) := by unfold clearLast; rw [len]
    rw [cl, pack_eight_only _ (by simp; omega), pack_eight_only l (by omega)]
    simpa using pack_eight_clear l (by omega) c
  | succ m ih =>
    intro l len c
    have long : 8 ≤ (clearLast l).length := by unfold clearLast; simp; omega
    have take' : (clearLast l).take 8 = l.take 8 := by
      unfold clearLast; exact List.take_set_of_le (by omega)
    have drop' : (clearLast l).drop 8 = clearLast (l.drop 8) := by
      unfold clearLast
      rw [List.drop_set, if_neg (by omega), List.length_drop]
      have idx : l.length - 1 - 8 = l.length - 8 - 1 := by omega
      have val : l.getD (l.length-1) 0 = (l.drop 8).getD (l.length-8-1) 0 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
          show 8 + (l.length-8-1) = l.length-1 by omega]
      rw [idx, val]
    rw [pack_split (clearLast l) long, pack_split l (by omega), take', drop']
    by_cases first : c < 238
    · rw [List.getElem?_append_left (by rw [Quartet.pack_eight_length]; exact first),
        List.getElem?_append_left (by rw [Quartet.pack_eight_length]; exact first)]
      have : masked (c-238*(m+1)) = id := by
        funext v; unfold masked; rw [if_neg (by omega)]; rfl
      rw [this, Option.map_id]
      rfl
    · rw [List.getElem?_append_right (by rw [Quartet.pack_eight_length]; omega),
        List.getElem?_append_right (by rw [Quartet.pack_eight_length]; omega), Quartet.pack_eight_length,
        ih (l.drop 8) (by simp; omega) (c-238), show c-238-238*m = c-238*(m+1) by omega]

theorem pack_clear_128 (l : List (BitVec 256)) (len : l.length = 128) (c : Nat) :
    (Quartet.packNodes (clearLast l))[c]? = (Quartet.packNodes l)[c]?.map (fun v =>
      if c = 3689 ∨ c = 3719 ∨ c = 3749 ∨ c = 3779 then v &&& 63#8 else v) := by
  have e : masked (c-238*15) = fun v => if c = 3689 ∨ c = 3719 ∨ c = 3749 ∨ c = 3779 then v &&& 63#8 else v := by
    funext v
    unfold masked
    by_cases h : c = 3689 ∨ c = 3719 ∨ c = 3749 ∨ c = 3779
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  rw [pack_nodes_clear 15 l (by omega) c, e]


theorem pack_nodes_head (a b : List (BitVec 256)) (la : 9 ≤ a.length) (lb : 9 ≤ b.length) (same : a.take 8 = b.take 8)
    (j : Nat) (small : j < 238) : (Quartet.packNodes a)[j]? = (Quartet.packNodes b)[j]? := by
  rw [pack_split a (by omega), pack_split b (by omega), same,
    List.getElem?_append_left (by rw [Quartet.pack_eight_length]; exact small),
    List.getElem?_append_left (by rw [Quartet.pack_eight_length]; exact small)]

/-- With at least nine frontier digests the near-honest input agrees with the honest one on its records. -/
theorem near_honest_input (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (many : 9 ≤ (honestNodes oracle message positions salts).length) :
    NearHonest (nearCheckInput oracle message positions salts) (honestCheckInput oracle message positions salts) := by
  let h := honestCheckInput oracle message positions salts
  have parts := PackedHonest.honest_proof_parts oracle message positions salts
  have nonempty : (Opening.groupsBefore positions positions.card).isEmpty = false := by
    apply Bool.eq_false_of_not_eq_true
    intro e
    rw [List.isEmpty_iff] at e
    unfold honestNodes at many
    rw [e] at many
    simp [capFrontierNodes, capIsMarked] at many
  have frontier : Quartet.frontierProof238 (PackedHonest.honestHeap oracle message salts)
      (Opening.groupsBefore positions positions.card) = Quartet.packNodes (honestNodes oracle message positions salts) := by
    unfold Quartet.frontierProof238 honestNodes
    rw [if_neg (by rw [nonempty]; decide)]
  rw [frontier] at parts
  obtain ⟨R, partsR, width⟩ : ∃ R : List Byte, h.proof = R ++ Quartet.packNodes (honestNodes oracle message positions salts) ∧
      R.length = 534*positions.card :=
    ⟨_, parts, by
      rw [PackedHonest.fixed_flatmap_length _ 534 (fun _ => Quartet.opening_record_length _ _ _ _) _,
        PackedHonest.honest_order_length]⟩
  refine ⟨_, rfl, ?_, ?_⟩
  · change (h.proof.take (534*positions.card) ++ _).length = h.proof.length
    rw [List.length_append, List.length_take, partsR, List.length_append, width, pack_nodes_length',
      pack_nodes_length', clear_last_length]
    omega
  · intro q small
    have s' : q < 534*positions.card+8 := small
    change (h.proof.take (534*positions.card) ++ _)[q]? = h.proof[q]?
    have tl : (h.proof.take (534*positions.card)).length = 534*positions.card := by
      rw [List.length_take, partsR, List.length_append, width]; omega
    by_cases rec : q < 534*positions.card
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt rec]
    · rw [List.getElem?_append_right (by omega), tl, partsR, List.getElem?_append_right (by omega), width]
      exact pack_nodes_head _ _ (by rw [clear_last_length]; exact many) many
        (clear_last_take _ many) _ (by omega)

end TwoPermutationPrototype.Packed.Checker
