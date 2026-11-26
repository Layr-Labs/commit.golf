import CommitGolfCandidate.PentaWrapMemory

/-! The wrapper's expansion maps an honest cap proof to the donor's honest penta proof: record
prefixes are the first 912 bytes of `pentaRecord`, and each of the record's top blocks (levels
7-10) is the table slot of the sibling node, `pentaNeighbour index k j`. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

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

theorem sorted_value_indices' (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val = positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

theorem penta_record_split (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    pentaRecord penta leaves index salt = capRecord penta leaves index salt ++
      [7, 8, 9, 10].flatMap (fun k => (List.range 4).flatMap fun j =>
        digestBytes (pentaNode penta leaves k (pentaNeighbour index k j))) := by
  unfold pentaRecord capRecord PENTA_LEVELS
  rw [List.append_assoc, ← List.flatMap_append]
  rfl

theorem digest_length (d : BitVec 256) : (digestBytes d).length = 32 := by simp [digestBytes]

theorem block_length (penta : PentaFunction) (leaves : DigestTape) (index : Index) (k : Nat) :
    ((List.range 4).flatMap fun j => digestBytes (pentaNode penta leaves k (pentaNeighbour index k j))).length = 128 := by
  rw [flat_map_length _ 32 _ (fun _ _ => digest_length _)]; simp

/-- Byte `128 lvl + 32 j + t` of the top blocks of a record. -/
theorem top_byte (penta : PentaFunction) (leaves : DigestTape) (index : Index) (lvl j t : Nat)
    (hl : lvl < 4) (hj : j < 4) (ht : t < 32) :
    ([7, 8, 9, 10].flatMap (fun k => (List.range 4).flatMap fun j =>
        digestBytes (pentaNode penta leaves k (pentaNeighbour index k j))))[128*lvl + (32*j + t)]? =
      (digestBytes (pentaNode penta leaves (7+lvl) (pentaNeighbour index (7+lvl) j)))[t]? := by
  rw [flat_map_chunk _ 128 _ (fun k _ => block_length penta leaves index k) lvl _ (by omega)]
  have e : [7, 8, 9, 10][lvl]? = some (7+lvl) := by interval_cases lvl <;> rfl
  rw [e, Option.bind_some, flat_map_chunk _ 32 _ (fun _ _ => digest_length _) j t ht,
    List.getElem?_range (by omega), Option.bind_some]

/-- Byte `32 (5 capFirst lvl + n) + t` of the table: byte `t` of level-`(7+lvl)` node `n`. -/
theorem table_byte (penta : PentaFunction) (leaves : DigestTape) (lvl n t : Nat) (hl : lvl < 4)
    (hn : n < capSlots (7+lvl)) (ht : t < 32) :
    (capTable penta leaves)[32*(5*capFirst lvl + n) + t]? = (digestBytes (pentaNode penta leaves (7+lvl) n))[t]? := by
  obtain ⟨s7, s8, s9, s10⟩ := cap_slots_values
  have level (k : Nat) : (capLevel penta leaves k).length = 32*capSlots k := cap_level_length penta leaves k
  have slot (k : Nat) (m : Nat) (hm : m < capSlots k) :
      (capLevel penta leaves k)[32*m + t]? = (digestBytes (pentaNode penta leaves k m))[t]? := by
    unfold capLevel
    rw [flat_map_chunk _ 32 _ (fun _ _ => digest_length _) m t ht, List.getElem?_range hm, Option.bind_some]
  unfold capTable
  interval_cases lvl <;> simp only [Nat.reduceAdd] at hn ⊢
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, capFirst]
    rw [List.getElem?_append_left (by rw [level]; omega)]
    simpa using slot 7 n hn
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, capFirst]
    rw [List.getElem?_append_right (by rw [level, s7]; omega), level, s7,
      List.getElem?_append_left (by rw [level]; omega), show 32*(5*43+n)+t-32*215 = 32*n+t by omega]
    exact slot 8 n hn
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, capFirst]
    rw [List.getElem?_append_right (by rw [level, s7]; omega), level, s7,
      List.getElem?_append_right (by rw [level, s8]; omega), level, s8,
      List.getElem?_append_left (by rw [level]; omega), show 32*(5*52+n)+t-32*215-32*45 = 32*n+t by omega]
    exact slot 9 n hn
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, capFirst]
    rw [List.getElem?_append_right (by rw [level, s7]; omega), level, s7,
      List.getElem?_append_right (by rw [level, s8]; omega), level, s8,
      List.getElem?_append_right (by rw [level, s9]; omega), level, s9,
      show 32*(5*54+n)+t-32*215-32*45-32*10 = 32*n+t by omega]
    exact slot 10 n hn


theorem group_bound (i lvl : Nat) (hi : i < 16777216) (hl : lvl < 4) :
    capQuot i lvl / 5 < pentaCount (8+lvl) := by
  have counts : pentaCount 8 = 43 ∧ pentaCount 9 = 9 ∧ pentaCount 10 = 2 ∧ pentaCount 11 = 1 := by decide
  unfold capQuot
  rw [Nat.div_div_eq_div_mul, ← pow_succ]
  interval_cases lvl <;> norm_num [counts] <;> omega

theorem get_d_some {β : Type} (l : List β) (i : Nat) (d : β) (h : i < l.length) :
    some ((l[i]?).getD d) = l[i]? := by
  rw [List.getElem?_eq_getElem h]; rfl

private theorem omitted_tail (L n T : Nat) (level : L < 4) (slot : n < capSlots (7+L))
    (byte : T < 32) (omitted : 8704 ≤ 32*(5*capFirst L + n) + T) : L = 3 ∧ 2 ≤ n := by
  obtain ⟨s7, s8, s9, s10⟩ := cap_slots_values
  have top : L = 3 := by
    by_contra lower
    interval_cases L <;>
      simp only [capFirst, Nat.reduceAdd, s7, s8, s9, s10] at slot omitted <;> omega
  refine ⟨top, ?_⟩
  rw [top] at omitted
  change 8704 ≤ 32*(270 + n) + T at omitted
  omega

/-- The wrapper's expansion of the honest cap proof is the honest penta proof. -/
theorem expand_cap_proof (penta : PentaFunction) (positions : Positions) (salts : OpenedSalts positions)
    (leaves : DigestTape) :
    expandProof positions (capTranscriptBuilderOld penta positions salts leaves).2 =
      (pentaTranscriptBuilder penta positions salts leaves).2 := by
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  have ordLen : ordered.length = positions.card := by simp [ordered]
  have recLen : ∀ x ∈ ordered, (capRecord penta leaves x.val (salts x)).length = 912 :=
    fun x _ => cap_record_length _ _ _ _
  have pentaLen : ∀ x ∈ ordered, (pentaRecord penta leaves x.val (salts x)).length = 1424 :=
    fun x _ => penta_record_length _ _ _ _
  have records : (ordered.flatMap fun x => capRecord penta leaves x.val (salts x)).length = 912*positions.card := by
    rw [flat_map_length _ 912 _ recLen, ordLen]
  have pentaProof : (pentaTranscriptBuilder penta positions salts leaves).2 =
      ordered.flatMap fun x => pentaRecord penta leaves x.val (salts x) := rfl
  have capProof : (capTranscriptBuilderOld penta positions salts leaves).2 =
      (ordered.flatMap fun x => capRecord penta leaves x.val (salts x)) ++
        (if positions.card = 0 then [] else (capTable penta leaves).take 8704) := rfl
  have sorted (r : Nat) (hr : r < positions.card) :
      sortedIndex positions r = (ordered[r]'(by omega)).val.val := by
    unfold sortedIndex
    rw [← sorted_value_indices' positions, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [Finset.length_sort, Finset.card_attach]; exact hr)]
    rfl
  rw [pentaProof]
  apply List.ext_getElem?
  intro b
  by_cases inside : b < 1424*positions.card
  · rw [show expandProof positions (capTranscriptBuilderOld penta positions salts leaves).2 =
        (List.range (1424*positions.card)).map (expandByte positions (capTranscriptBuilderOld penta positions salts leaves).2)
        from rfl, List.getElem?_map, List.getElem?_range inside, Option.map_some]
    have hb : b = 1424*(b/1424) + b % 1424 := by omega
    have hr : b/1424 < positions.card := by omega
    rw [hb, flat_map_chunk _ 1424 _ pentaLen _ _ (Nat.mod_lt _ (by decide)),
      List.getElem?_eq_getElem (by omega), Option.bind_some, ← hb]
    generalize hx : ordered[b/1424]'(by omega) = x
    have nonempty : positions.card ≠ 0 := by omega
    unfold expandByte
    dsimp only
    rw [penta_record_split]
    by_cases low : b % 1424 < 912
    · rw [if_pos low, capProof, List.getElem?_append_left (by rw [records]; omega),
        flat_map_chunk _ 912 _ recLen _ _ low, List.getElem?_eq_getElem (by omega), hx, Option.bind_some,
        List.getElem?_append_left (by rw [cap_record_length]; exact low)]
      exact get_d_some _ _ _ (by rw [cap_record_length]; exact low)
    · rw [if_neg low]
      have he' : b % 1424 < 1424 := Nat.mod_lt _ (by decide)
      generalize he : b % 1424 = e at low he' ⊢
      have index := (sorted (b/1424) hr).trans (by rw [hx])
      rw [index]
      -- the donor side: the sibling digest of the record's top block
      rw [List.getElem?_append_right (by rw [cap_record_length]; omega), cap_record_length]
      have eDecomp : e - 912 = 128*((e-912)/128) + (32*(((e-912)%128)/32) + (e-912)%32) := by omega
      have rhs : ([7, 8, 9, 10].flatMap (fun k => (List.range 4).flatMap fun j =>
          digestBytes (pentaNode penta leaves k (pentaNeighbour x.val k j))))[e - 912]? =
          (digestBytes (pentaNode penta leaves (7+(e-912)/128)
            (pentaNeighbour x.val (7+(e-912)/128) (((e-912)%128)/32))))[(e-912)%32]? := by
        conv_lhs => rw [eDecomp]
        exact top_byte penta leaves x.val _ _ _ (by omega) (by omega) (by omega)
      rw [rhs]
      have hl : (e-912)/128 < 4 := by omega
      have hj : ((e-912)%128)/32 < 4 := by omega
      have ht : (e-912)%32 < 32 := by omega
      generalize hL : (e-912)/128 = L at hl ⊢
      generalize hJ : ((e-912)%128)/32 = J at hj ⊢
      generalize hT : (e-912)%32 = T at ht ⊢
      have small : x.val.val < 16777216 := x.val.isLt
      have gb := group_bound x.val.val L small hl
      have neighbour : pentaNeighbour x.val (7+L) J = 5*(capQuot x.val.val L / 5) + (capQuot x.val.val L % 5 + J + 1) % 5 := by
        unfold pentaNeighbour pentaRot capQuot
        rw [show 7 + L + 1 = (7+L)+1 by omega, pow_succ, ← Nat.div_div_eq_div_mul]
      rw [neighbour]
      generalize hq : capQuot x.val.val L = q at gb ⊢
      have slot : (q%5 + J + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
      have count : 5*(q/5) + (q%5 + J + 1) % 5 < capSlots (7+L) := by
        unfold capSlots; rw [show 7 + L + 1 = 8 + L by omega]; omega
      let n := 5*(q/5) + (q%5 + J + 1) % 5
      let offset := 32*(5*capFirst L + n) + T
      have table := table_byte penta leaves L n T hl count ht
      have tableLen : (capTable penta leaves).length = 8800 := cap_table_length penta leaves
      have bound : offset < 8800 := by
        dsimp only [offset]
        obtain ⟨s7, s8, s9, s10⟩ := cap_slots_values
        change n < capSlots (7+L) at count
        interval_cases L <;> simp only [capFirst, Nat.reduceAdd, s7, s8, s9, s10] at count ⊢ <;> omega
      rw [capProof, if_neg nonempty,
        show 912*positions.card + 160*(capFirst L + q/5) + 32*((q%5 + J + 1) % 5) + T =
          (ordered.flatMap fun x => capRecord penta leaves x.val (salts x)).length + offset by
            rw [records]; dsimp [offset, n]; omega,
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      by_cases sent : offset < 8704
      · rw [List.getElem?_take_of_lt sent, ← table]
        exact get_d_some _ _ _ (by rw [tableLen]; exact bound)
      · have tail : L = 3 ∧ 2 ≤ n := omitted_tail L n T hl count ht (by omega)
        have zero : pentaNode penta leaves (7+L) n = 0 := by
          rw [tail.1]
          have outside : ¬ n < pentaCount 10 := by
            have : pentaCount 10 = 2 := by decide
            omega
          change (if n < pentaCount 10 then _ else _) = _
          rw [if_neg outside]
        rw [List.getElem?_eq_none (by simp; omega), Option.getD_none]
        change some (0 : Byte) = (digestBytes (pentaNode penta leaves (7+L) n))[T]?
        rw [zero]
        simp only [digestBytes, List.getElem?_ofFn, dif_pos ht]
        change some (0#8) = some ((0#256).extractLsb' (8*T) 8)
        rw [BitVec.extractLsb'_zero]
  · rw [List.getElem?_eq_none (by simp [expandProof]; omega),
      List.getElem?_eq_none (by rw [flat_map_length _ 1424 _ pentaLen, ordLen]; omega)]

end TwoPermutationPrototype.PentaWrap
