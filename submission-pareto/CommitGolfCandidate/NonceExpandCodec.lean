import CommitGolfCandidate.S6Codec

/-! Byte layout of `s6ExpandRecords`: its length and the source of every expanded byte.

For a delivered proof of `534 * indices.length + 30 * footer` bytes, the expansion has one
576-byte record per index, then `footer` 32-byte nodes. Each byte of the expansion is either a
delivered byte, a tag byte of the record's position, or zero. -/
namespace CommitGolfCandidate
open CommitGolf

/-! ### Nodes -/

theorem s6_expand_nodes_length (nodes : Nat) (bytes : List Byte) (enough : 30 * nodes ≤ bytes.length) :
    (s6ExpandNodes nodes bytes).length = 32 * nodes := by
  induction nodes generalizing bytes with
  | zero => rfl
  | succ nodes ih =>
    rw [s6ExpandNodes, List.length_append, List.length_append, List.length_take,
      List.length_replicate, ih _ (by simp only [List.length_drop]; omega)]
    omega

theorem s6_expand_nodes_getElem? (nodes : Nat) (bytes : List Byte) (enough : 30 * nodes ≤ bytes.length)
    (j o : Nat) (hj : j < nodes) (ho : o < 32) :
    (s6ExpandNodes nodes bytes)[32 * j + o]? = if o < 30 then bytes[30 * j + o]? else some 0 := by
  induction nodes generalizing bytes j with
  | zero => omega
  | succ nodes ih =>
    have takeLength : (bytes.take 30).length = 30 := by
      simp only [List.length_take]
      omega
    have firstLength : (bytes.take 30 ++ List.replicate 2 (0 : Byte)).length = 32 := by
      rw [List.length_append, takeLength, List.length_replicate]
    rw [s6ExpandNodes]
    rcases j with _ | j
    · rw [List.getElem?_append_left (by omega)]
      simp only [Nat.mul_zero, Nat.zero_add]
      by_cases low : o < 30
      · rw [ite_eq_left low, List.getElem?_append_left (by omega), List.getElem?_take_of_lt low]
      · rw [ite_eq_right low, List.getElem?_append_right (by omega), takeLength, List.getElem?_replicate,
          ite_eq_left (by omega)]
    · have shifted : 32 * (j + 1) + o - 32 = 32 * j + o := by omega
      have source : 30 + (30 * j + o) = 30 * (j + 1) + o := by omega
      rw [List.getElem?_append_right (by omega), firstLength, shifted,
        ih _ (by simp only [List.length_drop]; omega) j (by omega), List.getElem?_drop, source]

/-! ### One record -/

theorem s6_tag_bytes_length (index : Index) : (s6TagBytes index).length = 8 := by
  simp only [s6TagBytes, List.length_map, List.length_range]

theorem s6_expand_record_assoc (index : Index) (packed : List Byte) :
    s6ExpandRecord index packed = packed.take 16 ++ (s6TagBytes index ++ (List.replicate 8 0 ++
      ((packed.drop 16).take 128 ++ s6ExpandNodes 13 (packed.drop 144)))) := by
  rw [s6ExpandRecord]
  simp only [List.append_assoc]

theorem s6_expand_record_length (index : Index) (packed : List Byte) (enough : 534 ≤ packed.length) :
    (s6ExpandRecord index packed).length = 576 := by
  rw [s6_expand_record_assoc]
  simp only [List.length_append, List.length_take, List.length_drop, List.length_replicate,
    s6_tag_bytes_length]
  rw [s6_expand_nodes_length 13 _ (by simp only [List.length_drop]; omega)]
  omega

theorem s6_expand_record_nonce (index : Index) (packed : List Byte) (enough : 534 ≤ packed.length)
    (m : Nat) (hm : m < 16) :
    (s6ExpandRecord index packed)[m]? = packed[m]? := by
  have hA : (packed.take 16).length = 16 := by simp only [List.length_take]; omega
  rw [s6_expand_record_assoc, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hm]

theorem s6_expand_record_tag (index : Index) (packed : List Byte) (enough : 534 ≤ packed.length)
    (m : Nat) (hm : m < 8) :
    (s6ExpandRecord index packed)[16 + m]? = some (BitVec.ofNat 8 (s6Tag index / 2 ^ (8 * m))) := by
  have hA : (packed.take 16).length = 16 := by simp only [List.length_take]; omega
  have hB : (s6TagBytes index).length = 8 := s6_tag_bytes_length index
  have shifted : 16 + m - 16 = m := by omega
  rw [s6_expand_record_assoc, List.getElem?_append_right (by omega), hA, shifted,
    List.getElem?_append_left (by omega), s6TagBytes, List.getElem?_map, List.getElem?_range hm]
  rfl

theorem s6_expand_record_zero (index : Index) (packed : List Byte) (enough : 534 ≤ packed.length)
    (m : Nat) (hm : m < 8) :
    (s6ExpandRecord index packed)[24 + m]? = some 0 := by
  have hA : (packed.take 16).length = 16 := by simp only [List.length_take]; omega
  have hB : (s6TagBytes index).length = 8 := s6_tag_bytes_length index
  have hC : (List.replicate 8 (0 : Byte)).length = 8 := List.length_replicate
  have first : 24 + m - 16 = 8 + m := by omega
  have second : 8 + m - 8 = m := by omega
  rw [s6_expand_record_assoc, List.getElem?_append_right (by omega), hA, first,
    List.getElem?_append_right (by omega), hB, second, List.getElem?_append_left (by omega),
    List.getElem?_replicate, ite_eq_left hm]

theorem s6_expand_record_middle (index : Index) (packed : List Byte) (enough : 534 ≤ packed.length)
    (m : Nat) (hm : m < 128) :
    (s6ExpandRecord index packed)[32 + m]? = packed[16 + m]? := by
  have hA : (packed.take 16).length = 16 := by simp only [List.length_take]; omega
  have hB : (s6TagBytes index).length = 8 := s6_tag_bytes_length index
  have hC : (List.replicate 8 (0 : Byte)).length = 8 := List.length_replicate
  have hD : ((packed.drop 16).take 128).length = 128 := by
    simp only [List.length_take, List.length_drop]; omega
  have first : 32 + m - 16 = 16 + m := by omega
  have second : 16 + m - 8 = 8 + m := by omega
  have third : 8 + m - 8 = m := by omega
  rw [s6_expand_record_assoc, List.getElem?_append_right (by omega), hA, first,
    List.getElem?_append_right (by omega), hB, second, List.getElem?_append_right (by omega), hC,
    third, List.getElem?_append_left (by omega), List.getElem?_take_of_lt hm, List.getElem?_drop]

theorem s6_expand_record_sibling (index : Index) (packed : List Byte) (enough : 534 ≤ packed.length)
    (s o : Nat) (hs : s < 13) (ho : o < 32) :
    (s6ExpandRecord index packed)[160 + 32 * s + o]? =
      if o < 30 then packed[144 + 30 * s + o]? else some 0 := by
  have hA : (packed.take 16).length = 16 := by simp only [List.length_take]; omega
  have hB : (s6TagBytes index).length = 8 := s6_tag_bytes_length index
  have hC : (List.replicate 8 (0 : Byte)).length = 8 := List.length_replicate
  have hD : ((packed.drop 16).take 128).length = 128 := by
    simp only [List.length_take, List.length_drop]; omega
  have first : 160 + 32 * s + o - 16 = 144 + 32 * s + o := by omega
  have second : 144 + 32 * s + o - 8 = 136 + 32 * s + o := by omega
  have third : 136 + 32 * s + o - 8 = 128 + 32 * s + o := by omega
  have fourth : 128 + 32 * s + o - 128 = 32 * s + o := by omega
  have source : 144 + (30 * s + o) = 144 + 30 * s + o := by omega
  rw [s6_expand_record_assoc, List.getElem?_append_right (by omega), hA, first,
    List.getElem?_append_right (by omega), hB, second, List.getElem?_append_right (by omega), hC,
    third, List.getElem?_append_right (by omega), hD, fourth,
    s6_expand_nodes_getElem? 13 _ (by simp only [List.length_drop]; omega) s o hs ho,
    List.getElem?_drop, source]

/-! ### All records and the footer -/

theorem nonce_expand_records_length (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) :
    (s6ExpandRecords indices proof).length = 576 * indices.length + 32 * footer := by
  induction indices generalizing proof with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at size ⊢
    rw [s6ExpandRecords, show proof.length / 30 = footer by omega,
      s6_expand_nodes_length _ _ (by omega)]
  | cons index rest ih =>
    simp only [List.length_cons] at size ⊢
    rw [s6ExpandRecords, List.length_append, s6_expand_record_length _ _ (by omega),
      ih _ (by simp only [List.length_drop]; omega)]
    omega

theorem s6_expand_records_record (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (r : Nat) (hr : r < indices.length)
    (k : Nat) (hk : k < 576) :
    (s6ExpandRecords indices proof)[576 * r + k]? =
      (s6ExpandRecord (indices[r]'hr) (proof.drop (534 * r)))[k]? := by
  induction indices generalizing proof r with
  | nil => simp at hr
  | cons index rest ih =>
    have enough : 534 ≤ proof.length := by simp only [List.length_cons] at size; omega
    have restSize : (proof.drop 534).length = 534 * rest.length + 30 * footer := by
      simp only [List.length_drop, List.length_cons] at size ⊢
      omega
    have recordLength := s6_expand_record_length index proof enough
    rw [s6ExpandRecords]
    rcases r with _ | r
    · rw [List.getElem?_append_left (by omega)]
      simp only [Nat.mul_zero, Nat.zero_add, List.drop_zero, List.getElem_cons_zero]
    · have restBound : r < rest.length := by
        simp only [List.length_cons] at hr
        omega
      have shifted : 576 * (r + 1) + k - 576 = 576 * r + k := by omega
      have source : 534 + 534 * r = 534 * (r + 1) := by omega
      rw [List.getElem?_append_right (by omega), recordLength, shifted,
        ih (proof.drop 534) restSize r restBound, List.drop_drop, source]
      simp only [List.getElem_cons_succ]

theorem s6_expand_records_footer (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (k : Nat) :
    (s6ExpandRecords indices proof)[576 * indices.length + k]? =
      (s6ExpandNodes footer (proof.drop (534 * indices.length)))[k]? := by
  induction indices generalizing proof with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.drop_zero] at size ⊢
    rw [s6ExpandRecords, show proof.length / 30 = footer by omega]
  | cons index rest ih =>
    simp only [List.length_cons] at size ⊢
    have enough : 534 ≤ proof.length := by omega
    have restSize : (proof.drop 534).length = 534 * rest.length + 30 * footer := by
      simp only [List.length_drop]
      omega
    have recordLength := s6_expand_record_length index proof enough
    have shifted : 576 * (rest.length + 1) + k - 576 = 576 * rest.length + k := by omega
    have source : 534 + 534 * rest.length = 534 * (rest.length + 1) := by omega
    rw [s6ExpandRecords, List.getElem?_append_right (by omega), recordLength, shifted,
      ih (proof.drop 534) restSize, List.drop_drop, source]

theorem s6_expand_records_enough (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (r : Nat) (hr : r < indices.length) :
    534 ≤ (proof.drop (534 * r)).length := by
  simp only [List.length_drop]
  omega

/-! ### Byte sources -/

theorem nonce_expand_footer_byte (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (j o : Nat) (hj : j < footer)
    (ho : o < 32) :
    (s6ExpandRecords indices proof)[576 * indices.length + 32 * j + o]? =
      if o < 30 then proof[534 * indices.length + 30 * j + o]? else some 0 := by
  have offset : 576 * indices.length + 32 * j + o = 576 * indices.length + (32 * j + o) := by omega
  have source : 534 * indices.length + (30 * j + o) = 534 * indices.length + 30 * j + o := by omega
  rw [offset, s6_expand_records_footer indices proof footer size,
    s6_expand_nodes_getElem? footer _ (by simp only [List.length_drop]; omega) j o hj ho,
    List.getElem?_drop, source]

theorem nonce_expand_sibling_byte (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (r : Nat) (hr : r < indices.length)
    (s o : Nat) (hs : s < 13) (ho : o < 32) :
    (s6ExpandRecords indices proof)[576 * r + 160 + 32 * s + o]? =
      if o < 30 then proof[534 * r + 144 + 30 * s + o]? else some 0 := by
  have offset : 576 * r + 160 + 32 * s + o = 576 * r + (160 + 32 * s + o) := by omega
  have source : 534 * r + (144 + 30 * s + o) = 534 * r + 144 + 30 * s + o := by omega
  rw [offset, s6_expand_records_record indices proof footer size r hr _ (by omega),
    s6_expand_record_sibling _ _ (s6_expand_records_enough indices proof footer size r hr) s o hs ho,
    List.getElem?_drop, source]

theorem nonce_expand_middle_byte (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (r : Nat) (hr : r < indices.length)
    (m : Nat) (hm : m < 128) :
    (s6ExpandRecords indices proof)[576 * r + 32 + m]? = proof[534 * r + 16 + m]? := by
  have offset : 576 * r + 32 + m = 576 * r + (32 + m) := by omega
  have source : 534 * r + (16 + m) = 534 * r + 16 + m := by omega
  rw [offset, s6_expand_records_record indices proof footer size r hr _ (by omega),
    s6_expand_record_middle _ _ (s6_expand_records_enough indices proof footer size r hr) m hm,
    List.getElem?_drop, source]

theorem nonce_expand_zero_byte (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (r : Nat) (hr : r < indices.length)
    (m : Nat) (hm : m < 8) :
    (s6ExpandRecords indices proof)[576 * r + 24 + m]? = some 0 := by
  have offset : 576 * r + 24 + m = 576 * r + (24 + m) := by omega
  rw [offset, s6_expand_records_record indices proof footer size r hr _ (by omega),
    s6_expand_record_zero _ _ (s6_expand_records_enough indices proof footer size r hr) m hm]

theorem nonce_expand_tag_byte (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (r : Nat) (hr : r < indices.length)
    (m : Nat) (hm : m < 8) :
    (s6ExpandRecords indices proof)[576 * r + 16 + m]? =
      some (BitVec.ofNat 8 (s6Tag (indices[r]'hr) / 2 ^ (8 * m))) := by
  have offset : 576 * r + 16 + m = 576 * r + (16 + m) := by omega
  rw [offset, s6_expand_records_record indices proof footer size r hr _ (by omega),
    s6_expand_record_tag _ _ (s6_expand_records_enough indices proof footer size r hr) m hm]

theorem nonce_expand_nonce_byte (indices : List Index) (proof : List Byte) (footer : Nat)
    (size : proof.length = 534 * indices.length + 30 * footer) (r : Nat) (hr : r < indices.length)
    (m : Nat) (hm : m < 16) :
    (s6ExpandRecords indices proof)[576 * r + m]? = proof[534 * r + m]? := by
  rw [s6_expand_records_record indices proof footer size r hr m (by omega),
    s6_expand_record_nonce _ _ (s6_expand_records_enough indices proof footer size r hr) m hm,
    List.getElem?_drop]

end CommitGolfCandidate
