import CommitGolfCandidate.S6Codec
import CommitGolfCandidate.CapHonestLowerBytes
import CommitGolfCandidate.CapOpenLoadedBytes

/-! Honest internal proofs are canonical for the proof codec: every record's salt field
carries its tag and eight zero bytes. Internal nodes keep all 256 bits, so the codec needs no
fact about them. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-! ### Bytes of a digest -/

private theorem digest_bytes_window (digest : Digest) (start count : Nat) (inside : start+count ≤ 32) :
    ((digestBytes digest).drop start).take count =
      List.ofFn fun k : Fin count => BitVec.ofNat 8 (digest.toNat / 2^(8*(start+k.val))) := by
  apply List.ext_getElem
  · simp only [digestBytes, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k leftBound rightBound
    have small : k < count := by simpa only [List.length_ofFn] using rightBound
    simp only [List.getElem_take, List.getElem_drop, digestBytes, List.getElem_ofFn]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem digest_bytes_top_zero (digest : Digest) (small : digest.toNat < 2^240) :
    ((digestBytes digest).drop 30).take 2 = List.replicate 2 0 := by
  rw [digest_bytes_window digest 30 2 (by decide)]
  apply List.ext_getElem
  · simp
  · intro k leftBound rightBound
    have below : k < 2 := by simpa only [List.length_ofFn] using leftBound
    simp only [List.getElem_ofFn, List.getElem_replicate]
    have zero : digest.toNat / 2^(8*(30+k)) = 0 := by
      apply Nat.div_eq_of_lt
      calc digest.toNat < 2^240 := small
        _ ≤ 2^(8*(30+k)) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [zero]
    rfl

theorem expand_tagged_tag_bytes (index : Index) (nonce : Nonce128) :
    ((digestBytes (expandTagged index nonce)).drop 16).take 8 = s6TagBytes index := by
  have tagBound : s6Tag index < 2^64 := by
    have bounded := index.isLt
    change index.val < 16777216 at bounded
    unfold s6Tag
    omega
  have value : (expandTagged index nonce).toNat = nonce.toNat+s6Tag index*2^128 := by
    unfold expandTagged
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have nonceBound := nonce.isLt
    calc nonce.toNat+s6Tag index*2^128 < 2^128+s6Tag index*2^128 := Nat.add_lt_add_right nonceBound _
      _ = (s6Tag index+1)*2^128 := by ring
      _ ≤ 2^64*2^128 := Nat.mul_le_mul_right (2^128) (Nat.succ_le_of_lt tagBound)
      _ ≤ 2^256 := by norm_num
  rw [digest_bytes_window _ 16 8 (by decide), value]
  apply List.ext_getElem
  · simp [s6TagBytes]
  · intro k leftBound rightBound
    have below : k < 8 := by simpa only [List.length_ofFn] using leftBound
    simp only [List.getElem_ofFn, s6TagBytes, List.getElem_map, List.getElem_range]
    congr 1
    rw [show 8*(16+k) = 128+8*k by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt nonce.isLt, Nat.zero_add]

theorem expand_tagged_zero_bytes (index : Index) (nonce : Nonce128) :
    ((digestBytes (expandTagged index nonce)).drop 24).take 8 = List.replicate 8 0 := by
  have tagBound : s6Tag index < 2^64 := by
    have bounded := index.isLt
    change index.val < 16777216 at bounded
    unfold s6Tag
    omega
  have small : (expandTagged index nonce).toNat < 2^192 := by
    unfold expandTagged
    rw [BitVec.toNat_ofNat]
    have nonceBound := nonce.isLt
    calc (nonce.toNat+s6Tag index*2^128) % 2^256 ≤ nonce.toNat+s6Tag index*2^128 := Nat.mod_le _ _
      _ < 2^128+s6Tag index*2^128 := Nat.add_lt_add_right nonceBound _
      _ = (s6Tag index+1)*2^128 := by ring
      _ ≤ 2^64*2^128 := Nat.mul_le_mul_right (2^128) (Nat.succ_le_of_lt tagBound)
      _ = 2^192 := by norm_num
  rw [digest_bytes_window _ 24 8 (by decide)]
  apply List.ext_getElem
  · simp
  · intro k leftBound rightBound
    have below : k < 8 := by simpa only [List.length_ofFn] using leftBound
    simp only [List.getElem_ofFn, List.getElem_replicate]
    have zero : (expandTagged index nonce).toNat / 2^(8*(24+k)) = 0 := by
      apply Nat.div_eq_of_lt
      calc (expandTagged index nonce).toNat < 2^192 := small
        _ ≤ 2^(8*(24+k)) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [zero]
    rfl

/-! ### Canonical byte layouts from digest facts -/

private theorem drop_append_long {α : Type} (first second : List α) (count : Nat)
    (long : first.length ≤ count) : (first ++ second).drop count = second.drop (count-first.length) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, count = first.length+extra := ⟨count-first.length, by omega⟩
  rw [List.drop_append]
  simp

private theorem digest_bytes_length' (digest : Digest) : (digestBytes digest).length = 32 := by
  simp [digestBytes]

theorem s6_nodes_canonical_digests (digests : List Digest) (rest : List Byte) :
    S6NodesCanonical digests.length (digests.flatMap digestBytes ++ rest) :=
  s6_nodes_canonical _ _

/-- A record whose salt is tagged. -/
def S6HonestRecord (record : CapLowerRecord) : Prop :=
  ∃ nonce : Nonce128, record.salt = expandTagged record.index nonce

private theorem encoding_split (record : CapLowerRecord) :
    capLowerEncoding record =
      [record.salt] ++ List.ofFn record.others ++ [record.sibling 0] ++
        List.ofFn (fun level : Fin 13 => record.sibling level.succ) := by
  simp only [capLowerEncoding, List.ofFn_succ (n := 13), List.cons_append, List.append_assoc]
  rfl

theorem s6_record_canonical_honest (record : CapLowerRecord) (honest : S6HonestRecord record)
    (rest : List Byte) :
    S6RecordCanonical record.index ((capLowerEncoding record).flatMap digestBytes ++ rest) := by
  obtain ⟨nonce, tagged⟩ := honest
  rw [encoding_split]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  have saltLength := digest_bytes_length' record.salt
  have othersLength : ((List.ofFn record.others).flatMap digestBytes).length = 96 := by
    simp [digest_bytes_length']
  have firstLength := digest_bytes_length' (record.sibling 0)
  refine ⟨?_, ?_, ?_⟩
  · rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp only [List.length_drop]; omega), tagged]
    exact expand_tagged_tag_bytes record.index nonce
  · rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp only [List.length_drop]; omega), tagged]
    exact expand_tagged_zero_bytes record.index nonce
  · exact s6_nodes_canonical _ _

theorem s6_records_canonical_honest (records : List CapLowerRecord) (footer : List Digest)
    (honest : ∀ record ∈ records, S6HonestRecord record) :
    S6RecordsCanonical (records.map CapLowerRecord.index)
      (capDigestEncoding (capLowerTranscript records ++ footer)) := by
  induction records with
  | nil =>
      simp only [List.map_nil, capLowerTranscript, List.flatMap_nil, List.nil_append,
        S6RecordsCanonical]
      rw [cap_digest_encoding_length]
      refine ⟨by omega, ?_⟩
      rw [show 32*footer.length/32 = footer.length by omega]
      exact s6_nodes_canonical _ _
  | cons record tail ih =>
      have head := honest record (by simp)
      have later : ∀ other ∈ tail, S6HonestRecord other := fun other member => honest other (by simp [member])
      have recordLength : ((capLowerEncoding record).flatMap digestBytes).length = 576 := by
        simp [capLowerEncoding, digest_bytes_length']
      have split : capDigestEncoding (capLowerTranscript (record :: tail) ++ footer) =
          (capLowerEncoding record).flatMap digestBytes ++
            capDigestEncoding (capLowerTranscript tail ++ footer) := by
        simp only [capDigestEncoding, capLowerTranscript, List.flatMap_cons, List.flatMap_append,
          List.append_assoc]
      simp only [List.map_cons, S6RecordsCanonical]
      rw [split]
      refine ⟨by simp only [List.length_append, recordLength]; omega,
        s6_record_canonical_honest record head _, ?_⟩
      rw [drop_append_long _ _ _ (by omega)]
      simp only [recordLength, Nat.sub_self, List.drop_zero]
      exact ih later

/-! ### The honest opening -/

theorem cap_honest_record_canonical (message : Message) (committed : MachineState) (index : Index) :
    S6HonestRecord (capHonestLowerRecord message committed index) :=
  ⟨committedNonce committed index, rfl⟩

/-- The cap-level proof the opener emits from a committed trapdoor is canonical. -/
theorem cap_honest_loaded_canonical (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    S6Canonical positions
      (capOpenLoadedBytes (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor)
        positions) := by
  have encoded : capOpenLoadedBytes
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions =
      capDigestEncoding (capLowerTranscript (capHonestLowerRecords message committed positions) ++
        capOpenBoundaryDigests
          (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions) := by
    rw [capOpenLoadedBytes, cap_honest_lower_loaded_transcript message committed positions]
    simp only [capDigestEncoding, List.flatMap_append]
  have order : (capHonestLowerRecords message committed positions).map CapLowerRecord.index =
      positions.sort (· ≤ ·) := by
    simp only [capHonestLowerRecords, List.map_map, capOpenRequestedIndices]
    exact List.map_id _
  unfold S6Canonical
  rw [encoded, ← order]
  apply s6_records_canonical_honest
  intro record member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact cap_honest_record_canonical message committed index

end CommitGolfCandidate
