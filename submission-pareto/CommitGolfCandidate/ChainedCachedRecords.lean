import CommitGolfCandidate.ChainedCachedGeometry

/-! Typed records reconstructed from the chained cached heap and masked salts. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

theorem cached_widths_of_getElem (spec : Spec) (values : Nat → BitVec 256)
    (bounds : ∀ index (inside : index<spec.length), (values index).toNat<2^((spec[index]).1+(spec[index]).2)) :
    CachedWidths spec values := by
  induction spec generalizing values with
  | nil => trivial
  | cons field spec ih =>
    rcases field with ⟨low,high⟩
    constructor
    · exact bounds 0 (by simp)
    · apply ih
      intro index inside
      exact bounds (index+1) (by simpa)

def cachedRecordWords (heap : Nat → BitVec 238) (salt : BitVec 128) (index : Index) (ordinal : Nat) : BitVec 256 :=
  if ordinal=0 then salt.setWidth 256 else (heap (lowerNode index (ordinal-1) ^^^ 1)).setWidth 256

def cachedRecord (heap : Nat → BitVec 238) (salt : BitVec 128) (index : Index) : InteriorCodec.Record :=
  cachedPayload InteriorCodec.recordSpec (cachedRecordWords heap salt index)

theorem cached_record_widths (oracle : Oracle) (leaves : Nat → BitVec 238) (salt : BitVec 128)
    (index : Index) (masked : salt.toNat<2^121) :
    CachedWidths InteriorCodec.recordSpec (cachedRecordWords (referenceHeap oracle leaves) salt index) := by
  apply cached_widths_of_getElem
  intro ordinal inside
  cases ordinal with
  | zero =>
    change (salt.setWidth 256).toNat<2^(120+1)
    rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt (salt.isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (by decide : 128≤256)))]
    exact masked
  | succ ordinal => cases ordinal with
    | zero =>
      change ((referenceHeap oracle leaves (lowerNode index 0 ^^^ 1)).setWidth 256).toNat<2^(232+6)
      rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt ((referenceHeap oracle leaves _).isLt.trans_le
        (Nat.pow_le_pow_right (by decide) (by decide : 238≤256)))]
      exact (referenceHeap oracle leaves _).isLt
    | succ ordinal =>
      have bounded : ordinal<15 := by
        simp only [InteriorCodec.recordSpec,List.length_cons,List.length_ofFn] at inside
        omega
      have lower := width_lower ⟨ordinal,by omega⟩
      have bound := cached_lower_width oracle leaves index ⟨ordinal,bounded⟩
      simp only [InteriorCodec.recordSpec,List.getElem_cons_succ,List.getElem_ofFn]
      change ((referenceHeap oracle leaves (lowerNode index (ordinal+1) ^^^ 1)).setWidth 256).toNat<
        2^(232+(width ⟨ordinal,by omega⟩-232))
      rw [Nat.add_sub_of_le lower,BitVec.toNat_setWidth,Nat.mod_eq_of_lt
        ((referenceHeap oracle leaves _).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by decide : 238≤256)))]
      exact bound

theorem cached_record_raw_bytes (oracle : Oracle) (leaves : Nat → BitVec 238) (salt : BitVec 128)
    (index : Index) (masked : salt.toNat<2^121) :
    rawFieldsBytes (recordRawFields (cachedRecord (referenceHeap oracle leaves) salt index))=
      cachedSourceBytes InteriorCodec.recordSpec recordSourcePads (cachedRecordWords (referenceHeap oracle leaves) salt index) := by
  apply cached_payload_raw_bytes
  · decide +kernel
  · decide
  · exact cached_record_widths oracle leaves salt index masked

theorem cached_salt_word_bytes (salt : BitVec 128) :
    (List.ofFn fun byte : Fin 16 => (salt.setWidth 256).extractLsb' (8*byte.val) 8)=saltBytes salt := by
  apply congrArg List.ofFn
  funext byte
  apply BitVec.extractLsb'_setWidth_of_le
  have := byte.isLt
  omega

theorem cached_record_source (heap : Nat → BitVec 238) (salt : BitVec 128) (index : Index) :
    cachedSourceBytes InteriorCodec.recordSpec recordSourcePads (cachedRecordWords heap salt index)=
      lowerRecord true (fun node => (heap node).setWidth 256) index salt := by
  unfold lowerRecord
  rw [←cached_salt_word_bytes salt]
  rfl

end CommitGolfCandidate.Chained.Native
