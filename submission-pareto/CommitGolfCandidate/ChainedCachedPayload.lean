import CommitGolfCandidate.ChainedCachedBounds

/-! Reconstruct typed payloads from canonical serialized cached words. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

def cachedPayload : (spec : Spec) → (Nat → BitVec 256) → Payload spec
  | [],_ => .nil
  | (low,high)::spec,values => .cons ((values 0).setWidth (low+high))
      (cachedPayload spec (fun index => values (index+1)))

def CachedWidths : Spec → (Nat → BitVec 256) → Prop
  | [],_ => True
  | (low,high)::spec,values => (values 0).toNat<2^(low+high) ∧
      CachedWidths spec (fun index => values (index+1))

def cachedSourceBytes : Spec → List Proof → (Nat → BitVec 256) → Proof
  | [],_,_ => []
  | (low,_)::spec,pads,values =>
      (List.ofFn fun byte : Fin (low/8+1+(pads.headD []).length) => (values 0).extractLsb' (8*byte.val) 8)++
        cachedSourceBytes spec pads.tail (fun index => values (index+1))

theorem canonical_resize (value : BitVec 256) (width target : Nat) (small : value.toNat<2^width) :
    (value.setWidth width).setWidth target=value.setWidth target := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,Nat.mod_eq_of_lt small]

theorem cached_raw_field_bytes (low high : Nat) (value : BitVec (low+high)) (padding : Nat)
    (highSmall : high<7) (paddingSmall : padding<3) (aligned : low%8=0) :
    (cachedRawField low high value padding highSmall paddingSmall).bytes=
      List.ofFn (fun byte : Fin (low/8+1+padding) => value.extractLsb' (8*byte.val) 8) := by
  have length : (cachedRawField low high value padding highSmall paddingSmall).bytes.length=low/8+1+padding := by
    simp only [cachedRawField,RawField.bytes,List.length_append,packed_bits_length,List.length_ofFn,
      List.length_cons,List.length_replicate]
    omega
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using length
  · intro index left right
    have inside : index<low/8+1+padding := by simpa only [length] using left
    have byte := cached_raw_field_byte low high value padding index highSmall paddingSmall aligned inside
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem left] at byte
    simpa only [Option.getD_some,List.getElem_ofFn] using byte

theorem cached_payload_raw_bytes (spec : Spec) (values : Nat → BitVec 256) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2)
    (aligned : ∀ field ∈ spec, field.1%8=0)
    (zeros : ∀ pad ∈ pads, pad=List.replicate pad.length 0) (widths : CachedWidths spec values) :
    rawFieldsBytes (payloadRawFields (cachedPayload spec values) pads small padSmall)=cachedSourceBytes spec pads values := by
  induction spec generalizing values pads with
  | nil => rfl
  | cons field spec ih =>
    rcases field with ⟨low,high⟩
    have highSmall : high<7 := by have := small (low,high) (by simp); omega
    have paddingSmall : (pads.headD []).length<3 := by
      cases pads with
      | nil => simp
      | cons pad pads => have := padSmall pad (by simp); simpa using (show pad.length<3 by omega)
    have headZeros : pads.headD []=List.replicate (pads.headD []).length 0 := by
      cases pads with
      | nil => rfl
      | cons pad pads => exact zeros pad (by simp)
    have tailSmall : ∀ pad ∈ pads.tail, pad.length≤2 := by
      intro pad member
      exact padSmall pad (List.mem_of_mem_tail member)
    have tailZeros : ∀ pad ∈ pads.tail, pad=List.replicate pad.length 0 := by
      intro pad member
      exact zeros pad (List.mem_of_mem_tail member)
    have tailResult := ih (fun index => values (index+1)) pads.tail
      (fun field member => small field (by simp [member])) tailSmall
      (fun field member => aligned field (by simp [member])) tailZeros widths.2
    change (packedBits (List.ofFn fun bit : Fin low => ((values 0).setWidth (low+high)).getLsbD bit.val)++
      tailBitsWord 8 (List.ofFn fun bit : Fin high => ((values 0).setWidth (low+high)).getLsbD (low+bit.val))::pads.headD [])++
      rawFieldsBytes (payloadRawFields (cachedPayload spec (fun index => values (index+1))) pads.tail _ _)=_
    rw [tailResult,headZeros]
    have head := cached_raw_field_bytes low high ((values 0).setWidth (low+high)) (pads.headD []).length
      highSmall paddingSmall (aligned (low,high) (by simp))
    change _++_= _
    rw [show packedBits (List.ofFn fun bit : Fin low => ((values 0).setWidth (low+high)).getLsbD bit.val)++
        tailBitsWord 8 (List.ofFn fun bit : Fin high => ((values 0).setWidth (low+high)).getLsbD (low+bit.val))::
          List.replicate (pads.headD []).length 0=_ from head]
    conv => rhs; rw [cachedSourceBytes]
    congr 1
    apply congrArg List.ofFn
    funext byte
    have resized := canonical_resize (values 0) (low+high) (8*byte.val+8) widths.1
    have bits := congrArg (fun value => value.extractLsb' (8*byte.val) 8) resized
    rw [BitVec.extractLsb'_setWidth_of_le (b := (values 0).setWidth (low+high))
      (start := 8*byte.val) (len := 8) (w' := 8*byte.val+8) (by omega),
      BitVec.extractLsb'_setWidth_of_le (b := values 0) (start := 8*byte.val)
        (len := 8) (w' := 8*byte.val+8) (by omega)] at bits
    exact bits

end CommitGolfCandidate.Chained.Native
