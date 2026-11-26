import CommitGolfCandidate.ChainedAlignedBits
import CommitGolfCandidate.ChainedOpeningCodec

/-! Payload-derived low-byte copies and two-byte native tail descriptors. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf SplitCodec

def lowRows : {spec : Spec} → Payload spec → List (List Bool)
  | [],.nil => []
  | (low,_)::_,.cons value rest => (List.ofFn fun b : Fin low => value.getLsbD b.val)::lowRows rest

def highRows : {spec : Spec} → Payload spec → List (List Bool)
  | [],.nil => []
  | (low,high)::_,.cons value rest =>
    (List.ofFn fun b : Fin high => value.getLsbD (low+b.val))::highRows rest

@[simp] theorem low_rows_flatten {spec : Spec} (payload : Payload spec) :
    (lowRows payload).flatten=lows payload := by
  induction payload <;> simp_all [lowRows,lows]

@[simp] theorem high_rows_flatten {spec : Spec} (payload : Payload spec) :
    (highRows payload).flatten=highs payload := by
  induction payload <;> simp_all [highRows,highs]

@[simp] theorem high_rows_widths {spec : Spec} (payload : Payload spec) :
    (highRows payload).map List.length=spec.map Prod.snd := by
  induction payload <;> simp_all [highRows]

@[simp] theorem high_rows_length {spec : Spec} (payload : Payload spec) : (highRows payload).length=spec.length := by
  induction payload <;> simp_all [highRows]

def lowBytes {spec : Spec} (payload : Payload spec) : Proof := (lowRows payload).flatMap packedBits

theorem low_bytes_packed {spec : Spec} (payload : Payload spec)
    (aligned : ∀ field ∈ spec, field.1%8=0) : lowBytes payload=packedBits (lows payload) := by
  induction payload with
  | nil => rfl
  | @cons low high spec value rest ih =>
    have first : low%8=0 := aligned (low,high) (by simp)
    have tail : ∀ field ∈ spec, field.1%8=0 := fun field member => aligned field (by simp [member])
    change packedBits (List.ofFn fun b : Fin low => value.getLsbD b.val)++lowBytes rest = _
    rw [ih tail,lows,packed_bits_append _ _ (by simpa using first)]

theorem low_count_aligned (spec : Spec) (aligned : ∀ field ∈ spec, field.1%8=0) : lowCount spec%8=0 := by
  induction spec with
  | nil => rfl
  | cons field spec ih =>
    have first := aligned field (by simp)
    have rest := ih (fun entry member => aligned entry (by simp [member]))
    change (field.1+lowCount spec)%8=0
    omega

theorem encode_descriptors {spec : Spec} (payload : Payload spec)
    (aligned : ∀ field ∈ spec, field.1%8=0) :
    encode payload=lowBytes payload++packedBits (highRows payload).flatten := by
  rw [high_rows_flatten,low_bytes_packed payload aligned]
  exact packed_bits_append (lows payload) (highs payload) (by
    rw [lows_length]
    exact low_count_aligned spec aligned)

def descriptorBytes : List (List Bool) → Proof
  | [] => []
  | bits::rest => tailBitsWord 8 bits::BitVec.ofNat 8 bits.length::descriptorBytes rest

@[simp] theorem descriptor_bytes_length (rows : List (List Bool)) : (descriptorBytes rows).length=2*rows.length := by
  induction rows <;> simp_all [descriptorBytes] <;> omega

theorem descriptor_value (rows : List (List Bool)) (index : Nat) (inside : index<rows.length) :
    (descriptorBytes rows).getD (2*index) 0=tailBitsWord 8 (rows.getD index []) := by
  induction rows generalizing index with
  | nil => simp at inside
  | cons bits rows ih =>
    cases index with
    | zero => rfl
    | succ index =>
      rw [show 2*(index+1)=2*index+2 by omega]
      simpa only [descriptorBytes,List.getD_cons_succ] using ih index (by simpa using inside)

theorem descriptor_width (rows : List (List Bool)) (index : Nat) (inside : index<rows.length) :
    (descriptorBytes rows).getD (2*index+1) 0=BitVec.ofNat 8 (rows.getD index []).length := by
  induction rows generalizing index with
  | nil => simp at inside
  | cons bits rows ih =>
    cases index with
    | zero => rfl
    | succ index =>
      rw [show 2*(index+1)+1=(2*index+1)+2 by omega]
      simpa only [descriptorBytes,List.getD_cons_succ] using ih index (by simpa using inside)

theorem record_descriptor_widths (record : InteriorCodec.Record) :
    (highRows record).map List.length=[1,6,2,2,2,2,2,2,2,2,1,0,0,0,0,0,0] := by
  rw [high_rows_widths]
  decide +kernel

theorem record_descriptor_encoding (record : InteriorCodec.Record) :
    encode record=lowBytes record++packedBits (highRows record).flatten := by
  apply encode_descriptors
  decide +kernel

theorem footer_descriptor_encoding (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    encode footer=lowBytes footer++packedBits (highRows footer).flatten := by
  apply encode_descriptors
  intro field member
  obtain ⟨node,_,same⟩ := List.mem_map.mp member
  subst field
  change 232%8=0
  decide

theorem low_bytes_length {spec : Spec} (payload : Payload spec)
    (aligned : ∀ field ∈ spec, field.1%8=0) : (lowBytes payload).length=lowCount spec/8 := by
  rw [low_bytes_packed payload aligned,packed_bits_length,lows_length]
  have divisible := low_count_aligned spec aligned
  omega

theorem high_rows_small {spec : Spec} (payload : Payload spec)
    (small : ∀ field ∈ spec, field.2≤6) (row : List Bool) (member : row ∈ highRows payload) : row.length≤6 := by
  have width : row.length ∈ spec.map Prod.snd := by
    rw [←high_rows_widths payload]
    exact List.mem_map_of_mem member
  obtain ⟨field,belongs,same⟩ := List.mem_map.mp width
  rw [←same]
  exact small field belongs

theorem record_rows_small (record : InteriorCodec.Record) (row : List Bool) (member : row ∈ highRows record) :
    row.length≤6 := by
  exact high_rows_small record (by decide +kernel) row member

theorem footer_rows_small (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (row : List Bool) (member : row ∈ highRows footer) : row.length≤6 := by
  apply high_rows_small footer _ row member
  intro field belongs
  obtain ⟨node,_,same⟩ := List.mem_map.mp belongs
  subst field
  change InteriorCodec.footerWidth node-232≤6
  unfold InteriorCodec.footerWidth
  split <;> omega

theorem footer_low_bytes_length (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    (lowBytes footer).length=29*nodes.length := by
  have aligned : ∀ field ∈ InteriorCodec.footerSpec nodes, field.1%8=0 := by
    intro field member
    obtain ⟨node,_,same⟩ := List.mem_map.mp member
    subst field
    change 232%8=0
    decide
  have count : lowCount (InteriorCodec.footerSpec nodes)=232*nodes.length := by
    clear footer aligned
    induction nodes with
    | nil => rfl
    | cons node nodes ih =>
      change 232+lowCount (InteriorCodec.footerSpec nodes)=232*(nodes.length+1)
      rw [ih]
      omega
  rw [low_bytes_length footer aligned,count]
  omega

theorem record_descriptor_sizes (record : InteriorCodec.Record) :
    (lowBytes record).length=479 ∧ (packedBits (highRows record).flatten).length=3 ∧
      (descriptorBytes (highRows record)).length=34 := by
  have aligned : ∀ field ∈ InteriorCodec.recordSpec, field.1%8=0 := by decide +kernel
  rw [low_bytes_packed record aligned,packed_bits_length,packed_bits_length,
    high_rows_flatten,lows_length,highs_length,descriptor_bytes_length,high_rows_length]
  decide +kernel

end CommitGolfCandidate.Chained.Native
