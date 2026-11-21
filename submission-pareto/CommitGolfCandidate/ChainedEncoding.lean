import CommitGolfCandidate.ChainedQueryGraph

/-! An explicit512-bit layout for disjoint height and stage domains. -/
namespace CommitGolfCandidate.Chained
set_option exponentiation.threshold 520

abbrev Symbol := (Height × Seed) ⊕ (Height × Fin 7 × Output)

def symbolCode : Symbol → Nat
  | .inl (h, seed) => 2^476*h.val+seed.toNat
  | .inr (h, j, value) => 2^511+2^256*(7*h.val+j.val)+value.toNat

def pack (symbol : Symbol) : Input := BitVec.ofNat 512 (symbolCode symbol)

theorem first_code_small (h : Height) (seed : Seed) : symbolCode (.inl (h,seed)) < 2^511 := by
  have hh := h.isLt
  have hs := seed.isLt
  simp only [symbolCode]
  omega

theorem symbol_code_small (symbol : Symbol) : symbolCode symbol < 2^512 := by
  cases symbol with
  | inl pair =>
    obtain ⟨h,seed⟩ := pair
    have := first_code_small h seed
    omega
  | inr triple =>
    obtain ⟨h,j,value⟩ := triple
    have hh := h.isLt
    have hj := j.isLt
    have hv := value.isLt
    simp only [symbolCode]
    omega

theorem pack_value (symbol : Symbol) : (pack symbol).toNat = symbolCode symbol := by
  exact Nat.mod_eq_of_lt (symbol_code_small symbol)

theorem pack_injective : Function.Injective pack := by
  intro a b same
  have codes := congrArg BitVec.toNat same
  rw [pack_value,pack_value] at codes
  cases a with
  | inl a =>
    obtain ⟨ha,sa⟩ := a
    cases b with
    | inl b =>
      obtain ⟨hb,sb⟩ := b
      have hsa := sa.isLt
      have hsb := sb.isLt
      simp only [symbolCode] at codes
      have hh : ha.val = hb.val := by omega
      have hs : sa.toNat = sb.toNat := by omega
      exact congrArg Sum.inl (Prod.ext (Fin.ext hh) (BitVec.eq_of_toNat_eq hs))
    | inr b =>
      obtain ⟨hb,jb,vb⟩ := b
      have low := first_code_small ha sa
      simp only [symbolCode] at codes low
      omega
  | inr a =>
    obtain ⟨ha,ja,va⟩ := a
    cases b with
    | inl b =>
      obtain ⟨hb,sb⟩ := b
      have low := first_code_small hb sb
      simp only [symbolCode] at codes low
      omega
    | inr b =>
      obtain ⟨hb,jb,vb⟩ := b
      have hva := va.isLt
      have hvb := vb.isLt
      have hja := ja.isLt
      have hjb := jb.isLt
      simp only [symbolCode] at codes
      have hi : 7*ha.val+ja.val = 7*hb.val+jb.val := by omega
      have hh : ha.val = hb.val := by omega
      have hj : ja.val = jb.val := by omega
      have hv : va.toNat = vb.toNat := by omega
      exact congrArg Sum.inr (Prod.ext (Fin.ext hh)
        (Prod.ext (Fin.ext hj) (BitVec.eq_of_toNat_eq hv)))

noncomputable def unpack (value : Input) : Option Symbol :=
  if found : ∃ symbol, pack symbol = value then some found.choose else none

theorem unpack_pack (symbol : Symbol) : unpack (pack symbol) = some symbol := by
  classical
  rw [unpack, dif_pos ⟨symbol,rfl⟩]
  congr 1
  exact pack_injective (Exists.choose_spec (show ∃ s, pack s = pack symbol from ⟨symbol,rfl⟩))

def encodeNext (h : Height) (j : Nat) (value : Output) : Input :=
  if stage : 0 < j ∧ j < 8 then pack (.inr (h,⟨j-1,by omega⟩,value)) else 0

theorem encodeNext_valid (h : Height) (j : Nat) (value : Output)
    (positive : 0 < j) (bounded : j < 8) :
    encodeNext h j value = pack (.inr (h,⟨j-1,by omega⟩,value)) := by
  exact dif_pos ⟨positive,bounded⟩

noncomputable def decodeTag (value : Input) : Option (Height × Nat) :=
  (unpack value).map fun symbol => match symbol with
    | .inl (h,_) => (h,0)
    | .inr (h,j,_) => (h,j.val+1)

noncomputable def decodeLink (value : Input) : Option Output :=
  (unpack value).bind fun symbol => match symbol with
    | .inl _ => none
    | .inr (_,_,value) => some value

noncomputable def canonicalEncoding : Encoding where
  first h seed := pack (.inl (h,seed))
  next := encodeNext
  tag := decodeTag
  link := decodeLink
  first_tag h seed := by simp only [decodeTag,unpack_pack,Option.map_some]
  next_tag h j value positive bounded := by
    rw [encodeNext_valid h j value positive bounded]
    simp only [decodeTag,unpack_pack,Option.map_some]
    congr 2
    omega
  next_link h j value positive bounded := by
    rw [encodeNext_valid h j value positive bounded]
    simp [decodeLink,unpack_pack]
  first_injective h := by
    intro a b same
    exact (Prod.mk.inj (Sum.inl.inj (pack_injective same))).2
  next_injective h j positive bounded := by
    intro a b same
    rw [encodeNext_valid h j a positive bounded,encodeNext_valid h j b positive bounded] at same
    exact (Prod.mk.inj (Prod.mk.inj (Sum.inr.inj (pack_injective same))).2).2

end CommitGolfCandidate.Chained
