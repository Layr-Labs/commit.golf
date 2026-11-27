import CommitGolfCandidate.ChainedQueryGraph

/-! An 768-bit layout for disjoint height and stage domains. -/
namespace CommitGolfCandidate.Chained
set_option exponentiation.threshold 800

abbrev Symbol := (Height × Seed) ⊕ (Height × Fin 15 × Output)

/-- Class zero models any zero-gap binary parent, including untagged shortened levels. -/
def firstTag (h : Height) : Nat := if h.val=0 then 0 else 2^63+256*(h.val+1)
def nextTag (h : Height) (j : Fin 15) : Nat := 2^63+256*(h.val+1)+(j.val+1)
def symbolCode : Symbol → Nat
  | .inl (h, seed) => 2^512*firstTag h+seed.toNat
  | .inr (h, j, value) => 2^512*nextTag h j+value.toNat

def pack (s : Symbol) : Input := BitVec.ofNat 768 (symbolCode s)

theorem symbol_code_small (s : Symbol) : symbolCode s<2^768 := by
  rcases s with ⟨h,v⟩|⟨h,j,v⟩
  · have := v.isLt;have := h.isLt;simp only [symbolCode,firstTag];split <;> omega
  · have := h.isLt;have := j.isLt;have := v.isLt;simp only [symbolCode,nextTag];omega

private theorem separate (h k : Height) (s : Seed) (j : Fin 15) (v : Output) :
    symbolCode (.inl (h,s))≠symbolCode (.inr (k,j,v)) := by
  have := s.isLt;have := v.isLt;have := j.isLt
  intro same
  have tags : firstTag h=nextTag k j := by simp only [symbolCode] at same;omega
  unfold nextTag firstTag at tags;split at tags <;> omega

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
      have e : firstTag ha=firstTag hb := by omega
      have hh : ha.val=hb.val := by unfold firstTag at e; split at e <;> split at e <;> omega
      have hs : sa.toNat=sb.toNat := by rw [e] at codes;omega
      exact congrArg Sum.inl (Prod.ext (Fin.ext hh) (BitVec.eq_of_toNat_eq hs))
    | inr b =>
      obtain ⟨hb,jb,vb⟩ := b
      exact False.elim (separate ha hb sa jb vb codes)
  | inr a =>
    obtain ⟨ha,ja,va⟩ := a
    cases b with
    | inl b =>
      obtain ⟨hb,sb⟩ := b
      exact False.elim (separate hb ha sb ja va codes.symm)
    | inr b =>
      obtain ⟨hb,jb,vb⟩ := b
      have hva := va.isLt
      have hvb := vb.isLt
      have hja := ja.isLt
      have hjb := jb.isLt
      simp only [symbolCode] at codes
      have e : nextTag ha ja=nextTag hb jb := by omega
      have hh : ha.val=hb.val := by unfold nextTag at e; omega
      have hj : ja.val=jb.val := by unfold nextTag at e; omega
      have hv : va.toNat=vb.toNat := by rw [e] at codes;omega
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
  if stage : 0 < j ∧ j < 16 then pack (.inr (h,⟨j-1,by omega⟩,value)) else 0

theorem encodeNext_valid (h : Height) (j : Nat) (value : Output)
    (positive : 0 < j) (bounded : j < 16) :
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
