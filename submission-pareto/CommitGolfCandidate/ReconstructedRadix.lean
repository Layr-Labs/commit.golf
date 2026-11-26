import CommitGolfCandidate.ReconstructedProfile

namespace CommitGolfCandidate.Reconstruction

/-- The first coordinate varies fastest. This coordinate convention makes no assumption
about the byte order or traversal order of machine memory. -/
inductive Digits : List Nat → Type where
  | nil : Digits []
  | cons {base : Nat} {bases : List Nat} : Fin base → Digits bases → Digits (base :: bases)

def Digits.pack {bases : List Nat} : Digits bases → Fin bases.prod
  | .nil => ⟨0, by decide⟩
  | @cons b bs d ds =>
    let v := ds.pack
    ⟨d.val + b * v.val, by
      have h := Nat.mul_le_mul_left b (Nat.succ_le_of_lt v.isLt)
      have hd := d.isLt
      rw [Nat.mul_succ] at h
      simp only [List.prod_cons]
      omega⟩

def Digits.unpack : (bs : List Nat) → Fin bs.prod → Digits bs
  | [], _ => .nil
  | b :: bs, x =>
    have h : x.val < b * bs.prod := x.isLt
    have pos : 0 < b := by
      cases b with
      | zero => simp at h
      | succ => omega
    .cons ⟨x.val % b, Nat.mod_lt _ pos⟩
      (unpack bs ⟨x.val / b, (Nat.div_lt_iff_lt_mul pos).mpr (Nat.mul_comm b bs.prod ▸ h)⟩)

theorem Digits.pack_unpack (bs : List Nat) (x : Fin bs.prod) :
    (unpack bs x).pack = x := by
  induction bs with
  | nil =>
    apply Fin.ext
    have h : x.val < 1 := x.isLt
    change 0 = x.val
    omega
  | cons r rs ih =>
    apply Fin.ext
    simp only [unpack, pack, ih]
    exact Nat.mod_add_div _ _

theorem Digits.unpack_pack {bs : List Nat} (ds : Digits bs) : unpack bs ds.pack = ds := by
  induction ds with
  | nil => rfl
  | @cons b bs d ds ih =>
    have pos := Nat.zero_lt_of_lt d.isLt
    simp only [pack, unpack]
    congr 1
    · apply Fin.ext
      exact (Nat.add_mul_mod_self_left _ _ _).trans (Nat.mod_eq_of_lt d.isLt)
    · refine Eq.trans ?_ ih
      apply congrArg (unpack bs)
      apply Fin.ext
      simp [Nat.add_mul_div_left _ _ pos, Nat.div_eq_of_lt d.isLt]

def lowerHeader (ds : Digits sameSize.recordBases) : Fin (2 ^ sameSize.headerBits) :=
  ⟨ds.pack.val, Nat.lt_of_lt_of_le ds.pack.isLt header_capacity.2⟩

def readLowerHeader (h : Fin (2 ^ sameSize.headerBits)) : Option (Digits sameSize.recordBases) :=
  if ok : h.val < sameSize.recordBases.prod then some (Digits.unpack _ ⟨h.val, ok⟩) else none

theorem lower_header_roundtrip (ds : Digits sameSize.recordBases) :
    readLowerHeader (lowerHeader ds) = some ds := by
  simp [readLowerHeader, lowerHeader, ds.pack.isLt, Digits.unpack_pack]

abbrev CapDigits := Digits [211, 211, 211, 211]

def capHeader (ds : CapDigits) : Fin (2 ^ sameSize.capHeader) :=
  ⟨ds.pack.val, Nat.lt_of_lt_of_le ds.pack.isLt (by decide)⟩

def readCapHeader (h : Fin (2 ^ sameSize.capHeader)) : Option CapDigits :=
  if ok : h.val < [211, 211, 211, 211].prod then some (Digits.unpack _ ⟨h.val, ok⟩) else none

theorem cap_header_roundtrip (ds : CapDigits) :
    readCapHeader (capHeader ds) = some ds := by
  unfold readCapHeader capHeader
  rw [dite_eq_left ds.pack.isLt]
  exact congrArg some (Digits.unpack_pack ds)

end CommitGolfCandidate.Reconstruction
