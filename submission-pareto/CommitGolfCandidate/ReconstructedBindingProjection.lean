import CommitGolfCandidate.ReconstructedProfile

namespace CommitGolfCandidate.Reconstruction.Binding

/-- The first three machine words and the fourth word, in memory order. -/
abbrev Digest := BitVec 192 × BitVec 64

def width (d : Nat) := sameSize.widths[d]?.getD 0

def modulus (d : Nat) := sameSize.moduli[d]?.getD 0

def work (d : Nat) := max 1 (sameSize.calls[d]?.getD 0)

/-- Effective range of the high word. For an ordinary node the range is a
power of two. The paid residue operation uses the listed modulus itself. -/
def radix (d : Nat) :=
  if modulus d = 0 then 2^(width d - 192) else modulus d

def project (d : Nat) (raw : Digest) : Digest :=
  (raw.1, BitVec.ofNat 64 (raw.2.toNat % radix d))

theorem radix_pos (d : Nat) : 0 < radix d := by
  unfold radix
  split <;> rename_i h
  · exact Nat.two_pow_pos _
  · omega

private theorem profile_ranges : ∀ d : Fin 25,
    radix d ≤ 2^(width d - 192) ∧ 192 ≤ width d ∧ width d ≤ 256 ∧
    (0 < d.val → width d ≤ 240) := by decide

theorem ranges (d : Nat) (lt : d < 25) :
    radix d ≤ 2^(width d - 192) ∧ 192 ≤ width d ∧ width d ≤ 256 ∧
    (0 < d → width d ≤ 240) := profile_ranges ⟨d, lt⟩

private theorem mod_fits (d : Nat) (w : BitVec 64) :
    w.toNat % radix d < 2^64 :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) w.isLt

theorem project_hi (d : Nat) (raw : Digest) :
    (project d raw).2.toNat = raw.2.toNat % radix d := by
  simp [project, Nat.mod_eq_of_lt (mod_fits d _)]

def Canonical (d : Nat) (x : Digest) := x.2.toNat < radix d

theorem canonical_project (d : Nat) (raw : Digest) : Canonical d (project d raw) := by
  unfold Canonical
  rw [project_hi]
  exact Nat.mod_lt _ (radix_pos d)

theorem project_of_canonical (d : Nat) (x : Digest) (h : Canonical d x) :
    project d x = x := by
  refine Prod.ext (x := project d x) (y := x) rfl ?_
  exact BitVec.eq_of_toNat_eq ((project_hi _ _).trans (Nat.mod_eq_of_lt h))

/-- The size of the largest preimage of one projected digest. The unchanged
192 low bits leave just the high-word quotient as the index within a fiber. -/
def fiberSize (d : Nat) := (2^64-1) / radix d + 1

def rank (d : Nat) (x : Digest) : Fin (fiberSize d) :=
  ⟨x.2.toNat / radix d, Nat.lt_succ_of_le (Nat.div_le_div_right (by have := x.2.isLt; omega))⟩

def Fiber (d : Nat) (target : Digest) := { x : Digest // project d x = target }

theorem rank_injective (d : Nat) (target : Digest) (a b : Fiber d target)
    (same : rank d a.val = rank d b.val) : a = b := by
  have eq := a.property.trans b.property.symm
  have lo := congrArg Prod.fst eq
  change a.val.1 = b.val.1 at lo
  have hi := congrArg (fun v : Digest => v.2.toNat) eq
  change (project d _).2.toNat = (project d _).2.toNat at hi
  rw [project_hi, project_hi] at hi
  have quotient := congrArg Fin.val same
  change a.val.2.toNat / radix d = b.val.2.toNat / radix d at quotient
  apply Subtype.ext
  apply Prod.ext lo
  apply BitVec.eq_of_toNat_eq
  rw [← Nat.div_add_mod a.val.2.toNat (radix d), quotient, hi, Nat.div_add_mod]

/-- At every internal depth, the exact fiber divided by the square of the
scheduled work is at most this rational number times the 238-bit fiber.
The table check uses integer arithmetic only. -/
theorem normalized_fiber : ∀ d : Fin 24,
    1000000 * fiberSize d ≤ 1221263 * 2^18 * (work d)^2 := by decide

/-- Upper-halfword label in a canonical binary query. Leaf children keep
the all-ones marker. Internal children have their depth as the label. -/
def tag (d : Nat) : BitVec 64 := if d = 24 then 65535 else BitVec.ofNat 64 d

def childMask (d : Nat) (right : Bool) : BitVec 64 :=
  if modulus d = 0 then (tag d <<< 48) ||| BitVec.ofNat 64 (2^48 - 2^(width d - 192))
  else if right then tag d <<< 48 else 0

def marked (child : Nat) (right : Bool) (x : Digest) : Digest :=
  (x.1, x.2 ||| childMask child right)

theorem child_width (d : Nat) (positive : 0 < d) (lt : d < 25) :
    width d - 192 ≤ 48 := by have := (ranges d lt).2.2.2 positive; omega

/-- Low bits of a marked child prefix are exactly the bits of its canonical digest.
In particular decoration cannot merge two different canonical children. -/
private theorem retain_word (d : Fin 25) (right : Bool) (v : BitVec 64)
    (fit : v.toNat < radix d) (positive : 0 < d.val) :
    ((marked d right (0,v)).2 &&& BitVec.ofNat 64 (2^(width d - 192) - 1)) = v := by
  have bound : v.toNat < 2^(width d - 192) := Nat.lt_of_lt_of_le fit (ranges d d.isLt).1
  have law (a b c : BitVec 64) : (a ||| b) &&& c = (a &&& c) ||| (b &&& c) :=
    BitVec.and_or_distrib_right
  unfold marked
  rw [law]
  have zero : ∀ n : Fin 25, 0 < n.val → ∀ r : Bool,
      childMask n r &&& BitVec.ofNat 64 (2^(width n - 192)-1) = 0 := by decide
  rw [zero d positive right]
  change (v &&& _ ||| 0#64) = v
  rw [BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have upper : 2^(width d - 192) ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by have := child_width d positive d.isLt; omega)
  rw [Nat.mod_eq_of_lt (by have := Nat.two_pow_pos (width d - 192); omega)]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt bound]

theorem marked_injective (d : Fin 25) (positive : 0 < d.val) (right : Bool) {x y : Digest}
    (xc : Canonical d x) (yc : Canonical d y) (eq : marked d right x = marked d right y) :
    x = y := by
  have lo := congrArg Prod.fst eq
  change x.1 = y.1 at lo
  refine Prod.ext (x := x) (y := y) lo ?_
  have h := congrArg (fun v : Digest => v.2 &&& BitVec.ofNat 64 (2^(width d - 192)-1)) eq
  exact (retain_word d right x.2 xc positive).symm.trans (h.trans (retain_word d right y.2 yc positive))

theorem marked_tag (d : Fin 25) (pos : 0 < d.val) (x : Digest) (can : Canonical d x) :
    (marked d true x).2 >>> 48 = tag d := by
  have small : x.2.toNat < 2^48 := Nat.lt_of_lt_of_le can
    ((Nat.le_trans (ranges d d.isLt).1) (Nat.pow_le_pow_right (by decide) (child_width d pos d.isLt)))
  have z : x.2 >>> 48 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt small]
  have table : ∀ i : Fin 25, 0 < i.val → childMask i true >>> 48 = tag i := by decide
  change (x.2 ||| childMask d true) >>> 48 = _
  rw [BitVec.ushiftRight_or_distrib, z, BitVec.zero_or, table d pos]

theorem right_tag_injective (a b : Fin 25) (ha : 0 < a.val) (hb : 0 < b.val)
    (x y : Digest) (cx : Canonical a x) (cy : Canonical b y)
    (equal : marked a true x = marked b true y) : a = b := by
  have h := congrArg (fun w : Digest => w.2 >>> 48) equal
  change (marked a true x).2 >>> 48 = (marked b true y).2 >>> 48 at h
  rw [marked_tag a ha x cx, marked_tag b hb y cy] at h
  have table : ∀ i j : Fin 25, tag i = tag j → i = j := by decide
  exact table a b h

theorem marked_right_nonzero (d : Fin 25) (pos : 0 < d.val) (x : Digest) :
    (marked d true x).2 ≠ 0 := by
  have nonzero : ∀ i : Fin 25, 0 < i.val → childMask i true ≠ 0#64 := by decide
  intro h
  change x.2 ||| childMask d true = 0#64 at h
  exact nonzero d pos (BitVec.or_eq_zero_iff.mp h).2

end CommitGolfCandidate.Reconstruction.Binding
