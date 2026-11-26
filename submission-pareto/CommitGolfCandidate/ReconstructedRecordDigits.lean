import CommitGolfCandidate.ReconstructedLeafProjection
import CommitGolfCandidate.ReconstructedHonestDivision
import CommitGolfCandidate.ReconstructedWireBytes

namespace CommitGolfCandidate.Reconstruction.RecordDigits
open CommitGolf TwoPermutationPrototype.Sampling LeafTree Encoding Wire

set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

abbrev Depth := Fin 25
def ordered : List Depth := [19,18,17,16,15,14,13,12,11,10]
def canonical (t : Encoding.Tree) := ∀ d : Depth, ∀ j, Binding.Canonical d (t d j)

theorem radices (d : Depth) : Binding.radix d.val = base d.val * 2^(lows d.val-192) := by
  exact (by decide : ∀ j : Depth, Binding.radix j.val=base j.val * 2^(lows j.val-192)) d

theorem digit_bound (t : Encoding.Tree) (good : canonical t) (d : Depth) (j : Nat) :
    highDigit (t d j) (lows d) < base d := by
  have h : (t d j).2.toNat < Binding.radix d.val := good d j
  have h' : (t d j).2.toNat < base d.val * 2^(lows d.val-192) := h.trans_eq (radices d)
  unfold highDigit
  rw [Nat.shiftRight_eq_div_pow]
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (lows d.val-192))).2 h' 

def ds (t : Encoding.Tree) (good : canonical t) (i : Index) : (depths : List Depth) → Digits (depths.map (fun d => base d))
  | [] => .nil
  | d::tail => .cons ⟨highDigit (t d (sibling i d)) (lows d),digit_bound t good d _⟩ (ds t good i tail)

def forward (t : Encoding.Tree) (i : Index) (h : Nat) (d : Depth) :=
  h*base d+highDigit (t d (sibling i d)) (lows d)

private theorem pack_fold (t : Encoding.Tree) (g : canonical t) (i : Index) (xs : List Depth) (h : Nat) :
    xs.reverse.foldl (forward t i) h =
        (ds t g i xs).pack.val + (xs.map fun d => base d).prod*h := by
  induction xs with
  | nil => simp [ds,Digits.pack]
  | cons d xs ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,forward,ds,
      Digits.pack,List.map_cons,List.prod_cons,Nat.add_mul]
    ac_rfl

theorem order : ordered.map (fun j => base j)=sameSize.recordBases := by decide

def digits (t : Encoding.Tree) (g : canonical t) (i : Index) : Digits sameSize.recordBases := ds t g i ordered

theorem record_value (t : Encoding.Tree) (g : canonical t) (i : Index) :
    recordHeader t i = (lowerHeader (digits t g i)).val := by
  have p := pack_fold t g i ordered 0
  rw [Nat.mul_zero,Nat.add_zero] at p
  change _ = (digits t g i).pack.val
  exact p

/-- The 64+38 serialized header bits suffice for all ten digits and no bit is lost. -/
theorem header_bound (t : Encoding.Tree) (g : canonical t) (i : Index) : recordHeader t i<2^102 := by
  rw [record_value t g i]
  exact (lowerHeader _).isLt

attribute [local irreducible] recordHeader digits

theorem decode_header (t : Encoding.Tree) (g : canonical t) (i : Index) :
    let n := recordHeader t i
    let result := HonestDivision.extract sameSize.recordBases
      (HonestDivision.fromFields (n%2^64) ((n/2^64)%2^38))
    result.1=HonestDivision.digitList (digits t g i) ∧ HonestDivision.assemble 0 result.2=0 := by
  have bound := header_bound t g i
  have high : recordHeader t i/2^64 < 2^38 := (Nat.div_lt_iff_lt_mul (by decide : 0<2^64)).2 bound
  let P (lo hi : Nat) := let result := HonestDivision.extract sameSize.recordBases (HonestDivision.fromFields lo hi)
    result.1=HonestDivision.digitList (digits t g i) ∧ HonestDivision.assemble 0 result.2=0
  change P (recordHeader t i%2^64) (recordHeader t i/2^64%2^38)
  rw [Nat.mod_eq_of_lt high,record_value t g i]
  exact HonestDivision.record_roundtrip _

theorem ref_canonical (c : Compression) (leaves : DigestTape) : canonical (reference c leaves) := by
  intro d j
  apply CommitParents.node_canonical (compress c) (projected leaves) d j (by have := d.isLt;omega)
  exact fun n => Binding.canonical_project 24 _

end CommitGolfCandidate.Reconstruction.RecordDigits
