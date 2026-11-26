import CommitGolfCandidate.Stage3cDomains
namespace CommitGolfCandidate.Chained
open CommitGolf
set_option exponentiation.threshold 800

/-- Physical level one is the first level above the leaves. -/
def workClass (height : Height) : Height :=
  if 8≤height.val ∧ height.val<16 then height else ⟨0,by decide⟩

def wireWidth (height : Height) : Nat :=
  if 8≤height.val ∧ height.val<16 then width height
  else if height.val=0 ∨ height.val=23 then 256 else if height.val<5 then 240 else 238

theorem projected_width : ∀ h, width (workClass h)≤wireWidth h := by decide +kernel
theorem workClass_calls : ∀ h, calls (workClass h)=calls h := by decide +kernel
theorem plain_class_iff (h : Height) :
    workClass h=⟨0,by decide⟩ ↔ h.val<8 ∨ 16≤h.val := by
  exact (by decide +kernel : ∀ k : Height, workClass k=⟨0,by decide⟩ ↔ k.val<8 ∨ 16≤k.val) h

def parentQueries (H : Compression) (h : Height) (left right : Output) : Nat → List Input
  | 0 => [pack (.inl (workClass h, right ++ left))]
  | j+1 =>
    let previous:=parentQueries H h left right j
    previous ++ [encodeNext (workClass h) (j+1) (H (previous.getLastD 0))]

def queries (H : Compression) (h : Height) (left right : Output) : List Input :=
  parentQueries H h left right (calls h-1)

theorem prefix_length (H : Compression) (h : Height) (l r : Output) (n : Nat) :
    (parentQueries H h l r n).length = n+1 := by
  induction n with
  | zero => rfl
  | succ k ih => simp [parentQueries,ih]

theorem calls_positive : ∀ h, 0<calls h := by decide +kernel
theorem queries_length (H : Compression) (h : Height) (l r : Output) :
    (queries H h l r).length=calls h := by
  rw [queries,prefix_length];have :=calls_positive h;omega

def storeReply (h : Height) (v : Output) : Output :=
  BitVec.ofNat 256 (v.toNat % 2^(wireWidth h))

def parentDigest (H : Compression) (h : Height) (l r : Output) : Output :=
  storeReply h (H ((queries H h l r).getLastD 0))

theorem same_final_projection (h : Height) (v w : Output)
    (eqn : storeReply h v=storeReply h w) :
    v.toNat%2^(width (workClass h))=w.toNat%2^(width (workClass h)) := by
  have wh : wireWidth h≤256 := (by decide +kernel : ∀ j, wireWidth j≤256) h
  have dvd : 2^(width (workClass h)) ∣ 2^(wireWidth h) :=
    Nat.pow_dvd_pow 2 (projected_width h)
  have eq:=congrArg BitVec.toNat eqn
  simp only [storeReply,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
      (Nat.pow_le_pow_right (by decide : 0<2) wh))] at eq
  calc
    _ = (v.toNat % 2^(wireWidth h)) % 2^(width (workClass h)) := (Nat.mod_mod_of_dvd _ dvd).symm
    _ = (w.toNat % 2^(wireWidth h)) % 2^(width (workClass h)) := congrArg (fun x => x%2^(width (workClass h))) eq
    _ = _ := Nat.mod_mod_of_dvd _ dvd
end CommitGolfCandidate.Chained

namespace CommitGolfCandidate.Chained
open CommitGolf

theorem parent_witness (H : Compression) (h : Height) (l r l' r' : Output)
    (different : (l,r)≠(l',r'))
    (merged : parentDigest H h l r=parentDigest H h l' r') :
    ((r ++ l : Seed) ≠ r' ++ l') ∧
      (H ((queries H h l r).getLastD 0)).toNat%2^(width (workClass h)) =
      (H ((queries H h l' r').getLastD 0)).toNat%2^(width (workClass h)) := by
  refine ⟨?_,same_final_projection h _ _ merged⟩
  intro equal
  have bottom:=congrArg (BitVec.extractLsb' 0 256) equal
  have top:=congrArg (BitVec.extractLsb' 256 256) equal
  apply different
  exact Prod.ext (by simpa only [BitVec.extractLsb'_append_eq_right] using bottom) (by simpa only [BitVec.extractLsb'_append_eq_left] using top)
end CommitGolfCandidate.Chained
