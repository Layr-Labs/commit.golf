import CommitGolfCandidate.ReconstructedCheckHonestFields

namespace CommitGolfCandidate.Reconstruction.CheckHonestRadix
open CommitGolf Encoding HonestDivision RecordDigits CheckWalkValues
set_option maxRecDepth 14000
set_option maxHeartbeats 1300000

def high (t : Encoding.Tree) (idx : Index) (d : Nat) := highDigit (t d (sibling idx d)) (lows d)
def number (t : Encoding.Tree) (idx : Index) : Nat → Nat
  | 0 => 0
  | k+1 => number t idx k*base (10+k)+high t idx (10+k)

def rows (t : Encoding.Tree) (idx : Index) : Nat → List Wire.Field
  | 0 => []
  | k+1 => lowFields (t (10+k) (sibling idx (10+k))) (lows (10+k))++rows t idx k

theorem top (t : Encoding.Tree) (idx : Index) : number t idx 10=recordHeader t idx := rfl

private theorem radix (k : Nat) (h : k<15) :
    let i := CheckWalk.idx15 k
    CheckMixed.base i=base (10+k) ∧ 0<base (10+k) ∧ base (10+k)≤limb ∧
    CheckMixed.width i=lows (10+k) ∧ 192≤lows (10+k) ∧ lows (10+k)≤256 ∧ (10≤k → base (10+k)=1) := by
  let j : Fin 15 := ⟨k,h⟩
  exact (by decide : ∀ z : Fin 15,
    CheckMixed.base (CheckWalk.idx15 z.val)=base (10+z.val) ∧ 0<base (10+z.val) ∧ base (10+z.val)≤limb ∧
    CheckMixed.width (CheckWalk.idx15 z.val)=lows (10+z.val) ∧ 192≤lows (10+z.val) ∧ lows (10+z.val)≤256 ∧
    (10≤z.val → base (10+z.val)=1)) j

theorem width (k : Nat) (h : k<15) : CheckMixed.width (CheckWalk.idx15 k)=lows (10+k) ∧
    192≤lows (10+k) ∧ lows (10+k)≤256 :=
  ⟨(radix k h).2.2.2.1,(radix k h).2.2.2.2.1,(radix k h).2.2.2.2.2.1⟩

private theorem bound (t : Encoding.Tree) (ok : canonical t) (idx : Index) (k : Nat) (r : k<15) :
    high t idx (10+k)<base (10+k) := digit_bound t ok ⟨10+k,by omega⟩ (sibling idx (10+k))

private theorem unmixed (t : Encoding.Tree) (ok : canonical t) (idx : Index) (k : Nat) (a : 10≤k) (b : k<15) :
    number t idx (k+1)=number t idx k ∧ high t idx (10+k)=0 := by
  have q := (radix k b).2.2.2.2.2.2 a
  have r := bound t ok idx k b
  rw [q] at r
  have h : high t idx (10+k)=0 := by omega
  exact ⟨by rw [number,q,h,Nat.mul_one,Nat.add_zero],h⟩

theorem header (t : Encoding.Tree) (ok : canonical t) (idx : Index) : number t idx 15=recordHeader t idx :=
  (unmixed t ok idx 14 (by decide) (by decide)).1.trans
    ((unmixed t ok idx 13 (by decide) (by decide)).1.trans
      ((unmixed t ok idx 12 (by decide) (by decide)).1.trans
        ((unmixed t ok idx 11 (by decide) (by decide)).1.trans
          ((unmixed t ok idx 10 (by decide) (by decide)).1.trans (top t idx)))))

private theorem size (b r : Nat) (xs : List Nat) : (divide b r xs).1.length=xs.length ∧ bounded (divide b r xs).1 := by
  induction xs generalizing r with
  | nil => exact ⟨rfl,fun _ h => by cases h⟩
  | cons x xs ih =>
    let y := (r*limb+x)%b
    obtain ⟨n,small⟩ := ih y
    refine ⟨congrArg (·+1) n,?_⟩
    intro a ha
    change a∈_::(divide b y xs).1 at ha
    rcases List.mem_cons.mp ha with eq|h
    · subst a;exact Nat.mod_lt _ (by decide)
    · exact small a h

theorem splitHeader (t : Encoding.Tree) (ok : canonical t) (idx : Index) (k : Nat) (b : k<15) (xs : List Nat)
    (length : xs.length=4) (small : bounded xs) (num : HonestDivision.assemble 0 xs=number t idx (k+1)) :
    let p := CheckMixed.out (CheckWalk.idx15 k) xs
    p.1.length=4 ∧ bounded p.1 ∧ HonestDivision.assemble 0 p.1=number t idx k ∧ p.2=high t idx (10+k) := by
  have j : (CheckWalk.idx15 k).val=k := Nat.mod_eq_of_lt b
  have r := radix k b
  unfold CheckMixed.out
  rw [j]
  by_cases mixed : k<10
  · rw [ite_eq_left mixed,r.1]
    have v := divide_correct (base (10+k)) 0 xs r.2.1 r.2.2.1 small
    simp only [Nat.zero_mod,Nat.zero_div,num,number] at v
    have d := bound t ok idx k b
    have divEq : (number t idx k*base (10+k)+high t idx (10+k))/base (10+k)=number t idx k := by
      rw [Nat.add_comm,Nat.mul_comm,Nat.add_mul_div_left _ _ r.2.1,Nat.div_eq_of_lt d,Nat.zero_add]
    have modEq : (number t idx k*base (10+k)+high t idx (10+k))%base (10+k)=high t idx (10+k) := by
      rw [Nat.add_comm,Nat.mul_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt d]
    have shape := size (base (10+k)) 0 xs
    exact ⟨shape.1.trans length,shape.2,v.1.trans divEq,v.2.trans modEq⟩
  · rw [ite_eq_right mixed]
    have h := unmixed t ok idx k (by omega) b
    exact ⟨length,small,num.trans h.1,h.2.symm⟩

theorem zero (xs : List Nat) (h : xs.length=4) (z : HonestDivision.assemble 0 xs=0) : xs=[0,0,0,0] := by
  rcases xs with _|⟨a,xs⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  rcases xs with _|⟨b,xs⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  rcases xs with _|⟨c,xs⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  rcases xs with _|⟨d,xs⟩ <;> simp only [List.length_nil,List.length_cons] at h
  · omega
  have empty : xs=[] := List.length_eq_zero_iff.mp (by omega)
  subst xs
  simp only [HonestDivision.assemble,limb,Nat.zero_mul,Nat.zero_add] at z
  simp only [List.cons.injEq,and_true];omega

end CommitGolfCandidate.Reconstruction.CheckHonestRadix
