import CommitGolfCandidate.ReconstructedCheckGroupWalk
import CommitGolfCandidate.ReconstructedCheckGroupRead
import CommitGolfCandidate.ReconstructedCapSchedule

namespace CommitGolfCandidate.Reconstruction.CheckGroupPlan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckGroupRadix CheckGroupWalk CheckStream
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 13000
set_option maxHeartbeats 1400000

structure Result where
  valid : Bool
  cursor : Nat
  data : Memory

def decode (m : Memory) (xs : List Nat) (stream c : Nat) : Result :=
  if h : xs=[] then ⟨true,c,m⟩ else
    let v:=HonestStream.get stream c 31
    let sub:=xs.take 4
    let changed:=patch m sub v
    if (CapDigits.extract sub.length v).2=0 then decode changed (xs.drop 4) stream (c+31)
    else ⟨false,c+31,changed⟩
termination_by xs.length
decreasing_by have non : 0<xs.length := List.length_pos_iff.mpr h;simp;omega

theorem nil (m : Memory) (stream c : Nat) : decode m [] stream c=⟨true,c,m⟩ := by rw [decode, dite_eq_left rfl]
theorem cons (m : Memory) (xs : List Nat) (stream c : Nat) (non : xs≠[]) :
    decode m xs stream c=
      let v:=HonestStream.get stream c 31
      let sub:=xs.take 4
      let changed:=patch m sub v
      if (CapDigits.extract sub.length v).2=0 then decode changed (xs.drop 4) stream (c+31)
      else ⟨false,c+31,changed⟩ := by rw [decode,dite_eq_right non]

def groups (xs : List Nat) := (xs.length+3)/4

theorem cursor (m : Memory) (xs : List Nat) (stream c : Nat) (pass : (decode m xs stream c).valid=true) :
    (decode m xs stream c).cursor=c+31*groups xs := by
  by_cases zero : xs=[]
  · subst xs;rw [nil];rfl
  rw [cons _ _ _ _ zero] at pass ⊢
  dsimp only at pass ⊢
  split
  · rename_i good
    rw [ite_eq_left good] at pass
    rw [cursor _ _ _ _ pass]
    have pos:=List.length_pos_iff.mpr zero
    unfold groups;rw [List.length_drop];omega
  · rename_i bad
    rw [ite_eq_right bad] at pass
    cases pass
termination_by xs.length
decreasing_by have n:=List.length_pos_iff.mpr zero;simp;omega

theorem patch_frame (m : Memory) (xs : List Nat) (v i : Nat) (ids : ∀ a∈xs,a<1024) (away : (528384 ≤ i) ∨ (i < 524288)) :
    patch m xs v i=m i := by
  induction xs generalizing m v with
  | nil=>rfl
  | cons a xs ih=>
    have bound:=ids a List.mem_cons_self
    change patch (fix m a (v%211)) xs (v/211) i=_
    rw [ih _ _ (fun z hz=>ids z (List.mem_cons_of_mem _ hz)),unaffected _ _ _ _ (by unfold top cap;omega)]

theorem patch_honest (m : Memory) (xs : List Nat) (digit : Nat→Nat) (small : ∀ a,digit a<211) :
    patch m xs (Encoding.headerValue digit xs)=xs.foldl (fun mem id=>fix mem id (digit id)) m := by
  induction xs generalizing m with
  | nil=>rfl
  | cons a xs ih=>
    simp only [patch,Encoding.headerValue,List.foldl_cons,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (small a),
      Nat.add_mul_div_left _ _ (by decide : 0<211),Nat.div_eq_of_lt (small a),Nat.zero_add,ih]

theorem patch_safe (xs : List Nat) (digit : Nat→Nat) (small : ∀ a,digit a<211) :
    (CapDigits.extract xs.length (Encoding.headerValue digit xs)).2=0 := by rw [CapDigits.decode _ _ small]

end CommitGolfCandidate.Reconstruction.CheckGroupPlan

