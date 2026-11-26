import CommitGolfCandidate.ReconstructedCheckHonestCapPatch

namespace CommitGolfCandidate.Reconstruction.CheckHonestCapHeaders
open CommitGolf RiscvZkvm.Rv64 Wire Encoding CheckHonestCapLow CheckHonestCapPatch
open TwoPermutationPrototype TwoPermutationPrototype.RV64 CapSchedule
open CheckGroupWalk (patch)
open CheckGroupPlan (decode)
set_option maxRecDepth 15000
set_option maxHeartbeats 1300000

theorem run (t : Encoding.Tree) (d : Nat) (w : lows d=224) (bound : ∀ j,digit t d j<211) (xs : List Nat)
    (no : xs.Nodup) (a b : List Field) (s : Nat) (stream : s=pack (a++(capHeaders (digit t d) xs++b)))
    (m : Memory) (lower : ∀ j∈xs,Low m t d j) :
    let out := decode m xs s (bits a)
    out.valid=true ∧ (∀ j∈xs,Full out.data t d j) ∧ (∀ j, j∉xs → Equal out.data m j) := by
  by_cases empty : xs=[]
  · subst xs;rw [CheckGroupPlan.nil];refine ⟨rfl,?_,fun _ _ _ _ => rfl⟩
    intro j h;cases h
  let part := xs.take 4
  let rest := xs.drop 4
  let value := headerValue (digit t d) part
  let field : Field := ⟨value,31⟩
  let next := a++[field]
  let mem := patch m part value
  have splitList : part++rest=xs := List.take_append_drop 4 xs
  have disjoint := List.nodup_append.mp (show (part++rest).Nodup from splitList.symm ▸ no)
  have member (j : Nat) : j∈xs ↔ j∈part ∨ j∈rest := by rw [←splitList,List.mem_append]
  have frees (j : Nat) (h : j∈rest) : j∉part := fun l => disjoint.2.2 j l j h rfl
  have hpart (j : Nat) (h : j∈part) : j∉rest := fun l => disjoint.2.2 j h j l rfl
  have digits := CapDigits.decode (digit t d) part bound
  have small : value<2^31 := by
    have len : part.length≤4 := by simp [part]
    exact (CapDigits.header_lt (digit t d) part bound).trans_le
      ((Nat.pow_le_pow_right (n:=211) (by decide) len).trans (by decide : 211^4≤2^31))
  have layout := CapSchedule.header_step (digit t d) xs empty
  have src : s=pack (a++field::(capHeaders (digit t d) rest++b)) := by rw [stream,layout];rfl
  have val : HonestStream.get s (bits a) 31=value := by
    rw [src];exact (field_read a _ field (by change 31≤64;decide)).trans (Nat.mod_eq_of_lt small)
  have continueAt : s=pack (next++(capHeaders (digit t d) rest++b)) := by rw [src];simp [next,List.append_assoc]
  have nextBits : bits next=bits a+31 := by rw [show next=a++[field] from rfl,bits_append];rfl
  have finished : ∀ j∈part,Full mem t d j := patchFull t d w bound m part disjoint.1
    (fun j hj => lower j ((member j).2 (Or.inl hj)))
  have lowRest (j : Nat) (hj : j∈rest) : Low mem t d j :=
    low_eq (patchOther m part value j (frees j hj)) t d (lower j ((member j).2 (Or.inr hj)))
  have sub := run t d w bound rest disjoint.2.1 next b s continueAt mem lowRest
  rw [CheckGroupPlan.cons m xs s (bits a) empty]
  dsimp only
  rw [val,show (CapDigits.extract (xs.take 4).length value).2=0 from congrArg Prod.snd digits,ite_eq_left (rfl : (0:Nat)=0),←nextBits]
  refine ⟨sub.1,?_,?_⟩
  · intro j hj
    rcases (member j).1 hj with head|tail
    · exact full_eq (sub.2.2 j (hpart j head)) t d (finished j head)
    · exact sub.2.1 j tail
  · intro j absent k hk
    have tail : j∉rest := fun h => absent ((member j).2 (Or.inr h))
    have head : j∉part := fun h => absent ((member j).2 (Or.inl h))
    exact (sub.2.2 j tail k hk).trans (patchOther m part value j head k hk)
termination_by xs.length
decreasing_by
  have pos := List.length_pos_iff.mpr empty
  change (xs.drop 4).length<xs.length;rw [List.length_drop];omega

end CommitGolfCandidate.Reconstruction.CheckHonestCapHeaders
