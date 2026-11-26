import CommitGolfCandidate.ReconstructedCheckCapRepair
import CommitGolfCandidate.ReconstructedCheckEdge

namespace CommitGolfCandidate.Reconstruction.CheckCapAcceptedData
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckCapLowMemory CheckCapLowItem CheckCapLowStore
open CheckGroupWalk CheckGroupPlan CheckGroupRadix
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
set_option maxHeartbeats 1300000

theorem low_frame (m : Memory) (xs : List Nat) (stream c w q : Nat)
    (fresh : ∀ id∈xs,∀ k : Fin 4,q≠cell id+k.val) : fill stream w xs c m q=m q := by
  induction xs generalizing m c with
  | nil=>rfl
  | cons a xs ih=>
    rw [fill,ih _ _ (fun i hi=>fresh i (List.mem_cons_of_mem _ hi))]
    have f:=fresh a List.mem_cons_self
    have f0 : q≠cell a:=f 0
    have f1 : q≠cell a+1:=f 1
    have f2 : q≠cell a+2:=f 2
    have f3 : q≠cell a+3:=f 3
    simp only [data,copy,writeWord,ite_eq_right f0,ite_eq_right f1,ite_eq_right f2,ite_eq_right f3]

private theorem separate (a b k : Nat) (different : a≠b) (small : k<4) : top a≠cell b+k := by
  change 524288+4*a+3≠524288+4*b+k;omega

theorem low_top (m : Memory) (xs : List Nat) (stream c w id : Nat) (member : id∈xs) :
    (fill stream w xs c m (top id)).toNat<2^(w-192) := by
  induction xs generalizing m c with
  | nil=>cases member
  | cons a xs ih=>
    rw [fill]
    by_cases later : id∈xs
    · exact ih _ _ later
    · have eq:=List.mem_cons.mp member |>.resolve_right later
      subst a
      rw [low_frame _ xs _ _ _ _ (fun z hz k=>separate id z k (fun eq=>later (eq ▸ hz)) k.isLt)]
      change (copy m (cell id) _ _ _ (W (HonestStream.get stream (c+192) (w-192))) (cell id+3)).toNat<_
      simp only [copy,writeWord,ite_true,BitVec.toNat_ofNat]
      apply Nat.lt_of_le_of_lt (Nat.mod_le ..)
      unfold HonestStream.get
      exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem patch_away (m : Memory) (xs : List Nat) (v id : Nat) (notIn : id∉xs) : patch m xs v (top id)=m (top id) := by
  induction xs generalizing m v with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.mem_cons,not_or] at notIn
    exact (ih _ _ notIn.2).trans (unaffected _ _ _ _ (by unfold top cap;omega))

theorem patch_digit (m : Memory) (xs : List Nat) (v id : Nat) (unique : xs.Nodup) :
    ∃ z<211,patch m xs v (top id)=m (top id) ||| (W z <<< (32:Nat)) := by
  induction xs generalizing m v with
  | nil=>exact ⟨0,by decide,(BitVec.or_zero ..).symm⟩
  | cons a xs ih=>
    obtain ⟨fresh,distinct⟩:=List.nodup_cons.mp unique
    by_cases here : id=a
    · subst a
      refine ⟨v%211,Nat.mod_lt _ (by decide),?_⟩
      rw [patch,patch_away _ _ _ _ fresh];simp [fix,writeWord]
    · obtain ⟨z,lt,done⟩:=ih (fix m a (v%211)) (v/211) distinct
      rw [unaffected m a _ (top id) (by unfold top cap;omega)] at done
      exact ⟨z,lt,done⟩

theorem decode_digit (m : Memory) (xs : List Nat) (stream c id : Nat) (unique : xs.Nodup)
    (valid : (decode m xs stream c).valid=true) :
    ∃ z<211,(decode m xs stream c).data (top id)=m (top id) ||| (W z <<< (32:Nat)) := by
  by_cases empty : xs=[]
  · subst xs;rw [nil];exact ⟨0,by decide,(BitVec.or_zero ..).symm⟩
  · rw [cons _ _ _ _ empty] at valid ⊢
    dsimp only at valid ⊢
    split
    · rename_i ok
      rw [ite_eq_left ok] at valid
      let v:=HonestStream.get stream c 31
      let u:=patch m (xs.take 4) v
      by_cases head : id∈xs.take 4
      · have distinct : (xs.take 4++xs.drop 4).Nodup:=by simpa using unique
        have disjoint:=List.disjoint_of_nodup_append distinct
        have tail : id∉xs.drop 4 := fun h=>List.disjoint_left.mp disjoint head h
        rw [CheckCapRepair.decode_frame u (xs.drop 4) stream (c+31) (top id) (fun j hj eq=>by
          have num : id=j:=by unfold top cap at eq;omega
          exact tail (num ▸ hj))]
        exact patch_digit m (xs.take 4) v id unique.take
      · obtain ⟨z,lt,step⟩:=decode_digit u (xs.drop 4) stream (c+31) id unique.drop valid
        have prior : u (top id)=m (top id):=patch_away _ _ _ _ head
        rw [prior] at step;exact ⟨z,lt,step⟩
    · rename_i error;rw [ite_eq_right error] at valid;cases valid
termination_by xs.length
decreasing_by have h:=List.length_pos_iff.mpr empty;simp;omega

end CommitGolfCandidate.Reconstruction.CheckCapAcceptedData
