import CommitGolfCandidate.ReconstructedCheckCapLowMemory
import CommitGolfCandidate.ReconstructedCheckCapHeaders

namespace CommitGolfCandidate.Reconstruction.CheckCapRepair
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CheckGroupPlan CheckGroupWalk
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 17000
set_option maxHeartbeats 1300000

structure Same (a b : Result) : Prop where
  success : a.valid=b.valid
  position : a.cursor=b.cursor
  data : LeafMemory.Agrees a.data b.data

theorem decode_congr (m n : Memory) (xs : List Nat) (stream c : Nat) (h : LeafMemory.Agrees m n) :
    Same (decode m xs stream c) (decode n xs stream c) := by
  by_cases z : xs=[]
  · subst xs;rw [nil,nil];exact ⟨rfl,rfl,h⟩
  · rw [cons _ _ _ _ z,cons _ _ _ _ z]
    dsimp only
    have agree:=congruence m n (xs.take 4) (HonestStream.get stream c 31) h
    split
    · exact decode_congr _ _ (xs.drop 4) _ _ agree
    · exact ⟨rfl,rfl,agree⟩
termination_by xs.length
decreasing_by have k:=List.length_pos_iff.mpr z;simp;omega

theorem result_congr (d : Nat) (m n : Memory) (xs : List Nat) (stream c : Nat) (same : LeafMemory.Agrees m n) :
    Same (CheckCapHeaders.result d m xs stream c) (CheckCapHeaders.result d n xs stream c) := by
  unfold CheckCapHeaders.result;split
  · exact ⟨rfl,rfl,same⟩
  · exact decode_congr _ _ _ _ _ same

theorem decode_frame (m : Memory) (xs : List Nat) (stream c q : Nat) (other : ∀ id∈xs,q≠CheckGroupRadix.top id) :
    (decode m xs stream c).data q=m q := by
  by_cases empty : xs=[]
  · subst xs;rw [nil]
  · rw [cons _ _ _ _ empty];dsimp only
    have p (m : Memory) (ys : List Nat) (v : Nat) (apart : ∀ id∈ys,q≠CheckGroupRadix.top id) : patch m ys v q=m q := by
      induction ys generalizing m v with
      | nil=>rfl
      | cons a ys ih=>exact (ih _ _ (fun id h=>apart _ (List.mem_cons_of_mem _ h))).trans (unaffected _ _ _ _ (apart _ List.mem_cons_self))
    have sofar:=p m (xs.take 4) (HonestStream.get stream c 31) (fun id h=>other _ (List.mem_of_mem_take h))
    split
    · exact (decode_frame _ (xs.drop 4) _ _ q (fun id h=>other _ (List.mem_of_mem_drop h))).trans sofar
    · exact sofar
termination_by xs.length
decreasing_by have k:=List.length_pos_iff.mpr empty;simp;omega

theorem result_frame (d : Nat) (m : Memory) (xs : List Nat) (stream c q : Nat)
    (other : ∀ id∈xs,q≠CheckGroupRadix.top id) : (CheckCapHeaders.result d m xs stream c).data q=m q := by
  unfold CheckCapHeaders.result;split
  · rfl
  · exact decode_frame _ _ _ _ _ other

def result (d w : Nat) (m : Memory) (xs : List Nat) (stream c : Nat) :=
  CheckCapHeaders.result d (CheckCapLowMemory.fill stream w xs c m) xs stream (c+w*xs.length)

theorem nil_result (d w : Nat) (m : Memory) (stream c : Nat) : result d w m [] stream c=⟨true,c,m⟩ := by
  simp only [result,CheckCapHeaders.result,CheckCapLowMemory.fill,List.length_nil,Nat.mul_zero,Nat.add_zero,nil,ite_self]

theorem width (d : Nat) (pos : 0<d) (small : d≤9) : Encoding.lows d=224 ∨ Encoding.lows d=240 := by
  let i : Fin 9:=⟨d-1,by omega⟩
  have h:=(by decide : ∀ j : Fin 9, Encoding.lows (j.val+1)=224 ∨ Encoding.lows (j.val+1)=240) i
  rwa [show i.val+1=d by dsimp [i];omega] at h

end CommitGolfCandidate.Reconstruction.CheckCapRepair
