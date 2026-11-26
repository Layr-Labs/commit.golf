import CommitGolfCandidate.ReconstructedCheckCapIterate
import CommitGolfCandidate.ReconstructedCheckWalkValues

namespace CommitGolfCandidate.Reconstruction.CheckCapPaths
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckCapIterate CheckCapLevel CheckWalkValues
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 15000
set_option maxHeartbeats 950000

theorem heap_zero (idx : Index) : heap idx 0=1 := by
  have bound : idx.val<2^24:=idx.isLt
  change (16777216+idx.val)/16777216=1
  omega

theorem child (idx : Index) (k : Nat) (dep : k<24) :
    heap idx (k+1)=2*heap idx k+(side idx (k+1)).toNat := by
  let n:=heap idx (k+1)
  have half : n/2=heap idx k := by
    unfold n heap;rw [Nat.div_div_eq_div_mul,←Nat.pow_succ,show (24-(k+1)).succ=24-k by omega]
  have bit : side idx (k+1)=n.testBit 0 := by
    unfold side n heap
    rw [Nat.testBit_div_two_pow,Nat.zero_add,Nat.testBit_two_pow_add_gt (by omega : 24-(k+1)<24)]
  have test : n.testBit 0=decide (n%2=1) := by rw [Nat.testBit_eq_decide_div_mod_eq];simp
  change n=_
  rw [bit,test]
  rcases Nat.mod_two_eq_zero_or_one n with a|b
  · simp only [decide_eq_false (by omega : ¬n%2=1),Bool.toNat_false];omega
  · simp only [decide_eq_true b,Bool.toNat_true];omega

theorem range (idx : Index) (k : Nat) (small : k≤24) :
    2^k≤heap idx k ∧ heap idx k<2^(k+1) := by
  induction k with
  | zero=>rw [heap_zero];decide
  | succ k ih=>
    obtain ⟨lo,hi⟩:=ih (by omega)
    have b : (side idx (k+1)).toNat≤1:=by cases side idx (k+1) <;> decide
    rw [child idx k (by omega),Nat.pow_succ 2 (k+1),Nat.pow_succ 2 k] at *
    omega

theorem active (f : Nat→Bool) (idx : Index) (k : Nat) (small : k<9)
    (live : Live f (k+1) (heap idx (k+1))=true) : Live f k (heap idx k)=true := by
  have lo:=(range idx k (by omega)).1
  have eq : heap idx (k+1)-2^(k+1)=2*(heap idx k-2^k)+(side idx (k+1)).toNat:=by
    rw [child idx k (by omega),Nat.pow_succ];omega
  unfold Live at *
  rw [eq] at live
  rw [show 9-k=(9-(k+1))+1 by omega,HonestSizeSchedule.row]
  cases h : side idx (k+1) <;> simp_all only [Bool.toNat_false,Bool.toNat_true,Nat.add_zero,Bool.true_or,Bool.or_true]

theorem direction (idx : Index) (k : Nat) (dep : k<24) :
    side idx (k+1)::CheckPath.dirs idx k=CheckPath.dirs idx (k+1) := by
  unfold CheckPath.dirs side
  rw [List.range'_succ,List.map_cons,show 24-(k+1)+1=24-k by omega]

def Sound (o : Oracle) (f : Nat→Bool) (d : Nat) (s t : MachineState) (log : List PublicRow) (out : Option Nat) :=
  ∀ ⦃c⦄,out=some c→d≤9→∀ (idx : Index),Live f d (heap idx d)=true→
    ∀ all : List PublicRow,log⊆all→Binding.Path (history all) (oracleCompression o) d (CheckPath.dirs idx d)
      (node t 1) (node s (heap idx d))

theorem paths {o f stream d c s out t log} (tr : Trail o f stream d c s out t log) :
    Sound o f d s t log out := by
  induction tr with
  | finish c s b=>
    intro _ _ _ idx _ _ _;rw [heap_zero];exact Binding.Path.root _
  | stopped k c s t log m base bad halt=>intro _ h;cases h
  | level k c s u t log tail m out base good rest ih=>
    intro endC ending small idx live all included
    have dep : k<24:=by omega
    have below:=range idx k (by omega)
    have liveParent:=active f idx k (by omega) live
    have parentPath:=ih ending (by omega) idx liveParent all (fun _ a=>included (List.mem_append_right _ a))
    rw [child idx k dep] at live ⊢
    obtain ⟨edge⟩:=good.edges _ below.1 below.2 (side idx (k+1)) live
    let fullEdge : CheckPath.Edge o all k (side idx (k+1)) (node s (2*heap idx k+(side idx (k+1)).toNat))
        (node u (heap idx k)) := { edge with observed := fun _ h=>included (List.mem_append_left _ (edge.observed h)) }
    rw [←direction idx k dep]
    exact fullEdge.extend parentPath

end CommitGolfCandidate.Reconstruction.CheckCapPaths

