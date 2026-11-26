import CommitGolfCandidate.Stage3cParent
import CommitGolf.Riscv
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

theorem projected_bit (d : Height) (v : Output) (b : Nat) (inside : b<256) :
    (storeReply d v).getLsbD b=(decide (b<wireWidth d) && v.getLsbD b) := by
  simp only [storeReply,BitVec.getLsbD_ofNat,inside,decide_true,Bool.true_and,Nat.testBit_mod_two_pow]
  rfl

def heldMask (d : Height) : Word := BitVec.ofNat 64 (2^(wireWidth d-224)-1)
def keptHalf (v m : Word) : BitVec 32 := (((extractHalfword v 2).zeroExtend 64) &&& m).truncate 32

private theorem last_circuit (v m : Word) : replaceWord32 v 1 (keptHalf v m) =
    v &&& (((m &&& 65535#64) <<< 32) ||| 4294967295#64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceWord32,keptHalf,extractHalfword,BitVec.getLsbD_and,BitVec.getLsbD_or,
    BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_setWidth]
  interval_cases i <;> simp [Bool.and_comm,Bool.and_assoc]

private theorem mask_numeric (d : Height) (low : 224≤wireWidth d) (upper : wireWidth d≤240) :
    ((heldMask d &&& 65535#64) <<< 32) ||| 4294967295#64 =
      BitVec.ofNat 64 (2^(wireWidth d-192)-1) := by
  have checked : ∀ j : Fin 17,
      ((BitVec.ofNat 64 (2^j.val-1) &&& 65535#64) <<< 32) ||| 4294967295#64 =
      BitVec.ofNat 64 (2^(32+j.val)-1) := by decide +kernel
  exact (checked ⟨wireWidth d-224,by omega⟩).trans (congrArg (fun n=>BitVec.ofNat 64 (2^n-1)) (by dsimp;omega))

theorem last_projection (d : Height) (v : Output) (low : 224≤wireWidth d) (upper : wireWidth d≤240) :
    replaceWord32 (v.extractLsb' 192 64) 1 (keptHalf (v.extractLsb' 192 64) (heldMask d))=
      (storeReply d v).extractLsb' 192 64 := by
  rw [last_circuit,mask_numeric d low upper]
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  have bound : 192+i<256:=by omega
  have same : (i<wireWidth d-192)↔192+i<wireWidth d:=by omega
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_extractLsb',BitVec.getLsbD_ofNat,hi,decide_true,Bool.true_and,
    Nat.testBit_two_pow_sub_one,projected_bit d v _ bound,same,Bool.and_comm]

theorem early_projection (d : Height) (v : Output) (low : 224≤wireWidth d) (j : Nat) (j3 : j<3) :
    v.extractLsb' (64*j) 64=(storeReply d v).extractLsb' (64*j) 64 := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  have small : 64*j+i<wireWidth d:=by omega
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,projected_bit d v (64*j+i) (by omega),small]

theorem full_projection (d : Height) (v : Output) (full : wireWidth d=256) : storeReply d v=v := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  rw [projected_bit d v i hi,full];simp only [hi,decide_true,Bool.true_and]
end CommitGolfCandidate.S5Machine
