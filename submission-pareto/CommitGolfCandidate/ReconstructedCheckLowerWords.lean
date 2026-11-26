import CommitGolfCandidate.ReconstructedCheckStream
import CommitGolfCandidate.ReconstructedCheckLowerLayout

namespace CommitGolfCandidate.Reconstruction.CheckLowerWords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckHeaderPlan
set_option maxRecDepth 13000
set_option maxHeartbeats 1250000

private theorem middle (env : Env) (r : Fin 64) (j : Nat) :
    (CheckLowerPlan.middle r j).val env=(field (r.val+64*j) 64).val env := by
  have hi:=r.isLt
  have off : (r.val+64*j)%64=r.val := by omega
  have index : (r.val+64*j)/64=j := by omega
  unfold CheckLowerPlan.middle field
  simp only [off,index]
  by_cases z : r.val=0
  · simp [z,CheckHeaderPlan.shift]
  · have spill : 64<r.val+64 := by omega
    have complement : 64-r.val<64 := by omega
    have remaining : 63-r.val<64 := by omega
    simp only [z,ite_false,spill,ite_true,Term.val,Bin.run,CheckField.left,CheckField.right,
      Nat.mod_eq_of_lt complement,Nat.mod_eq_of_lt remaining,Nat.mod_eq_of_lt hi,
      show 1%64=1 by decide,←BitVec.shiftLeft_add,show 1+(63-r.val)=64-r.val by omega]

theorem low (env : Env) (stream q : Nat) (r : Fin 64) (source : CheckField.Source env stream q) :
    ((field r 64).val env).toNat=HonestStream.get stream (64*q+r.val) 64 := by
  have h:=CheckField.bits env stream q r 64 (by decide) (by have:=r.isLt;omega) (by have:=r.isLt;omega) source
  simpa only [Nat.mod_eq_of_lt (Term.val env (field r 64)).isLt] using h

theorem mid (env : Env) (stream q : Nat) (r : Fin 64) (j : Nat) (fit : j≤2) (source : CheckField.Source env stream q) :
    ((CheckLowerPlan.middle r j).val env).toNat=HonestStream.get stream (64*q+r.val+64*j) 64 := by
  rw [middle,Nat.add_assoc]
  have h:=CheckField.bits env stream q (r.val+64*j) 64 (by decide) (by have:=r.isLt;omega) (by have:=r.isLt;omega) source
  simpa only [Nat.mod_eq_of_lt (Term.val env (field (r.val+64*j) 64)).isLt] using h

theorem high (env : Env) (stream q : Nat) (r : Fin 64) (w : Nat) (fit : 192≤w ∧ w≤240) (source : CheckField.Source env stream q) :
    ((CheckLowerPlan.top r w).val env).toNat=HonestStream.get stream (64*q+r.val+192) (w-192) := by
  unfold CheckLowerPlan.top
  simp only [Term.val,Bin.run,BitVec.toNat_and,BitVec.toNat_ofNat]
  have high : 2^(w-192)≤2^48:=Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt (by omega : 2^(w-192)-1<2^64),Nat.and_two_pow_sub_one_eq_mod,Nat.add_assoc]
  exact CheckField.bits env stream q (r.val+192) (w-192) (by omega) (by have:=r.isLt;omega) (by have:=r.isLt;omega) source

end CommitGolfCandidate.Reconstruction.CheckLowerWords
