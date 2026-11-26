import CommitGolfCandidate.ReconstructedCheckHeaderPlan
import CommitGolfCandidate.ReconstructedHonestStream

namespace CommitGolfCandidate.Reconstruction.CheckField
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckHeaderPlan
set_option maxRecDepth 12000
set_option maxHeartbeats 1100000

def Source (env : Env) (stream q : Nat) := ∀ i<5,
  (word i).val env=BitVec.ofNat 64 (HonestStream.word stream (q+i))

theorem right (env : Env) (x : Term) (n : Nat) : (CheckHeaderPlan.shift false x n).val env=x.val env >>> (n%64) := by
  by_cases eq : n%64=0
  · simp [CheckHeaderPlan.shift,eq]
  · have ord : (BitVec.ofNat 64 (n%64)).toNat%64=n%64 := by simp only [BitVec.toNat_ofNat];omega
    simp [CheckHeaderPlan.shift,eq,Term.val,Bin.run,ord]

theorem left (env : Env) (x : Term) (n : Nat) : (CheckHeaderPlan.shift true x n).val env=x.val env <<< (n%64) := by
  by_cases eq : n%64=0
  · simp [CheckHeaderPlan.shift,eq]
  · have ord : (BitVec.ofNat 64 (n%64)).toNat%64=n%64 := by simp only [BitVec.toNat_ofNat];omega
    simp [CheckHeaderPlan.shift,eq,Term.val,Bin.run,ord]

theorem bits (env : Env) (stream q cursor width : Nat) (wide : width≤64) (endAt : cursor+width≤320)
    (start : cursor<320) (src : Source env stream q) :
    ((field cursor width).val env).toNat%2^width=HonestStream.get stream (64*q+cursor) width := by
  let k:=cursor/64;let r:=cursor%64
  have off : (64*q+cursor)%64=r := by dsimp [r];omega
  have idx : (64*q+cursor)/64=q+k := by dsimp [k];omega
  have full (i : Nat) : HonestStream.word stream i<2^64 := Nat.mod_lt _ (by decide)
  have klt : k<5 := by dsimp [k];omega
  unfold field HonestStream.get
  simp only [off,idx]
  change ((if 64<r+width then Term.bin Bin.bitOr (CheckHeaderPlan.shift true (word (k+1)) (64-r)) (CheckHeaderPlan.shift false (word k) r)
    else CheckHeaderPlan.shift false (word k) r).val env).toNat % 2^width = _
  by_cases spill : 64<r+width
  · have next : k+1<5 := by dsimp [k,r] at *;omega
    have usable : 0<r ∧ r<64 := by dsimp [r] at *;omega
    have tails : 64-r<64 := by omega
    simp only [spill,ite_true,Term.val,Bin.run,left,right,src k klt,src (k+1) next,Nat.mod_eq_of_lt tails,
      Nat.mod_eq_of_lt usable.2,BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (full _),Nat.add_assoc,Nat.or_comm]
  · have rem : r<64 := Nat.mod_lt _ (by decide)
    simp only [spill,ite_false,right,src k klt,Nat.mod_eq_of_lt rem,BitVec.toNat_ushiftRight,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (full _)]

end CommitGolfCandidate.Reconstruction.CheckField
