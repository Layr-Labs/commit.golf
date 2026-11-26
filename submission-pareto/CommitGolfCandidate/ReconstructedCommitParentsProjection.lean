import CommitGolfCandidate.ReconstructedCommitParentsSpec
import CommitGolf.Riscv

namespace CommitGolfCandidate.Reconstruction.CommitParents
open Binding RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 850000

def lowMask (d : Nat) := BitVec.ofNat 64 (2^(width d-192)-1)

private theorem normal_top (d : Fin 24) (zero : modulus d = 0) (x : Binding.Digest) :
    (project d x).2 = x.2 &&& lowMask d := by
  apply BitVec.eq_of_toNat_eq
  rw [project_hi,BitVec.toNat_and]
  unfold radix lowMask
  rw [ite_eq_left zero,BitVec.toNat_ofNat]
  have upper := (ranges d (by have := d.isLt;omega)).2.2.1
  have b := Nat.pow_le_pow_right (n := 2) (by decide) (show width d-192 ≤ 64 by omega)
  rw [Nat.mod_eq_of_lt (show 2^(width d-192)-1<2^64 by have := Nat.two_pow_pos (width d-192); omega),Nat.and_two_pow_sub_one_eq_mod]

private theorem half_top (w x : BitVec 64) :
    replaceHalfword w 3 (x.truncate 16) = (w &&& 0xffffffffffff) ||| (x <<< 48) := by
  have mask : ~~~(0xffff#64 <<< (3*16 : Nat))=(0xffffffffffff : BitVec 64) := by decide
  rw [replaceHalfword,mask]
  apply congrArg (fun v => (w &&& 0xffffffffffff) ||| v)
  change (x.truncate 16).zeroExtend 64 <<< 48 = x <<< 48
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth]
  by_cases h : i<48
  · simp [hi,h]
  · simp [hi,h,show i-48<16 by omega,show i-48<64 by omega]

private theorem narrow_top (w x : BitVec 64) :
    replaceWord32 w 1 (((extractHalfword w 2).zeroExtend 64 ||| x).truncate 32) =
      (w &&& 0xffffffffffff) ||| (x <<< 32) := by
  change (w &&& 0xffffffff#64) ||| (((((w >>> 32).truncate 16).zeroExtend 64 ||| x).truncate 32).zeroExtend 64 <<< 32) = _
  have bits (i : Fin 64) :
      (0xffffffff#64).getLsbD i = decide (i.val<32) ∧ (0xffffffffffff#64).getLsbD i = decide (i.val<48) := by
    exact (by decide : ∀ i : Fin 64, (0xffffffff#64).getLsbD i=decide (i.val<32) ∧
      (0xffffffffffff#64).getLsbD i=decide (i.val<48)) i
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨low,high⟩ := bits ⟨i,hi⟩
  change (0xffffffff#64).getLsbD i = _ at low
  have high' : (0xffffffffffff : BitVec 64).getLsbD i = decide (i<48) := high
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight,low,high']
  have bit : (0xffffffffffff#64)[i]=decide (i<48) := high
  by_cases h : i < 32
  · simp [h,show i<48 by omega,hi,bit]
  · have di : 32+(i-32)=i := by omega
    by_cases k : i<48 <;>
      simp [h,k,hi,bit,show ¬i<32 by omega,show i-32<32 by omega,show i-32<64 by omega,
        show i-32<16 ↔ i<48 by omega,di,Nat.add_comm]

private theorem same_fill (w m n fill : BitVec 64) (agree : m &&& ~~~fill = n &&& ~~~fill) :
    (w &&& m) ||| fill = (w &&& n) ||| fill := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have eq := congrArg (fun v : BitVec 64=>v.getLsbD i) agree
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] at eq
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_and]
  cases h : fill.getLsbD i <;> simp_all

theorem wide_store (d : Fin 24) (wide : width d=240) (x : Binding.Digest) :
    replaceHalfword x.2 3 ((BitVec.ofNat 64 d.val).truncate 16) = (written d (project d x)).2 := by
  have facts : ∀ n : Fin 24, width n = 240 →
      n.val ≠ 0 ∧ modulus n = 0 ∧ lowMask n = 0xffffffffffff ∧ childMask n false = BitVec.ofNat 64 n.val <<< 48 := by decide
  obtain ⟨nz,m,lo,mask⟩ := facts d wide
  simp only [half_top,written,nz,ite_false,marked,normal_top d m,lo,mask]
  rfl

theorem residue_store (d : Fin 24) (res : modulus d ≠ 0) (x : Binding.Digest) :
    x.2 % BitVec.ofNat 64 (modulus d) = (written d (project d x)).2 := by
  have bounds : ∀ i : Fin 24, modulus i ≠ 0 → i.val ≠ 0 ∧ modulus i < 2^64 := by decide
  obtain ⟨nz,small⟩ := bounds d res
  simp only [written,nz,ite_false,marked,childMask,res,Bool.false_eq_true,BitVec.or_zero]
  change _ = (project d x).2 ||| 0#64
  rw [BitVec.or_zero]
  apply BitVec.eq_of_toNat_eq
  rw [project_hi,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  simp [radix,res]

theorem narrow_store (d : Fin 24) (narrow : width d < 240) (reg : modulus d = 0) (x : Binding.Digest) :
    replaceWord32 x.2 1 (((extractHalfword x.2 2).zeroExtend 64 ||| BitVec.ofNat 64 (narrowMarker d)).truncate 32) =
      (written d (project d x)).2 := by
  have facts : ∀ i : Fin 24, width i < 240 → modulus i = 0 →
    i.val ≠ 0 ∧ childMask i false = BitVec.ofNat 64 (narrowMarker i) <<< 32 ∧
    (0xffffffffffff : BitVec 64) &&& ~~~(childMask i false) = lowMask i &&& ~~~(childMask i false) := by decide
  obtain ⟨nz,m,eq⟩ := facts d narrow reg
  rw [narrow_top,←m,written,ite_eq_right nz]
  change _ = (project d x).2 ||| childMask d false
  rw [normal_top d reg x]
  exact same_fill _ _ _ _ eq

theorem root_store (x : Binding.Digest) : written 0 (project 0 x) = x := by
  have c : Canonical 0 x := x.2.isLt
  rw [project_of_canonical 0 x c];rfl

theorem consumed_residue_right (d : Fin 25) (positive : 0 < d.val) (res : modulus d ≠ 0)
    (x : Binding.Digest) (can : Canonical d x) :
    replaceHalfword (written d x).2 3 ((BitVec.ofNat 64 d.val).truncate 16) = (marked d true x).2 := by
  have table : ∀ i : Fin 25, modulus i ≠ 0 → tag i = BitVec.ofNat 64 i.val ∧ radix i ≤ 2^48 := by decide
  obtain ⟨tg,bound⟩ := table d res
  have lo : x.2 &&& 0xffffffffffff#64 = x.2 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    change x.2.toNat &&& (2^48-1) = x.2.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod,Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le can bound)]
  rw [half_top]
  simp [written,Nat.ne_of_gt positive,marked,childMask,res,tg,lo]

end CommitGolfCandidate.Reconstruction.CommitParents
