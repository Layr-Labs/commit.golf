import CommitGolf.Riscv
import Mathlib.Tactic
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def mergeWord (r : Nat) (v p : Word) := if r=0 then v else (v <<< (8*r)) ||| p
def restWord (r n : Nat) (v : Word) :=
  if r+n<8 then (v <<< (8*(8-n))) >>> (8*(8-n))
  else (v <<< (8*(8-n))) >>> (8*(16-r-n))

private theorem bitOfByte (v : Word) (k b : Nat) (hb : b<8) :
    (extractByte v k).getLsbD b=v.getLsbD (8*k+b) := by
  simp [extractByte,hb,Nat.mul_comm,Nat.add_comm]
theorem byteMerge (v p : Word) (r j : Nat) (r8 : r<8) (j8 : j<8)
    (zero : r≤j → r≠0 → extractByte p j=0) :
    extractByte (mergeWord r v p) j=if j<r then extractByte p j else extractByte v (j-r) := by
  by_cases rz:r=0
  · subst r;simp [mergeWord]
  rw [mergeWord,if_neg rz]
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  rw [bitOfByte _ _ _ hb,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft]
  simp only [show 8*j+b<64 by omega,decide_true,Bool.true_and]
  by_cases lt:j<r
  · rw [if_pos lt,bitOfByte _ _ _ hb]
    simp [show 8*j+b<8*r by omega]
  · rw [if_neg lt,bitOfByte _ _ _ hb]
    have z:=congrArg (fun x : Byte=>x.getLsbD b) (zero (by omega) rz)
    simp only [bitOfByte _ _ _ hb, BitVec.getLsbD_zero] at z
    simp [show ¬8*j+b<8*r by omega,z,show 8*j+b-8*r=8*(j-r)+b by omega]

theorem byteRest (v : Word) (r n j : Nat) (r8 : r<8) (n8 : n≤8) (j8 : j<8)
    (short : r+n<8 → r=0) (nonzero : (r+n)%8≠0) :
    extractByte (restWord r n v) j =
      if j<(r+n)%8 then extractByte v ((if r+n<8 then 0 else 8-r)+j) else 0 := by
  apply BitVec.eq_of_getLsbD_eq;intro b hb
  rw [bitOfByte _ _ _ hb]
  by_cases fits : r+n<8
  · have rz:=short fits;subst r
    rw [restWord,if_pos fits,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft]
    simp only [if_pos fits,Nat.zero_add,Nat.mod_eq_of_lt (by omega : n<8)]
    by_cases yes : j<n
    · rw [if_pos yes,bitOfByte _ _ _ hb]
      simp only [show 8*(8-n)+(8*j+b)<64 by omega,show ¬8*(8-n)+(8*j+b)<8*(8-n) by omega,decide_true,decide_false,Bool.not_false,Bool.true_and,Nat.add_sub_cancel_left,Nat.zero_add,if_pos (show n<8 by omega)]
    · rw [if_neg yes]
      simp [show ¬8*(8-n)+(8*j+b)<64 by omega]
  · rw [restWord,if_neg fits,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft]
    by_cases yes : j<(r+n)%8
    · rw [if_pos yes,if_neg fits,bitOfByte _ _ _ hb]
      have lo : ¬8*(16-r-n)+(8*j+b)<8*(8-n):=by omega
      have hi : 8*(16-r-n)+(8*j+b)<64:=by omega
      simp only [hi,lo,decide_false,decide_true,Bool.not_false,Bool.true_and]
      congr 1;omega
    · rw [if_neg yes]
      simp [show ¬8*(16-r-n)+(8*j+b)<64 by omega]
end CommitGolfCandidate.R4b
