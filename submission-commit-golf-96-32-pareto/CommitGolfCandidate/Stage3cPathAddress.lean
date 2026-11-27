import Mathlib.Data.Nat.Bitwise
import CommitGolfCandidate.Stage3cOpenExpressions
import CommitGolfCandidate.Stage3cOpenSources
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape bytes node record gapOffset)
def layerBase (l : Nat) := tdBase+levelOffset l
def stride (l : Nat) := 48*levelCount l
def indexAbove (i : Index) (l : Nat) := i.val/2^l
def mate (i : Index) (l : Nat) := indexAbove i l ^^^ 1

theorem above_bound (i : Index) (l : Nat) (le : l≤LOG_LENGTH) : indexAbove i l < levelCount l := by
  have power : levelCount l * 2^l = LENGTH := by
    unfold levelCount LENGTH; rw [←Nat.pow_add, Nat.sub_add_cancel le]
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^l)).mpr
  exact power.symm ▸ i.isLt

theorem mate_bound (i : Index) (l : Nat) (lt : l<LOG_LENGTH) : mate i l < levelCount l := by
  have one : 1 < 2^(LOG_LENGTH-l) := Nat.one_lt_pow (by omega) (by decide)
  exact Nat.xor_lt_two_pow (above_bound _ _ (by omega)) one

theorem above_next (i : Index) (l : Nat) : indexAbove i (l+1) = indexAbove i l/2 := by
  unfold indexAbove;rw [Nat.div_div_eq_div_mul,Nat.pow_succ]

theorem step_base (l : Nat) (lt : l<LOG_LENGTH) : layerBase l+stride l=layerBase (l+1) := by
  have s := level_successor l lt;unfold layerBase stride;rw [level_adjacent l lt];omega

theorem step_stride (l : Nat) (lt : l<LOG_LENGTH) : stride l/2=stride (l+1) := by
  have s := level_successor l lt; unfold stride;omega

def pathBytes (tree : Levels) (i : Index) (l n : Nat) : Proof :=
  (List.range' l n).flatMap fun j => bytes (n:=32) (node tree j (mate i j))

theorem path_cons (tree : Levels) (i : Index) (l n : Nat) :
    pathBytes tree i l (n+1) = bytes (n:=32) (node tree l (mate i l)) ++ pathBytes tree i (l+1) n := by
  simp only [pathBytes,List.range'_succ,List.flatMap_cons]

theorem path_len (tree : Levels) (i : Index) (l n : Nat) : (pathBytes tree i l n).length=32*n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [path_cons,List.length_append,ih];simp [bytes];omega

theorem record_eq (t : Levels) (s : SaltTape) (d : Nat) (i : Index) :
    record t s d i = bytes (n:=24) (s i) ++ pathBytes t i 0 d := by
  simp only [record,pathBytes,mate,indexAbove,List.range_eq_range']

theorem shifted (n k : Nat) : (BitVec.ofNat 64 n <<< k) = BitVec.ofNat 64 (n*2^k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mul_mod]

theorem shr (n k : Nat) (small : n<2^64) : (BitVec.ofNat 64 n >>> k) = BitVec.ofNat 64 (n/2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) small)]

theorem table_sibling_address (base j : Nat) (bound : j<2^64) :
    W base + ((((W j >>> 1) <<< 1) + (W j >>> 1)) <<< 5) + (((W j &&& 1) ^^^ 1) <<< 5)=
      W (base+gapOffset (j ^^^ 1)) := by
  have low : (W j &&& 1)=W (j%2) := by
    change (BitVec.ofNat 64 j &&& BitVec.ofNat 64 (2^1-1))=_
    rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod];rfl
  rw [low]
  unfold W
  rw [shr j 1 bound,shifted,←BitVec.ofNat_add,shifted,←BitVec.ofNat_add]
  change _ + ((BitVec.ofNat 64 (j%2) ^^^ BitVec.ofNat 64 1) <<< 5)=_
  rw [←BitVec.ofNat_xor,shifted,←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  unfold gapOffset
  by_cases even : j%2=0
  · rw [even,Nat.xor_one_of_even (Nat.even_iff.mpr even)];simp;omega
  · rw [show j%2=1 by omega,Nat.xor_one_of_odd (n:=j) (Nat.odd_iff.mpr (by omega))];simp;omega

end CommitGolfCandidate.Chained.BinaryMachine.Open
