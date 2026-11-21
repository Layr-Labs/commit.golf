import CommitGolfCandidate.ChainedFirstPackExecution
import CommitGolfCandidate.ChainedEncoding

/-! Bit-exact contiguous child layout used by the native first-stage packer. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 520

def childWord (value : BitVec 238) (index : Nat) : Word := value.extractLsb' (64*index) 64

def firstPackedWord (height : Word) (left right : BitVec 238) (index : Nat) : Word :=
  match index with
  | 0 => childWord left 0
  | 1 => childWord left 1
  | 2 => childWord left 2
  | 3 => childWord left 3 ||| (childWord right 0 <<< 46)
  | 4 => (childWord right 0 >>> 18) ||| (childWord right 1 <<< 46)
  | 5 => (childWord right 1 >>> 18) ||| (childWord right 2 <<< 46)
  | 6 => (childWord right 2 >>> 18) ||| (childWord right 3 <<< 46)
  | _ => (childWord right 3 >>> 18) ||| (height <<< 28)

def firstPackedValue (height : Word) (left right : BitVec 238) : Input :=
  firstPackedWord height left right 7 ++ firstPackedWord height left right 6 ++
    firstPackedWord height left right 5 ++ firstPackedWord height left right 4 ++
    firstPackedWord height left right 3 ++ firstPackedWord height left right 2 ++
    firstPackedWord height left right 1 ++ firstPackedWord height left right 0

theorem first_packed_bits (height : Word) (left right : BitVec 238) :
    firstPackedValue height left right = height.setWidth 36 ++ right ++ left := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i inside
  dsimp only [firstPackedValue,firstPackedWord,childWord]
  interval_cases i <;>
    simp only [BitVec.getLsbD_append,BitVec.getLsbD_or,BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth] <;> simp

private theorem append_nat {a b : Nat} (high : BitVec a) (low : BitVec b) :
    (high ++ low).toNat = high.toNat*2^b+low.toNat := by
  rw [BitVec.toNat_append,← Nat.shiftLeft_add_eq_or_of_lt low.isLt,Nat.shiftLeft_eq]

theorem first_packed_encoding (h : Height) (left right : BitVec 238) :
    firstPackedValue (BitVec.ofNat 64 h.val) left right = canonicalEncoding.first h (right ++ left) := by
  rw [first_packed_bits]
  apply BitVec.eq_of_toNat_eq
  change _ = (pack (.inl (h,right ++ left))).toNat
  rw [pack_value]
  have h64 : h.val < 2^64 := by have := h.isLt; omega
  have h36 : h.val < 2^36 := by have := h.isLt; omega
  simp only [append_nat,BitVec.toNat_setWidth,BitVec.toNat_ofNat,symbolCode,
    Nat.mod_eq_of_lt h64,Nat.mod_eq_of_lt h36]
  ring

end CommitGolfCandidate.Chained.Native
