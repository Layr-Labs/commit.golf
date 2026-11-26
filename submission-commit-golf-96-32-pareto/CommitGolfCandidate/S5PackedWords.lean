import CommitGolfCandidate.S5Model
import CommitGolf.Riscv
namespace CommitGolfCandidate.S5Machine.Writer
open RiscvZkvm.Rv64
/-- A pending word has only its low `k` bits occupied. OR-ing the shifted source
therefore emits the low word of the concatenation. -/
theorem joined_word (buffer source : Word) (k : Nat) (fits : buffer.toNat<2^k) :
    buffer ||| (source <<< k) = BitVec.ofNat 64 (buffer.toNat+2^k*source.toNat) := by
  rw [Nat.add_comm,Nat.two_pow_add_eq_or_of_lt fits,BitVec.ofNat_or,BitVec.ofNat_toNat,BitVec.or_comm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mul_comm]

/-- When the low word is full, the high part is obtained by shifting only
the source word. The `exactFit` arm of the code handles a zero carry. -/
theorem joined_carry (buffer source : Word) (k : Nat) (hk : k≤64) (fits : buffer.toNat<2^k) :
    (source >>> (64-k)).toNat=(buffer.toNat+2^k*source.toNat)/2^64 := by
  have top : 2^64=2^k*2^(64-k) := by rw [←pow_add,show k+(64-k)=64 by omega]
  rw [top,←Nat.div_div_eq_div_mul,Nat.add_comm,Nat.mul_add_div (Nat.two_pow_pos k),
    Nat.div_eq_of_lt fits,Nat.add_zero,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

def widths (fs : List S5.Field) := (fs.map Prod.fst).sum

theorem encode_append (fs gs : List S5.Field) :
    S5.encode (fs++gs)=S5.encode fs+2^widths fs*S5.encode gs := by
  induction fs with
  | nil=>simp [S5.encode,widths]
  | cons x xs ih=>
    simp only [List.cons_append,S5.encode,ih,widths,List.map_cons,List.sum_cons,pow_add]
    ring

theorem encode_bound (fs : List S5.Field) : S5.encode fs < 2^widths fs := by
  induction fs with
  | nil=>simp [S5.encode,widths]
  | cons x xs ih=>
    have residue:=Nat.mod_lt x.2 (Nat.two_pow_pos x.1)
    have bound:=Nat.mul_le_mul_left (2^x.1) (show S5.encode xs+1≤2^widths xs from ih)
    rw [Nat.mul_add,Nat.mul_one] at bound
    change x.2%2^x.1+2^x.1*S5.encode xs<2^(x.1+widths xs)
    rw [pow_add];omega
end CommitGolfCandidate.S5Machine.Writer
