import CommitGolfCandidate.ChainedContinuationDomain
import CommitGolfCandidate.Memory

/-! The native continuation header denotes the canonical next-stage input. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option exponentiation.threshold 520

private theorem append_nat {a b : Nat} (high : BitVec a) (low : BitVec b) :
    (high ++ low).toNat = high.toNat*2^b+low.toNat := by
  rw [BitVec.toNat_append,← Nat.shiftLeft_add_eq_or_of_lt low.isLt,Nat.shiftLeft_eq]

theorem domain_input (s : MachineState) (buffer : Word) (h : Height) (j : Nat)
    (small : j < 7) (aligned : buffer.toNat % 8 = 0) (words : DomainWords s buffer h j) :
    readBuffer s buffer.toNat 64 = canonicalEncoding.next h (j+1) (readBuffer s buffer.toNat 32) := by
  have address (k : Nat) : BitVec.ofNat 64 (buffer.toNat+32+k) = buffer+BitVec.ofNat 64 (32+k) := by
    rw [Nat.add_assoc,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have address0 : BitVec.ofNat 64 (buffer.toNat+32) = buffer+32 := by
    simpa using address 0
  rw [read_compression_halves s buffer.toNat aligned,
    read_digest_words s (buffer.toNat+32) (by omega),address 24,address 16,address 8,address0]
  norm_num only [Nat.reduceAdd]
  erw [words.tag,words.zero0,words.zero1,words.flag]
  change _ = encodeNext h (j+1) _
  rw [encodeNext_valid h (j+1) _ (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [pack_value]
  have tagSmall : 7*h.val+j < 2^64 := by have := h.isLt; omega
  simp only [append_nat,BitVec.toNat_ofNat,symbolCode,Nat.add_sub_cancel]
  rw [Nat.mod_eq_of_lt tagSmall]
  norm_num
  ring

end CommitGolfCandidate.Chained.Native
