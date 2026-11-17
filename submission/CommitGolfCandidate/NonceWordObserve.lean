import CommitGolfCandidate.NonceWordBytes

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open NonceCopyMemory
set_option maxHeartbeats 400000

private theorem word_bytes_ext {first second : Word}
    (same : ∀ byte, byte<8 → extractByte first byte=extractByte second byte) : first=second := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  have remainder : bit%8<8 := by omega
  have position : bit/8*8+bit%8=bit := by omega
  have equal:=congrArg (fun value : Byte => value.getLsbD (bit%8)) (same (bit/8) (by omega))
  simp only [extractByte,BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight,position,remainder,
    decide_true,Bool.true_and] at equal
  exact equal

theorem nonce_aligned_word_eq (before after : MachineState) (location : Nat)
    (aligned : location%8=0)
    (same : ∀ byte<8, before.getByte (BitVec.ofNat 64 (location+byte))=
      after.getByte (BitVec.ofNat 64 (location+byte))) :
    before.getMem (BitVec.ofNat 64 location)=after.getMem (BitVec.ofNat 64 location) := by
  apply word_bytes_ext
  intro byte bounded
  have observed:=same byte bounded
  rw [nonce_aligned_byte before location byte aligned,nonce_aligned_byte after location byte aligned,
    Nat.div_eq_of_lt bounded,Nat.mod_eq_of_lt bounded] at observed
  simpa only [address,Nat.mul_zero,Nat.add_zero] using observed
end CommitGolfCandidate
