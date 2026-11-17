import CommitGolfCandidate.NonceBits
import CommitGolfCandidate.NonceBuffer
/-! Little-endian reads of three nonce words and exact expansion back to the padded 256-bit salt representation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem read_nonce_words (state : MachineState) (address : Nat) (aligned : address%8=0) :
    readBuffer state address 24=
      (state.getMem (BitVec.ofNat 64 (address+16))++
        state.getMem (BitVec.ofNat 64 (address+8)))++
        state.getMem (BitVec.ofNat 64 address) := by
  have slice := read_buffer_slice state address 32 0 24 (by decide)
  simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] at slice
  rw [←slice,read_digest_words _ _ aligned]
  have extract (a b c d : Word) :
      (((a++b)++c)++d : BitVec 256).extractLsb' 0 192=(b++c)++d := nonce_bits_low a b c d
  exact extract _ _ _ _

theorem read_nonce_congr (left right : MachineState) (address : Nat) (aligned : address%8=0)
    (words : ∀ i<3,left.getMem (BitVec.ofNat 64 (address+8*i))=
      right.getMem (BitVec.ofNat 64 (address+8*i))) :
    readBuffer left address 24=readBuffer right address 24 := by
  rw [read_nonce_words _ _ aligned,read_nonce_words _ _ aligned,
    words 2 (by decide),words 1 (by decide)]
  rw [show left.getMem (BitVec.ofNat 64 address)=right.getMem (BitVec.ofNat 64 address) by simpa using words 0 (by decide)]
theorem nonce_expand_extract (state : MachineState) (address : Nat) :
    expandNonce192 ((readNonce state address).extractLsb' 0 192)=readNonce state address := by
  unfold readNonce expandNonce192
  have extract (nonce : BitVec 192) : (nonce.setWidth 256).extractLsb' 0 192=nonce := nonce_bits_expand_low nonce
  rw [extract]
end CommitGolfCandidate
