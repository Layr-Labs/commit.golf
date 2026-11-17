import CommitGolfCandidate.NonceSaltMemory
import CommitGolfCandidate.WriteMemory

/-! Byte-exact extraction of one padded nonce from packed syscall randomness. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem read_nonce_buffer (state : MachineState) (address : Nat) :
    readNonce state address=expandNonce192 (readBuffer state address 24) := by
  unfold readNonce
  rw [read_buffer_slice state address 32 0 24 (by decide)]
  rfl

theorem write_bits_nonce {bits : Nat} (state : MachineState) (address offset : Nat)
    (answer : BitVec bits) (inside : offset+24≤(bits+7)/8) (bounded : (bits+7)/8≤2^64) :
    readNonce (writeBits state (BitVec.ofNat 64 address) answer) (address+offset)=
      expandNonce192 (answer.extractLsb' (8*offset) 192) := by
  rw [read_nonce_buffer]
  apply congrArg expandNonce192
  apply read_serialized_slice
  intro j hj
  have written := write_bits_byte state (BitVec.ofNat 64 address) answer (offset+j) (by omega) bounded
  simpa only [BitVec.ofNat_add,Nat.add_assoc,BitVec.add_assoc] using written

theorem write_bits_nonce_chunk (count : Nat) (state : MachineState) (address : Nat)
    (answer : BitVec (192*count)) (index : Fin count) (bounded : 24*count≤2^64) :
    readNonce (writeBits state (BitVec.ofNat 64 address) answer) (address+24*index.val)=
      expandNonce192 (answer.extractLsb' (192*index.val) 192) := by
  have size : (192*count+7)/8=24*count := by omega
  have result := write_bits_nonce state address (24*index.val) answer
    (by rw [size];have h:=index.isLt;omega) (by rw [size];exact bounded)
  simpa only [show 8*(24*index.val)=192*index.val by omega] using result

end CommitGolfCandidate
