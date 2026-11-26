import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.WriteMemoryCore

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Any complete digest within a syscall reply can be read back unchanged. -/
theorem write_bits_digest {bits : Nat} (state : MachineState) (address offset : Nat)
    (answer : BitVec bits) (inside : offset+32 ≤ (bits+7)/8)
    (bounded : (bits+7)/8 ≤ 2^64) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) answer) (address+offset) 32 =
      answer.extractLsb' (8*offset) 256 := by
  apply read_serialized_slice
  intro j hj
  have written := write_bits_byte state (BitVec.ofNat 64 address) answer (offset+j) (by omega) bounded
  simpa only [BitVec.ofNat_add, Nat.add_assoc, BitVec.add_assoc] using written

end CommitGolfCandidate
