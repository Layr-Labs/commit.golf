import CommitGolf.Riscv

/-! A machine buffer as a byte list. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def nonceMemoryBytes (state : MachineState) (base length : Nat) : List Byte :=
  (List.range length).map (fun offset => state.getByte (BitVec.ofNat 64 (base+offset)))

theorem nonce_memory_bytes_length (state : MachineState) (base length : Nat) :
    (nonceMemoryBytes state base length).length = length := by
  simp only [nonceMemoryBytes, List.length_map, List.length_range]

end CommitGolfCandidate
