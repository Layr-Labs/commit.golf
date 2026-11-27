import CommitGolfCandidate.Stage3cMessageInput

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
theorem initial_empty (m : Message) (addr count : Nat) (lo : 4294971392 ≤ addr)
    (hi : addr+count ≤ MEMORY_BYTES) :
    readBuffer (startState m) addr count = 0 := by
  apply (initial_input_read Artifact.submission .commit m addr count (by unfold MEMORY_BYTES at hi; omega)).trans
  have zero (i : Nat) (lt : i < count) :
      inputByte Artifact.submission .commit m (addr+i) = 0 := by
    have above : ¬addr+i < 4096+16777216*256 := by omega
    have below : ¬MEMORY_BYTES ≤ addr+i := by omega
    unfold inputByte
    change (match [messageBuffer 4096 m].find? _ with
      | some b => b.byteAt (addr+i-b.address)
      | none => if MEMORY_BYTES ≤ addr+i then _ else _) = _
    simp [List.find?_cons, messageBuffer, show LEAF_SIZE / 8 = 256 by decide,
      show LENGTH = 16777216 by decide, above, below]
  have sumZero : (∑ j ∈ Finset.range count, (inputByte Artifact.submission .commit m (addr+j)).toNat * 2^(8*j)) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [zero j (Finset.mem_range.mp hj)]; simp
  rw [sumZero]
  rfl

end CommitGolfCandidate.Chained.BinaryMachine
