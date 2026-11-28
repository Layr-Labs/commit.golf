import CommitGolfCandidate.QuadCommitGeometry
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationPackedLeafInput

namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
open CommitGolfCandidate (read_buffer_memory_congr read_serialized_slice splitBlocks initial_input_byte inputByte write_bits_byte write_bits_read_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits image leafCode levelsCode

structure ABI (s : Submission) : Prop where
  code : s.image .commit=image
  message : s.layout.message=4096
  output : s.layout.commitment=4294971392
  heap : s.layout.trapdoor=4294971424

theorem abi (opening checker : Image) : ABI (submission opening checker) := ⟨rfl,rfl,rfl,rfl⟩

theorem abi_entry (s : Submission) (abi : ABI s) (msg : Message) : CommitEntry (s.initialState .commit msg) := by
  refine ⟨rfl,?_,?_,?_⟩
  · change BitVec.ofNat 64 s.layout.message=_;rw [abi.message];rfl
  · change BitVec.ofNat 64 s.layout.commitment=_;rw [abi.output];rfl
  · change BitVec.ofNat 64 s.layout.trapdoor=_;rw [abi.heap];rfl

end TwoPermutationPrototype.Quad.Commit
