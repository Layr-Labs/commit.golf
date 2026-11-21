import CommitGolfCandidate.TwoPermutationPackedLeafLatch
import CommitGolfCandidate.ChainedCommitFetch

/-! Compose the unchanged delivered leaves and masking prefix without the old parent image. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64

theorem chained_image_packed : chainedCommitImage = packedWideCommitImage := packed_manifest_image.symm

def leafPrefixTrace (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← PackedLeaves.executableLeaves.trace ready
  return zeroEntry leaves

theorem leaf_prefix_execution (ready : MachineState) (regs : Chain.BodyRegs ready) (fuel : Nat) :
    execute chainedCommitImage (184754175+zeroEntryCost+fuel) ready true =
      (do let parents ← leafPrefixTrace ready
          let result ← execute chainedCommitImage fuel parents true
          return result.charge (419635199+zeroEntryCost) 33554432) := by
  rw [chained_image_packed,show 184754175+zeroEntryCost+fuel=184754175+(zeroEntryCost+fuel) by omega,
    PackedLeaves.executableLeaves.executes ready regs]
  simp only [leafPrefixTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have fin := PackedLeaves.executableLeaves.finished ready regs leaves reached
  rw [zero_entry_execute leaves fin.pc fin.stride fin.stop]
  simp [Execution.charge,Nat.add_assoc]

theorem leaf_prefix_parent_pc (ready : MachineState) (regs : Chain.BodyRegs ready) (out : MachineState)
    (reached : out ∈ support (leafPrefixTrace ready)) : out.pc = 184628 := by
  simp only [leafPrefixTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨leaves,last,rfl⟩ := reached
  have fin := PackedLeaves.executableLeaves.finished ready regs leaves last
  exact zero_entry_pc leaves fin.pc fin.stride fin.stop

end CommitGolfCandidate.Chained.Native
