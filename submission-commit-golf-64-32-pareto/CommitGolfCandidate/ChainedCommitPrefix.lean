import CommitGolfCandidate.TwoPermutationPackedLeafLatch
import CommitGolfCandidate.ChainedCommitFetch
import CommitGolfCandidate.ChainedFastEntry

/-! Compose the unchanged delivered leaves and masking prefix without the old parent image. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64

theorem chained_image_packed : chainedCommitImage = packedWideCommitImage := packed_manifest_image.symm

def leafPrefixTrace (ready : MachineState) : OracleComp World MachineState := do
  let leaves ← PackedLeaves.executableLeaves.trace ready
  return skipEntry leaves

theorem leaf_prefix_execution (ready : MachineState) (regs : Chain.BodyRegs ready) (fuel : Nat) :
    execute chainedCommitImage (184754175+skipEntryCost+fuel) ready true =
      (do let parents ← leafPrefixTrace ready
          let result ← execute chainedCommitImage fuel parents true
          return result.charge (1157832703+skipEntryCost) 33554432) := by
  rw [chained_image_packed,show 184754175+skipEntryCost+fuel=184754175+(skipEntryCost+fuel) by omega,
    PackedLeaves.executableLeaves.executes ready regs]
  simp only [leafPrefixTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have fin := PackedLeaves.executableLeaves.finished ready regs leaves reached
  rw [skip_entry_execute leaves fin.pc]
  simp [Execution.charge,Nat.add_assoc]

theorem leaf_prefix_parent_pc (ready : MachineState) (regs : Chain.BodyRegs ready) (out : MachineState)
    (reached : out ∈ support (leafPrefixTrace ready)) : out.pc = 186848 := by
  simp only [leafPrefixTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨leaves,last,rfl⟩ := reached
  have fin := PackedLeaves.executableLeaves.finished ready regs leaves last
  exact (skip_entry_ready leaves fin.pc fin.selector fin.heap fin.stride fin.stop).2.1

end CommitGolfCandidate.Chained.Native
