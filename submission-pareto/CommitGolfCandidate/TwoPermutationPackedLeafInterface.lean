import CommitGolfCandidate.TwoPermutationPackedZeroLeaves
import CommitGolfCandidate.NonceChainSetup

/-! The delivered leaf-phase contract, independent of internal-parent hashing. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure PackedLeavesFinished (state : MachineState) : Prop where
  pc : state.pc=184608
  selector : state.getReg .x5=0
  heap : state.getReg .x9=4294971424
  stride : state.getReg .x19=536870912
  stop : state.getReg .x21=wordAddress (leafDest (2^24))
  output : state.getReg .x8=4294971392

structure PackedLeafExecution where
  trace : MachineState → OracleComp World MachineState
  executes : ∀ (ready : MachineState), Chain.BodyRegs ready → ∀ fuel : Nat,
    execute packedWideCommitImage (184754175+fuel) ready true =
      (do let leaves ← trace ready
          let out ← execute packedWideCommitImage fuel leaves true
          return out.charge 419635199 33554432)
  finished : ∀ (ready : MachineState), Chain.BodyRegs ready → ∀ out ∈ support (trace ready),
    PackedLeavesFinished out

end TwoPermutationPrototype.RV64
