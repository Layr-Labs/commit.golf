import CommitGolfCandidate.TwoPermutationOpeningCapFlow
import CommitGolfCandidate.QuartetRVImage

namespace TwoPermutationPrototype.QuartetRV
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (trapdoorBase markBase machineMarks markWord)

def quartetProofBase : Nat := 11676946528

structure CapContext (groups : List Nat) (state : MachineState) : Prop where
  heap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase
  markBaseWord : state.getReg .x26 = BitVec.ofNat 64 markBase
  capLeavesWord : state.getReg .x27 = 256#64
  proofStart : state.getReg .x20 = BitVec.ofNat 64 quartetProofBase
  markValue : ∀ node, 0 < node → node < 512 → machineMarks state node = markWord groups node

/-- The cap blocks preserve the fixed ABI registers and the physical marks. -/
theorem CapContext.of_preserved {groups : List Nat} {before after : MachineState}
    (context : CapContext groups before)
    (register : ∀ r, r ∈ ([.x25, .x26, .x27, .x20] : List Reg) →
      after.getReg r = before.getReg r)
    (marks : ∀ node, 0 < node → node < 512 → machineMarks after node = machineMarks before node) :
    CapContext groups after :=
  ⟨(register .x25 (by decide)).trans context.heap,
   (register .x26 (by decide)).trans context.markBaseWord,
   (register .x27 (by decide)).trans context.capLeavesWord,
   (register .x20 (by decide)).trans context.proofStart,
   fun node positive bounded => (marks node positive bounded).trans (context.markValue node positive bounded)⟩

end TwoPermutationPrototype.QuartetRV
