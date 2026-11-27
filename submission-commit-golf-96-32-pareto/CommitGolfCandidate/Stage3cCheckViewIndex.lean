import CommitGolfCandidate.Stage3cCheckCursorBounds
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
attribute [local irreducible] Pw.atProof Pw.packedInput readBuffer
theorem view_indices (x : CheckInput) (batch : Bool) : (view batch x).idx=Pw.recordIndex x.positions ∧ (view batch x).entry=Pw.recordValue x :=
  by cases batch <;> exact ⟨rfl,rfl⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
