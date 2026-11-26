import CommitGolfCandidate.S5CheckCursorBounds
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
attribute [local irreducible] S5.atProof S5.packedInput readBuffer
theorem view_indices (x : CheckInput) (batch : Bool) : (view batch x).idx=S5.recordIndex x.positions ∧ (view batch x).entry=S5.recordValue x :=
  by cases batch <;> exact ⟨rfl,rfl⟩
end CommitGolfCandidate.S5Machine.Check
