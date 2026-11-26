import CommitGolfCandidate.ReconstructedCheckDivideOps

namespace CommitGolfCandidate.Reconstruction.CheckDivision
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine LeafModel CheckRecorded CheckDivideOps CommitBlocks
open TwoPermutationPrototype.RV64
set_option maxRecDepth 24000
set_option maxHeartbeats 1400000

def ops (cell : Nat) : List Op := [
  .normal (.ld .x7 .x22 0 cell),
  .div .x28 .x27 .x7,
  .normal (.reg .x29 (.slli .x28 32)),
  .normal (.reg .x28 (.mul .x28 .x7)),
  .normal (.reg .x28 (.subw .x27 .x28)),
  .normal (.reg .x27 (.srli .x29 32)),
  .normal (.reg .x28 (.slli .x28 32)),
  .normal (.reg .x28 (.or .x28 .x18)),
  .div .x28 .x28 .x7,
  .normal (.reg .x29 (.slli .x28 32)),
  .normal (.reg .x28 (.mul .x28 .x7)),
  .normal (.reg .x28 (.subw .x18 .x28)),
  .normal (.reg .x18 (.srli .x29 32)),
  .normal (.reg .x28 (.slli .x28 32)),
  .normal (.reg .x28 (.or .x28 .x20)),
  .div .x28 .x28 .x7,
  .normal (.reg .x29 (.slli .x28 32)),
  .normal (.reg .x28 (.mul .x28 .x7)),
  .normal (.reg .x28 (.subw .x20 .x28)),
  .normal (.reg .x20 (.srli .x29 32)),
  .normal (.reg .x28 (.slli .x28 32)),
  .normal (.reg .x28 (.or .x28 .x25)),
  .div .x29 .x28 .x7,
  .normal (.reg .x30 (.slli .x29 32)),
  .normal (.reg .x25 (.srli .x30 32)),
  .normal (.reg .x7 (.mul .x29 .x7)),
  .normal (.reg .x7 (.sub .x28 .x7)),
  .normal (.reg .x15 (.sll .x7 .x15)),
  .normal (.reg .x6 (.or .x15 .x6))]

def after (m : Model) (cell : Nat) := (ops cell).foldl (fun a op=>op.apply a) m

private theorem listed (cell : Nat) : CheckStraight.Listed 351 ((ops cell).map Op.instr) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩

theorem positive (o : Oracle) (m : Model) (cell : Nat) (room : cell<2^33) (atCell : m.reg .x22=wordAddress cell)
    (s : MachineState) (pc : s.pc=addr 351) (fits : Fits s m) :
    ∃ t, Segment o 29 s t [] ∧ t.pc=addr 380 ∧ Fits t (after m cell) := by
  have valid : Valid m (ops cell) := by
    simp only [ops,Valid,OpeningOps.Op.Valid,true_and,and_true]
    exact ⟨room,by rw [atCell];exact BitVec.add_zero _⟩
  exact block o m (ops cell) 351 (by change 351+29≤796;decide) (listed cell) valid s pc fits

end CommitGolfCandidate.Reconstruction.CheckDivision
