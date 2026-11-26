import CommitGolfCandidate.ReconstructedCommitLoop
import CommitGolfCandidate.ReconstructedCommitSlices
import CommitGolfCandidate.ReconstructedSeed

namespace CommitGolfCandidate.Reconstruction.CommitSetup
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitControl CommitBlocks CommitSlices

set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local irreducible] ArtifactEncoding.decode

def im : Image := Artifact.submission.image .commit

/-- Fetch a concrete instruction in the commit image by its packed index. -/
theorem fetch_at (i : Fin 150132) (op : Instruction)
    (decode : decodeInstruction (Artifact.commitCode.get 32 i) = some op)
    (s : MachineState) (pc : s.pc = addr i.val) :
    fetch im s = some op := by
  have h := CommitSlices.commit_view i s (by simpa using pc)
  exact h.trans decode

/-- Execute a register-only setup instruction and retain exactly the relevant registers. -/
theorem set_counter (i : Nat) (x y : Word) (op : Instr)
    (f : ∀ s : MachineState, s.pc = addr i → fetch im s = some (.base op))
    (effect : ∀ s : MachineState, At (addr i) x s →
      ordinaryStep s (.base op) = some (execInstrBr s op) ∧ At (addr (i+1)) y (execInstrBr s op))
    (fee : instructionCycles (.base op) = 1) :
    Fragment im 1 1 0 (At (addr i) x) (At (addr (i+1)) y) := by
  intro s hs r hr
  obtain ⟨step,post⟩ := effect s hs
  rw [execute_ordinary_step im _ s _ 0 true (f s hs.1) step] at hr
  simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
  subst r
  exact ⟨by simp [Execution.charge,fee], by rfl, fun _ => post⟩

end CommitGolfCandidate.Reconstruction.CommitSetup
