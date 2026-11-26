import CommitGolfCandidate.ReconstructedCommitSchedule

namespace CommitGolfCandidate.Reconstruction.CommitExit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitControl CommitBlocks CommitSetup CommitSchedule

attribute [local irreducible] ArtifactEncoding.decode execute

/-- These are the three instructions following the final root-word copy. -/
theorem finish : Fragment im 3 3 0 (StateAt 150129 1) (fun _ => False) := by
  intro s hs r hr
  let t := execInstrBr s (.ADDI .x5 .x0 1)
  let u := execInstrBr t (.ADDI .x10 .x0 0)
  have f := fetch_at 150129 (.base (.ADDI .x5 .x0 1)) rfl s hs.1
  have pt : t.pc = addr 150130 := congrArg (·+4) hs.1
  have g := fetch_at 150130 (.base (.ADDI .x10 .x0 0)) rfl t pt
  have pu : u.pc = addr 150131 := congrArg (·+4) pt
  have h := fetch_at 150131 (.base .ECALL) rfl u pu
  have e : execute im 1 u true = pure ⟨.success,u,1,0⟩ := by
    rw [execute,h]
    rfl
  rw [execute_ordinary_step im _ s t 2 true f rfl,
      execute_ordinary_step im _ t u 1 true g rfl,e] at hr
  simp only [pure_bind,support_pure,Set.mem_singleton_iff] at hr
  subst r
  exact ⟨Nat.le_refl 3,Nat.le_refl 0,fun h => by cases h⟩

end CommitGolfCandidate.Reconstruction.CommitExit
