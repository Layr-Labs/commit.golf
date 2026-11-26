import CommitGolfCandidate.ReconstructedCommitSetup

namespace CommitGolfCandidate.Reconstruction.CommitSetup
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitControl CommitBlocks CommitSlices

set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local irreducible] ArtifactEncoding.decode

private theorem seedPC (s : MachineState) (pc : s.pc = 4096) :
    (seedState s 6).pc + 4 = addr 7 := by
  change s.pc+4+4+4+4+4+4+4 = _
  rw [pc]; rfl

private theorem seedCounter (s : MachineState) :
    (seedState s 6).getReg .x20 = s.getReg .x20 := rfl

private theorem writePC {n : Nat} (s : MachineState) (a : Word) (v : BitVec n) :
    (writeBits s a v).pc = s.pc+4 := rfl

private theorem lastStep (s : MachineState) (pc : s.pc = addr 7)
    (counter : s.getReg .x20 = 0) :
    ∀ r ∈ support (execute im 1 s true),
      r.cycles = 1 ∧ r.oracleCalls = 0 ∧ At (addr 8) 0 r.state := by
  have f := fetch_at 7 (.base (.ADDI .x5 .x0 0)) (by rfl) s pc
  intro r hr
  rw [execute_ordinary_step im (.base (.ADDI .x5 .x0 0)) s
    (execInstrBr s (.ADDI .x5 .x0 0)) 0 true f rfl] at hr
  simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
  subst r
  exact ⟨rfl,rfl,congrArg (·+4) pc,rfl,counter⟩

attribute [local irreducible] execute seedState writeBits

theorem boot (initial : MachineState) (pc : initial.pc = 4096) (counter : initial.getReg .x20 = 0) :
    ∀ r ∈ support (execute im 8 initial true),
      r.cycles = 11 ∧ r.oracleCalls = 0 ∧ At (addr 8) 0 r.state := by
  have h := actual_seed_prefix initial pc 1
  intro r hr
  change r ∈ support (execute (Artifact.submission.image .commit) (7+1) initial true) at hr
  rw [h] at hr
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hr
  obtain ⟨seed,_,run,runMem,rfl⟩ := hr
  have post := lastStep _ ((writePC _ _ _).trans (seedPC initial pc))
    ((writeBits_register ..).trans ((seedCounter initial).trans counter)) run runMem
  simpa only [Execution.charge,post.1,post.2.1,Nat.zero_add,true_and] using post.2.2

end CommitGolfCandidate.Reconstruction.CommitSetup
