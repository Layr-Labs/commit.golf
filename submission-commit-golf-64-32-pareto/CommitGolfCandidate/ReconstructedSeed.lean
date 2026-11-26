import CommitGolf.Artifact
import CommitGolfCandidate.Execution
import CommitGolfCandidate.ReconstructedFetch

namespace CommitGolfCandidate.Reconstruction
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

private def seedOps : List Instr :=
  [.LUI .x8 0x15000, .ADDIW .x8 .x8 247, .SLLI .x8 .x8 4, .ADDI .x5 .x0 2,
   .ADDI .x10 .x8 32, .ADDI .x11 .x0 24, .ECALL]

def seedState (s : MachineState) (n : Nat) := (seedOps.take n).foldl execInstrBr s

private def seedWords : List (BitVec 32) :=
  [0x15000437, 0x0f74041b, 0x00441413, 0x00200293, 0x02040513, 0x01800593, 0x00000073]

private theorem packed_word (i : Fin 7) :
    Artifact.commitCode.get 32 ⟨i.val, Nat.lt_trans i.isLt (by decide : 7 < 150132)⟩ =
      seedWords[i.val]?.getD 0 := by
  fin_cases i <;> rfl

private theorem decoded (i : Fin 7) :
    decodeInstruction (Artifact.commitCode.get 32 ⟨i.val, Nat.lt_trans i.isLt (by decide : 7 < 150132)⟩) =
      some (.base (seedOps[i.val]?.getD .EBREAK)) := by
  rw [packed_word]
  fin_cases i <;> rfl

attribute [local irreducible] ArtifactEncoding.decode

private theorem seed_fetch (i : Fin 7) (s : MachineState)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*i.val)) :
    fetch (Artifact.submission.image .commit) s = some (.base (seedOps[i.val]?.getD .EBREAK)) := by
  have small := i.isLt
  have inside : i.val < 150132 := by omega
  have fits : 4096 + 4*i.val < 2^64 := by omega
  have code : (Artifact.submission.image .commit).code = ArtifactEncoding.decode 32 Artifact.commitCode := by
    exact Eq.refl (ArtifactEncoding.decode 32 Artifact.commitCode)
  exact (@fetch_packed 150132 _ Artifact.commitCode code i.val inside fits s pc).trans (decoded i)

theorem seed_setup (s : MachineState) (pc : s.pc = 4096) (fuel : Nat) :
    execute (Artifact.submission.image .commit) (6+fuel) s true =
      (do let r ← execute (Artifact.submission.image .commit) fuel (seedState s 6) true
          return r.charge 6 0) := by
  apply execute_unit_steps (states := seedState s)
  intro i hi
  refine ⟨.base (seedOps[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply seed_fetch ⟨i, by omega⟩
    interval_cases i <;> simp [seedState, seedOps, execInstrBr, pc, MachineState.setPC]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem seed_length (s : MachineState) : (seedState s 6).getReg .x11 = 24 := rfl

theorem seed_destination (s : MachineState) : (seedState s 6).getReg .x10 = 5637148560 := by
  simp [seedState, seedOps, execInstrBr, MachineState.setPC, MachineState.setReg, MachineState.getReg, signExtend12]

theorem generator_register (s : MachineState) : (seedState s 6).getReg .x8 = 5637148528 := by
  simp [seedState, seedOps, execInstrBr, MachineState.setPC, MachineState.setReg, MachineState.getReg, signExtend12]

theorem seed_register_setup_memory (s : MachineState) : (seedState s 6).mem = s.mem := rfl

theorem seed_syscall_pc (s : MachineState) : (seedState s 6).pc = s.pc+24 := by
  change s.pc+4+4+4+4+4+4 = s.pc+24
  simp only [BitVec.add_assoc]
  rfl

/-- The seed read in the delivered commitment costs ten cycles up to and including RANDOM.
The continuation is universally quantified over the remaining fuel. -/
theorem actual_seed_prefix (s : MachineState) (pc : s.pc = 4096) (fuel : Nat) :
    execute (Artifact.submission.image .commit) (7+fuel) s true =
      (do let seed ← liftM ($ᵗ BitVec (8*((seedState s 6).getReg .x11).toNat) : ProbComp _)
          let r ← execute (Artifact.submission.image .commit) fuel
            (writeBits (seedState s 6) 5637148560 seed) true
          return r.charge 10 0) := by
  let ready := seedState s 6
  have loc : ready.pc = 4120 := by simp [ready, seedState, seedOps, execInstrBr, pc, MachineState.setPC]
  have f := seed_fetch 6 ready loc
  change fetch _ _ = some (.base .ECALL) at f
  have mode : ready.getReg .x5 = 2 := rfl
  have dst : ready.getReg .x10 = 5637148560 := seed_destination s
  have n : ready.getReg .x11 = 24 := rfl
  have valid : randomArgumentsValid ready = true := by
    simp only [randomArgumentsValid, dst, n, rangeValid, MEMORY_BYTES]
    decide
  rw [show 7+fuel = 6+(fuel+1) by omega, seed_setup s pc]
  change (do let r ← execute _ (fuel+1) ready true; pure (r.charge 6 0)) = _
  rw [execute, f]
  simp only [mode, valid, dst, n]
  simp [Execution.charge, ready, ← Nat.add_assoc]

end CommitGolfCandidate.Reconstruction
