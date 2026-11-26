import CommitGolfDepth.Rounds
import CommitGolf.Artifact

/-! Resource-only client of the real batched interpreter and artifact ABI.

The seven delivered instructions obtain two compression descriptors from embedded
image data through sp. The second input aliases the first output at byte 512:
both inputs must therefore be captured before either oracle response is written.
The theorem uses the zero message and every fixed oracle, including the runner's
independent public-call counter. It is not a cryptographic certificate or score.
-/

namespace CommitGolf.Challenge
open OracleComp OracleSpec CommitGolfDepth.Rounds CommitGolfDepth.Rounds.RoundMachine

private def fixtureImage : Riscv.Image :=
  ⟨[0x00010513, 0x00200593, 0x00300293, 0x73, 0x00100293, 0x00000513, 0x73], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 32, 2, 0, 0, 0, 0, 0, 0]⟩

def fixtureCore : CommitGolf.Submission where
  sizes := ⟨16, 64⟩
  layout := ⟨4096, 4294971392, 4294971424, 4294971440, 4429189168, 8724156464⟩
  image
    | .commit => fixtureImage
    | .opening => fixtureImage
    | .check => fixtureImage
  steps
    | .commit => 7
    | .opening => 7
    | .check => 7

def submission : CommitGolfDepth.Rounds.Submission where
  core := fixtureCore
  modes
    | .commit => .batched
    | .opening => .batched
    | .check => .batched

theorem submission_matches_artifact : submission = Artifact.depthSubmission := by rfl

theorem admission : submission.core.Admission := by
  intro program
  cases program <;> decide +kernel

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def observe (r : Execution) : Riscv.Exit × Nat × Nat × Nat :=
  (r.result.exit, r.result.cycles, r.result.oracleCalls, r.oracleRounds)

def initial : RiscvZkvm.Rv64.MachineState := fixtureCore.initialState .commit (fun _ => 0)
def s1 := (initial.setReg .x10 (BitVec.ofNat 64 (Riscv.dataBase (fixtureCore.image .commit)))).setPC 4100
def s2 := (s1.setReg .x11 2).setPC 4104
def s3 := (s2.setReg .x5 3).setPC 4108

theorem prefix0 : isBatchCall (fixtureCore.image .commit) initial = false := by rfl

theorem tick0 : Riscv.execute (fixtureCore.image .commit) 1 initial true =
    pure ⟨.unfinished, s1, 1, 0⟩ := by rfl

theorem prefix1 : isBatchCall (fixtureCore.image .commit) s1 = false := by rfl

theorem tick1 : Riscv.execute (fixtureCore.image .commit) 1 s1 true =
    pure ⟨.unfinished, s2, 1, 0⟩ := by rfl

theorem prefix2 : isBatchCall (fixtureCore.image .commit) s2 = false := by rfl

theorem tick2 : Riscv.execute (fixtureCore.image .commit) 1 s2 true =
    pure ⟨.unfinished, s3, 1, 0⟩ := by rfl

theorem snapshot : Batch.snapshotAll s3 [⟨0,0,64,512⟩,⟨0,512,64,544⟩] =
    some [⟨.inl 0,512⟩,⟨.inl 0,544⟩] := by decide +kernel

theorem batch_flag : isBatchCall (fixtureCore.image .commit) s3 = true := by rfl

theorem loaded : loadDescriptors s3 (s3.getReg .x10) (s3.getReg .x11).toNat =
    some [⟨0,0,64,512⟩,⟨0,512,64,544⟩] := by decide +kernel

def s4 (first second : BitVec COMPRESSION_OUTPUT_LENGTH) :=
  ((Batch.writeReply (Batch.writeReply s3 ⟨.inl 0,512⟩ first) ⟨.inl 0,544⟩ second).setPC 4112)
def s5 (first second : BitVec COMPRESSION_OUTPUT_LENGTH) := ((s4 first second).setReg .x5 1).setPC 4116
def s6 (first second : BitVec COMPRESSION_OUTPUT_LENGTH) := ((s5 first second).setReg .x10 0).setPC 4120

def finished (first second : BitVec COMPRESSION_OUTPUT_LENGTH) : Execution :=
  ⟨⟨.success, s6 first second, 33, 2⟩, 1⟩

private theorem suffix_at (state : RiscvZkvm.Rv64.MachineState) (atPC : state.pc = 4112) :
    executeBatched (fixtureCore.image .commit) 3 state true =
      pure (⟨⟨.success,
        (((state.setReg .x5 1).setPC 4116).setReg .x10 0).setPC 4120, 3, 0⟩, 0⟩ : Execution) := by
  let next := (state.setReg .x5 1).setPC 4116
  let last := (next.setReg .x10 0).setPC 4120
  have fetched4 : Riscv.fetch (fixtureCore.image .commit) state =
      some (.base (.ADDI .x5 .x0 1)) := by
    unfold Riscv.fetch
    rw [atPC]
    rfl
  have fetched5 : Riscv.fetch (fixtureCore.image .commit) next =
      some (.base (.ADDI .x10 .x0 0)) := by
    unfold Riscv.fetch
    rw [show next.pc = 4116 from rfl]
    rfl
  have fetched6 : Riscv.fetch (fixtureCore.image .commit) last =
      some (.base .ECALL) := by
    unfold Riscv.fetch
    rw [show last.pc = 4120 from rfl]
    rfl
  have flag4 : isBatchCall (fixtureCore.image .commit) state = false := by
    simp only [isBatchCall, fetched4]
  have tick4 : Riscv.execute (fixtureCore.image .commit) 1 state true =
      pure (⟨.unfinished, next, 1, 0⟩ : Riscv.Execution) := by
    rw [Riscv.execute, fetched4]
    change (do
      let result ← Riscv.execute (fixtureCore.image .commit) 0
        ((state.setReg .x5 1).setPC (state.pc + 4)) true
      pure (result.charge 1 0)) = _
    rw [atPC]
    rfl
  have flag5 : isBatchCall (fixtureCore.image .commit) next = false := by
    simp only [isBatchCall, fetched5]
  have tick5 : Riscv.execute (fixtureCore.image .commit) 1 next true =
      pure (⟨.unfinished, last, 1, 0⟩ : Riscv.Execution) := by
    rw [Riscv.execute, fetched5]
    rfl
  have flag6 : isBatchCall (fixtureCore.image .commit) last = false := by
    simp only [isBatchCall, fetched6]
    rfl
  have tick6 : Riscv.execute (fixtureCore.image .commit) 1 last true =
      pure (⟨.success, last, 1, 0⟩ : Riscv.Execution) := by
    rw [Riscv.execute, fetched6]
    rfl
  rw [executeBatched, flag4]
  simp only [Bool.false_eq_true, ite_false, tick4, pure_bind, ite_true]
  rw [executeBatched, flag5]
  simp only [Bool.false_eq_true, ite_false, tick5, pure_bind, ite_true]
  rw [executeBatched, flag6]
  simp only [Bool.false_eq_true, ite_false, tick6, pure_bind]
  rfl

theorem suffix (first second : BitVec COMPRESSION_OUTPUT_LENGTH) :
    executeBatched (fixtureCore.image .commit) 3 (s4 first second) true =
      pure (⟨⟨.success, s6 first second, 3, 0⟩, 0⟩ : Execution) :=
  suffix_at _ rfl

theorem run_queries :
    submission.run .commit (fun _ => 0) = (do
      let first ← (World.query (.inr (.inl 0)) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH))
      let second ← (World.query (.inr (.inl 0)) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH))
      pure (finished first second)) := by
  change executeBatched (fixtureCore.image .commit) 7 initial true = _
  rw [executeBatched, prefix0]
  simp only [Bool.false_eq_true, ite_false, tick0, pure_bind, ite_true]
  rw [executeBatched, prefix1]
  simp only [Bool.false_eq_true, ite_false, tick1, pure_bind, ite_true]
  rw [executeBatched, prefix2]
  simp only [Bool.false_eq_true, ite_false, tick2, pure_bind, ite_true]
  rw [executeBatched, batch_flag]
  simp only [ite_true, loaded, snapshot]
  simp only [runFrozenWorld, pure_bind, bind_assoc]
  change (do
    let first ← (World.query (.inr (.inl 0)) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH))
    let second ← (World.query (.inr (.inl 0)) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH))
    let rest ← executeBatched (fixtureCore.image .commit) 3 (s4 first second) true
    pure (charge (charge (charge (charge rest 27 2 1) 1 0 0) 1 0 0) 1 0 0)) = _
  simp only [suffix, pure_bind]
  rfl

private theorem extract_replace_last (word : BitVec 64) (byte : Byte) :
    RiscvZkvm.Rv64.extractByte (RiscvZkvm.Rv64.replaceByte word 7 byte) 7 = byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  interval_cases bit <;> simp [RiscvZkvm.Rv64.extractByte, RiscvZkvm.Rv64.replaceByte]

theorem first_byte (first second : BitVec COMPRESSION_OUTPUT_LENGTH) :
    (finished first second).result.state.getByte 543 = first.extractLsb' 248 8 := by
  change RiscvZkvm.Rv64.extractByte
    (RiscvZkvm.Rv64.replaceByte _ 7 (BitVec.ofNat 8 (first.toNat / 2^248))) 7 = _
  rw [extract_replace_last]
  simp only [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem second_byte (first second : BitVec COMPRESSION_OUTPUT_LENGTH) :
    (finished first second).result.state.getByte 575 = second.extractLsb' 248 8 := by
  change RiscvZkvm.Rv64.extractByte
    (RiscvZkvm.Rv64.replaceByte _ 7 (BitVec.ofNat 8 (second.toNat / 2^248))) 7 = _
  rw [extract_replace_last]
  simp only [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem run_fixed (oracle : Oracle) :
    oracle.run (submission.run .commit (fun _ => 0)) =
      pure (finished (oracle.compression 0) (oracle.compression 0), 2) := by
  rw [run_queries]
  rfl

theorem resource_fixture (oracle : Oracle) :
    Pr{let result ← oracle.run (submission.run .commit (fun _ => 0))}[
      result.1.result.exit = .success ∧ result.1.result.cycles ≤ 33 ∧
      result.1.oracleRounds ≤ 1 ∧ result.1.result.oracleCalls = 2 ∧ result.2 = 2 ∧
      result.1.result.state.getByte 543 = (oracle.compression 0).extractLsb' 248 8 ∧
      result.1.result.state.getByte 575 = (oracle.compression 0).extractLsb' 248 8] = 1 := by
  rw [run_fixed]
  simp only [prEvent_pure, first_byte, second_byte]
  simp [finished]

end CommitGolf.Challenge
