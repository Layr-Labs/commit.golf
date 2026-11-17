import CommitGolfCandidate.S3CommitRef
import CommitGolfCandidate.Group341Encoding

/-! Instruction fetches of the appended stage-3 leaf phase. Word 54 jumps to word 251827
(PC 1011404): five entry words, 64 leaves of fourteen words (PC 1011424 + 56u), three latch
words (PC 1015008), 42 repair words and three exit words (PC 1015020). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The fourteen instructions of leaf `u`; slots 3 and 12 are the permutation calls. -/
def s3LeafCode (u : Nat) : List Instr :=
  s3LeafHeadInstructions ++ [.ECALL] ++ s3LeafMidInstructions u ++ [.ECALL, .ADDI .x10 .x10 184]

def s3FinishInstructions : List Instr := s3RepairInstructions ++ s3ExitInstructions

theorem s3_entry_decoded (k : Nat) (hk : k < 5) :
    (s3AppendedWords[k]?).bind decodeInstruction =
      some (.base ((s3EntryInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s3_leaf_decoded (u i : Nat) (hu : u < 64) (hi : i < 14) :
    (s3AppendedWords[5 + 14 * u + i]?).bind decodeInstruction =
      some (.base (((s3LeafCode u)[i]?).getD .EBREAK)) := by
  interval_cases u <;> interval_cases i <;> rfl

theorem s3_latch_decoded (k : Nat) (hk : k < 3) :
    (s3AppendedWords[901 + k]?).bind decodeInstruction =
      some (.base ((s3LatchInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s3_finish_decoded (k : Nat) (hk : k < 45) :
    (s3AppendedWords[904 + k]?).bind decodeInstruction =
      some (.base ((s3FinishInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

/-- Word `k` of the appended code is fetched at PC `1011404 + 4k`. -/
theorem s3_image_word (k : Nat) (instruction : Instr) (state : MachineState)
    (bounded : k < 8145) (pc : state.pc = BitVec.ofNat 64 (1011404 + 4 * k))
    (decoded : (s3AppendedWords[k]?).bind decodeInstruction = some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  apply commit_fetch state (251827 + k) _ (by omega)
  · rw [pc]
    congr 1
    omega
  · change (group341ImageWords[251827 + k]?).bind decodeInstruction = _
    rw [s3_appended_word]
    exact decoded

theorem s3_image_entry (k : Nat) (hk : k < 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1011404 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s3EntryInstructions[k]?).getD .EBREAK)) :=
  s3_image_word k _ state (by omega) pc (s3_entry_decoded k hk)

theorem s3_image_leaf (u i : Nat) (hu : u < 64) (hi : i < 14) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1011424 + 56 * u + 4 * i)) :
    fetch (submission.image .commit) state =
      some (.base (((s3LeafCode u)[i]?).getD .EBREAK)) := by
  apply s3_image_word (5 + 14 * u + i) _ state (by omega) _ (s3_leaf_decoded u i hu hi)
  rw [pc]
  congr 1
  omega

theorem s3_image_latch (k : Nat) (hk : k < 3) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1015008 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s3LatchInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (901 + k) _ state (by omega) _ (s3_latch_decoded k hk)
  rw [pc]
  congr 1
  omega

theorem s3_image_finish (k : Nat) (hk : k < 45) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1015020 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s3FinishInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (904 + k) _ state (by omega) _ (s3_finish_decoded k hk)
  rw [pc]
  congr 1
  omega

end CommitGolfCandidate
