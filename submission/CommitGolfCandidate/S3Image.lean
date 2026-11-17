import CommitGolfCandidate.S3CommitRef
import CommitGolfCandidate.Group341Encoding

/-! Exact fetches for eight 64-leaf segments. Each segment retains the same
fourteen-instruction leaves and two pointer advances. Only the last segment
executes the two-instruction long-loop transfer. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def s3SegmentPC (segment : Nat) : Nat := 1011424 + 3592 * segment

def s3LeafCode (u : Nat) : List Instr :=
  s3LeafHeadInstructions ++ [.ECALL] ++ s3LeafMidInstructions u ++ [.ECALL, .ADDI .x10 .x10 184]

def s3LongLatchInstructions : List Instr :=
  [.BLTU .x23 .x22 8, .JAL .x0 8, .JAL .x0 2068408]

def s3FinishInstructions : List Instr := s3RepairInstructions ++ s3ExitInstructions

theorem s3_segment_word (segment index : Nat) (hs : segment < 8) (hi : index < 898) :
    s3AppendedWords[5 + 898 * segment + index]? =
      some (s3SegmentWords.getD index 0) := by
  unfold s3AppendedWords
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  change (List.ofFn (fun i : Fin 7184 => s3SegmentWords.getD (i.val % 898) 0) ++
    s3ClosingWords)[5 + 898 * segment + index - 5]? = _
  rw [show 5 + 898 * segment + index - 5 = 898 * segment + index by omega]
  rw [List.getElem?_append_left (by simp only [List.length_ofFn]; omega), List.getElem?_ofFn, dif_pos (by omega)]
  change some (s3SegmentWords.getD ((898 * segment + index) % 898) 0) = _
  rw [show (898 * segment + index) % 898 = index by omega]

theorem s3_closing_word (index : Nat) :
    s3AppendedWords[7189 + index]? = s3ClosingWords[index]? := by
  unfold s3AppendedWords
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
  change (List.ofFn (fun i : Fin 7184 => s3SegmentWords.getD (i.val % 898) 0) ++
    s3ClosingWords)[7189 + index - 5]? = _
  rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn]
  rw [show 7189 + index - 5 - 7184 = index by omega]

theorem s3_entry_decoded (k : Nat) (hk : k < 5) :
    (s3AppendedWords[k]?).bind decodeInstruction =
      some (.base ((s3EntryInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s3_leaf_decoded (segment u i : Nat) (hs : segment < 8) (hu : u < 64) (hi : i < 14) :
    (s3AppendedWords[5 + 898 * segment + 14 * u + i]?).bind decodeInstruction =
      some (.base (((s3LeafCode u)[i]?).getD .EBREAK)) := by
  rw [show 5 + 898 * segment + 14 * u + i = 5 + 898 * segment + (14 * u + i) by omega,
    s3_segment_word segment (14 * u + i) hs (by omega)]
  interval_cases u <;> interval_cases i <;> rfl

theorem s3_advance_decoded (segment k : Nat) (hs : segment < 8) (hk : k < 2) :
    (s3AppendedWords[5 + 898 * segment + 896 + k]?).bind decodeInstruction =
      some (.base ((s3LatchInstructions[k]?).getD .EBREAK)) := by
  rw [show 5 + 898 * segment + 896 + k = 5 + 898 * segment + (896 + k) by omega,
    s3_segment_word segment (896 + k) hs (by omega)]
  interval_cases k <;> rfl

theorem s3_long_latch_decoded (k : Nat) (hk : k < 3) :
    (s3AppendedWords[7189 + k]?).bind decodeInstruction =
      some (.base ((s3LongLatchInstructions[k]?).getD .EBREAK)) := by
  rw [s3_closing_word]
  interval_cases k <;> rfl

theorem s3_finish_decoded (k : Nat) (hk : k < 45) :
    (s3AppendedWords[7192 + k]?).bind decodeInstruction =
      some (.base ((s3FinishInstructions[k]?).getD .EBREAK)) := by
  rw [show 7192 + k = 7189 + (3 + k) by omega, s3_closing_word]
  interval_cases k <;> rfl

theorem s3_image_word (k : Nat) (instruction : Instr) (state : MachineState)
    (bounded : k < 7237) (pc : state.pc = BitVec.ofNat 64 (1011404 + 4 * k))
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

theorem s3_image_leaf (segment u i : Nat) (hs : segment < 8) (hu : u < 64) (hi : i < 14)
    (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (s3SegmentPC segment + 56 * u + 4 * i)) :
    fetch (submission.image .commit) state =
      some (.base (((s3LeafCode u)[i]?).getD .EBREAK)) := by
  apply s3_image_word (5 + 898 * segment + 14 * u + i) _ state (by omega) _
    (s3_leaf_decoded segment u i hs hu hi)
  rw [pc]
  congr 1
  simp only [s3SegmentPC]
  omega

theorem s3_image_advance (segment k : Nat) (hs : segment < 8) (hk : k < 2)
    (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (s3SegmentPC segment + 3584 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s3LatchInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (5 + 898 * segment + 896 + k) _ state (by omega) _
    (s3_advance_decoded segment k hs hk)
  rw [pc]
  congr 1
  simp only [s3SegmentPC]
  omega

theorem s3_image_long_latch (k : Nat) (hk : k < 3) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1040160 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s3LongLatchInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (7189 + k) _ state (by omega) _ (s3_long_latch_decoded k hk)
  rw [pc]
  congr 1
  omega

theorem s3_image_finish (k : Nat) (hk : k < 45) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1040172 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s3FinishInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (7192 + k) _ state (by omega) _ (s3_finish_decoded k hk)
  rw [pc]
  congr 1
  omega

end CommitGolfCandidate
