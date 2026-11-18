import CommitGolfCandidate.S3CommitRef
import CommitGolfCandidate.Group341Encoding

/-! Instruction fetches of the appended code, part A: the code lists of a leaf, a group call and a parent, the
decoded words of every block except leaves 22..63, and the fetch lemmas of those blocks. `S3Image` collects the
parts. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The eleven instructions of leaf `l`; slots 6 and 9 are the permutation calls. -/
def s3LeafCode (l : Nat) : List Instr :=
  s3LeafHeadInstructions l ++ [.ECALL] ++ s3LeafMidInstructions l ++ [.ECALL, s3LeafTailInstruction l]

/-- The three instructions of group call `c`; slot 2 is the permutation call. -/
def s6GroupCallCode (c : Nat) : List Instr :=
  s6GroupCallInstructions c ++ [.ECALL]

/-- The four instructions of one parent; slot 0 is the compression call. -/
def s6ParentCode : List Instr :=
  .ECALL :: s6ParentStepInstructions

theorem s6_clear_decoded (k : Nat) (hk : k < 5) :
    (s3AppendedWords[202 + k]?).bind decodeInstruction =
      some (.base ((s6GenClearInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s6_leaf_setup_decoded (k : Nat) (hk : k < 9) :
    (s3AppendedWords[207 + k]?).bind decodeInstruction =
      some (.base ((s6LeafSetupInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s6_block_base_decoded (k : Nat) (hk : k < 2) :
    (s3AppendedWords[216 + k]?).bind decodeInstruction =
      some (.base ((s6BlockBaseInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s6_group_call_decoded (c i : Nat) (hc : c < 16) (hi : i < 3) :
    (s3AppendedWords[922 + 3 * c + i]?).bind decodeInstruction =
      some (.base (((s6GroupCallCode c)[i]?).getD .EBREAK)) := by
  interval_cases c <;> interval_cases i <;> rfl

theorem s3_latch_decoded (k : Nat) (hk : k < 5) :
    (s3AppendedWords[970 + k]?).bind decodeInstruction =
      some (.base ((s3LatchInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s6_parent_setup_decoded (k : Nat) (hk : k < 7) :
    (s3AppendedWords[975 + k]?).bind decodeInstruction =
      some (.base ((s6ParentSetupInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

/-- Word `k` of the parent loop body: the four parent words, repeated. -/
def s6ParentBodyWord (k : Nat) : BitVec 32 :=
  match k % 4 with
  | 0 => 115
  | 1 => 401187
  | 2 => 4228187411
  | _ => 4261807635

/-- The parent loop body as one list comparison (linear in its length, instead of one list lookup
per word). -/
theorem s6_parent_body :
    (s3AppendedWords.drop 982).take 1024 = List.ofFn (fun k : Fin 1024 => s6ParentBodyWord k.val) := by
  decide +kernel

theorem s6_parent_body_word (k : Nat) (inside : k < 1024) :
    s3AppendedWords[982 + k]? = some (s6ParentBodyWord k) := by
  have read := congrArg (fun words : List (BitVec 32) => words[k]?) s6_parent_body
  simp only [List.getElem?_take_of_lt inside, List.getElem?_drop, List.getElem?_ofFn] at read
  rw [read, dif_pos inside]

/-- The 1,024 words of the parent loop body repeat the four parent words. -/
theorem s6_parent_words (j i : Nat) (hj : j < 256) (hi : i < 4) :
    s3AppendedWords[982 + 4 * j + i]? = s3AppendedWords[982 + i]? := by
  rw [show 982 + 4 * j + i = 982 + (4 * j + i) by omega, s6_parent_body_word (4 * j + i) (by omega),
    s6_parent_body_word i (by omega)]
  unfold s6ParentBodyWord
  rw [show (4 * j + i) % 4 = i % 4 by omega]

theorem s6_parent_decoded (j i : Nat) (hj : j < 256) (hi : i < 4) :
    (s3AppendedWords[982 + 4 * j + i]?).bind decodeInstruction =
      some (.base ((s6ParentCode[i]?).getD .EBREAK)) := by
  rw [s6_parent_words j i hj hi]
  interval_cases i <;> rfl

theorem s6_parent_branch_decoded :
    (s3AppendedWords[2006]?).bind decodeInstruction = some (.base s6ParentBranch) := by
  rfl

theorem s6_parent_exit_decoded :
    (s3AppendedWords[2007]?).bind decodeInstruction = some (.base s6ParentExit) := by
  rfl

/-- Leaves 0..21 of `s3_leaf_decoded`. -/
theorem s3_leaf_decoded_first (l i : Nat) (hl : l < 22) (hi : i < 11) :
    (s3AppendedWords[218 + 11 * l + i]?).bind decodeInstruction =
      some (.base (((s3LeafCode l)[i]?).getD .EBREAK)) := by
  interval_cases l <;> interval_cases i <;> rfl

/-- Word `k` of the appended code is fetched at PC `1011404 + 4k`. -/
theorem s3_image_word (k : Nat) (instruction : Instr) (state : MachineState)
    (bounded : k < 2008) (pc : state.pc = BitVec.ofNat 64 (1011404 + 4 * k))
    (decoded : (s3AppendedWords[k]?).bind decodeInstruction = some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  apply commit_fetch state (251827 + k) _ (by omega)
  · rw [pc]
    congr 1
    omega
  · change (group341ImageWords[251827 + k]?).bind decodeInstruction = _
    rw [s3_appended_word]
    exact decoded

theorem s6_image_clear (k : Nat) (hk : k < 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1012212 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s6GenClearInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (202 + k) _ state (by omega) _ (s6_clear_decoded k hk)
  rw [pc]
  congr 1
  omega

theorem s6_image_leaf_setup (k : Nat) (hk : k < 9) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1012232 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s6LeafSetupInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (207 + k) _ state (by omega) _ (s6_leaf_setup_decoded k hk)
  rw [pc]
  congr 1
  omega

theorem s6_image_block_base (k : Nat) (hk : k < 2) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1012268 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s6BlockBaseInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (216 + k) _ state (by omega) _ (s6_block_base_decoded k hk)
  rw [pc]
  congr 1
  omega

theorem s6_image_group_call (c i : Nat) (hc : c < 16) (hi : i < 3) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1015092 + 12 * c + 4 * i)) :
    fetch (submission.image .commit) state =
      some (.base (((s6GroupCallCode c)[i]?).getD .EBREAK)) := by
  apply s3_image_word (922 + 3 * c + i) _ state (by omega) _ (s6_group_call_decoded c i hc hi)
  rw [pc]
  congr 1
  omega

theorem s3_image_latch (k : Nat) (hk : k < 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1015284 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s3LatchInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (970 + k) _ state (by omega) _ (s3_latch_decoded k hk)
  rw [pc]
  congr 1
  omega

theorem s6_image_parent_setup (k : Nat) (hk : k < 7) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1015304 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s6ParentSetupInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (975 + k) _ state (by omega) _ (s6_parent_setup_decoded k hk)
  rw [pc]
  congr 1
  omega

/-- Slot `i` of parent `j` of the loop body. -/
theorem s6_image_parent (j i : Nat) (hj : j < 256) (hi : i < 4) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1015332 + 16 * j + 4 * i)) :
    fetch (submission.image .commit) state =
      some (.base ((s6ParentCode[i]?).getD .EBREAK)) := by
  apply s3_image_word (982 + 4 * j + i) _ state (by omega) _ (s6_parent_decoded j i hj hi)
  rw [pc]
  congr 1
  omega

theorem s6_image_parent_branch (state : MachineState) (pc : state.pc = BitVec.ofNat 64 1019428) :
    fetch (submission.image .commit) state = some (.base s6ParentBranch) := by
  apply s3_image_word 2006 _ state (by omega) _ s6_parent_branch_decoded
  rw [pc]

theorem s6_image_parent_exit (state : MachineState) (pc : state.pc = BitVec.ofNat 64 1019432) :
    fetch (submission.image .commit) state = some (.base s6ParentExit) := by
  apply s3_image_word 2007 _ state (by omega) _ s6_parent_exit_decoded
  rw [pc]

end CommitGolfCandidate
