import CommitGolfCandidate.CapOpenPathPrepare

/-! The reference lower-path iteration prepares the sibling address, copies
four words, advances the cursor, moves to the parent and decrements the path
counter. CapFastPath executes the equivalent unrolled path. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenPathTailInstructions : List Instr :=
  [.ADDI .x25 .x25 32, .SRLI .x20 .x20 1,
   .ADDI .x28 .x28 4095, .BNE .x28 .x0 8136]

def capOpenPathTailPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capOpenPathTailInstructions.take count).foldl execInstrBr state

def capOpenPathCopied (state : MachineState) : MachineState :=
  capDigestCopyPrefix false (capOpenPathPrefix state 3) 8

def capOpenPathState (state : MachineState) : MachineState :=
  capOpenPathTailPrefix (capOpenPathCopied state) 4

private theorem fold_take_next {A S : Type} (step : S → A → S)
    (code : List A) (state : S) (fallback : A) (i : Nat) (hi : i < code.length) :
    (code.take (i+1)).foldl step state =
      step ((code.take i).foldl step state) ((code[i]?).getD fallback) := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos code i hi, Option.getD_some]

theorem cap_open_path_tail_succ (state : MachineState) (count : Nat)
    (bounded : count < 4) :
    capOpenPathTailPrefix state (count+1) =
      execInstrBr (capOpenPathTailPrefix state count)
        ((capOpenPathTailInstructions[count]?).getD .EBREAK) := by
  exact fold_take_next execInstrBr capOpenPathTailInstructions state .EBREAK count
    (by simpa only [capOpenPathTailInstructions, List.length_cons, List.length_nil] using bounded)

theorem cap_open_path_tail_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) :
    (capOpenPathTailPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capOpenPathTailPrefix, capOpenPathTailInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_open_path_copy_access (state : MachineState) (node rootBase cursor : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (base : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (rootBound : rootBase + 32*(node ^^^ 1) + 32 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (cursorBound : cursor + 32 ≤ MEMORY_BYTES) (cursorAligned : cursor % 8 = 0) :
    (∀ word : Fin 4,
      accessValid ((capOpenPathPrefix state 3).getReg .x23 +
        BitVec.ofNat 64 (8*word.val)) 8 = true) ∧
    (∀ word : Fin 4,
      accessValid ((capOpenPathPrefix state 3).getReg .x25 +
        BitVec.ofNat 64 (8*word.val)) 8 = true) := by
  have root := cap_open_path_address state node rootBase index base
  have cursorPointer := (cap_open_path_prepare_register state 3 (by decide) .x25
    (by decide)).trans pointer
  have rootSmall : rootBase + 32*(node ^^^ 1) < 2^64 := by
    simp only [MEMORY_BYTES] at rootBound
    omega
  have cursorSmall : cursor < 2^64 := by
    simp only [MEMORY_BYTES] at cursorBound
    omega
  rw [root, cursorPointer]
  constructor
  · apply opening_digest_access_valid
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt rootSmall] using rootBound
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt rootSmall]
      omega
  · apply opening_digest_access_valid
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cursorSmall] using cursorBound
    · simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cursorSmall] using cursorAligned

end CommitGolfCandidate
