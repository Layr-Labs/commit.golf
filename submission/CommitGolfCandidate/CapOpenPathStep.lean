import CommitGolfCandidate.CapOpenPathPrepare

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

theorem cap_open_path_tail_execute (state : MachineState) (pc : state.pc = 4324)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (4+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenPathTailPrefix state 4) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := capOpenPathTailPrefix state)
  intro i bounded
  refine ⟨.base ((capOpenPathTailInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (57+i) _ (by omega)
    · rw [cap_open_path_tail_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · rw [cap_open_path_tail_succ state i bounded]
    interval_cases i <;>
      simp only [capOpenPathTailInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, ↓reduceIte]
  · interval_cases i <;> rfl

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

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_open_path_execute (state : MachineState) (node rootBase cursor : Nat)
    (pc : state.pc = 4280)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (base : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (rootBound : rootBase + 32*(node ^^^ 1) + 32 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (cursorBound : cursor + 32 ≤ MEMORY_BYTES) (cursorAligned : cursor % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (15+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenPathState state) allowCoins
          return result.charge 15 0) := by
  have accesses := cap_open_path_copy_access state node rootBase cursor index base pointer
    rootBound rootAligned cursorBound cursorAligned
  have copyPC : (capOpenPathPrefix state 3).pc = 4292 := by
    rw [cap_open_path_prepare_pc state 3 (by decide), pc]
    rfl
  have tailPC : (capOpenPathCopied state).pc = 4324 := by
    rw [capOpenPathCopied, cap_copy_prefix_pc false _ 8 (by decide), copyPC]
    rfl
  have tailRun : execute ((capExperimental 24).image .opening) (4+fuel)
      (capDigestCopyPrefix false (capOpenPathPrefix state 3) 8) allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenPathState state) allowCoins
          return result.charge 4 0) :=
    cap_open_path_tail_execute (capOpenPathCopied state) tailPC fuel allowCoins
  rw [show 15+fuel = 3+(8+(4+fuel)) by omega,
    cap_open_path_prepare_execute state pc,
    cap_digest_copy_execute _ false 4292 cap_open_path_copy_fetched
      (capOpenPathPrefix state 3) copyPC accesses.1 accesses.2,
    tailRun]
  simp only [capOpenPathState, capOpenPathCopied, bind_assoc, pure_bind, charge_pair,
    Nat.reduceAdd]

end CommitGolfCandidate
