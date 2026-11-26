import CommitGolfCandidate.CheckRefinement

/-! Exact behavior of the checker image for a fixed oracle: exit code, cycles and calls.
The cap chain must reproduce the commitment, and every requested position must climb to
its supplied cap node; any failed comparison rejects the whole opening. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

/-- The four comparisons made by a comparison block. -/
def rootWordsMatch (cap : Bool) (state : MachineState) : Bool :=
  decide (∀ word : Fin 4,
    state.getMem (state.getReg .x21+BitVec.ofNat 64 (8*word.val)) =
      state.getMem (state.getReg (compareReg cap)+BitVec.ofNat 64 (8*word.val)))

theorem root_words_match_iff (cap : Bool) (state : MachineState) :
    rootWordsMatch cap state = true ↔
      ∀ word < 4, state.getMem (state.getReg .x21+BitVec.ofNat 64 (8*word)) =
        state.getMem (state.getReg (compareReg cap)+BitVec.ofNat 64 (8*word)) := by
  simp only [rootWordsMatch, decide_eq_true_eq]
  exact ⟨fun h word bound => h ⟨word, bound⟩, fun h word => h word word.isLt⟩

/-- States of one position iteration for a fixed oracle. -/
def positionHashState (oracle : Oracle) (state : MachineState) : MachineState :=
  (checkEvaluation oracle (checkPositionHash state)).1

def positionSelectState (oracle : Oracle) (state : MachineState) : MachineState :=
  checkCapSelectState (positionHashState oracle state)

def nextCheckState (oracle : Oracle) (state : MachineState) : MachineState :=
  checkPositionNextState (checkRootWordsState false (positionSelectState oracle state) 4)

/-- A finite, deterministic description of the machine's position loop. -/
def checkLoopAccepts (oracle : Oracle) : Nat → MachineState → Bool
  | 0, _ => true
  | count+1, state =>
      rootWordsMatch false (positionSelectState oracle state) &&
        checkLoopAccepts oracle count (nextCheckState oracle state)

/-- The full checker after the length gate: empty openings accept; otherwise the cap
comparison and every position must pass. -/
def checkReadyAccepts (oracle : Oracle) (count : Nat) (state : MachineState) : Bool :=
  count == 0 || (rootWordsMatch true (capPhaseState oracle state) &&
    checkLoopAccepts oracle count (checkRootWordsState true (capPhaseState oracle state) 4))

theorem check_evaluation_bind_fst (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).1 =
      (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).1 := by
  rw [check_evaluation_bind]

theorem evaluation_charge (oracle : Oracle) (computation : OracleComp World Execution)
    (cycles calls : Nat) :
    (checkEvaluation oracle (do let result ← computation; return result.charge cycles calls)).1 =
      (checkEvaluation oracle computation).1.charge cycles calls := by
  simp only [check_evaluation_bind_fst, check_evaluation_pure]

theorem evaluation_hash (oracle : Oracle) (hash : OracleComp World MachineState)
    (continuation : MachineState → OracleComp World Execution) (cycles calls : Nat) :
    (checkEvaluation oracle (do
      let state ← hash
      let result ← continuation state
      return result.charge cycles calls)).1 =
      (checkEvaluation oracle (continuation (checkEvaluation oracle hash).1)).1.charge cycles calls := by
  simp only [check_evaluation_bind_fst, check_evaluation_pure]

/-- Buffer and control invariants at the start of each position iteration. These are
memory-safety and input-format conditions, not assumptions about proof contents. -/
structure CheckLoopInvariant (state : MachineState) (count : Nat) : Prop where
  pc : state.pc = if count = 0 then 4616 else 4344
  counter : state.getReg .x27 = BitVec.ofNat 64 count
  scratch : state.getReg .x21 = 256
  indices : ∀ word < count,
    accessValid (state.getReg .x24 + BitVec.ofNat 64 (8 * word)) 8 = true
  indexBound : ∀ word < count,
    (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * word))).toNat < 2^24
  indexOutside : ∀ word < count, ∀ i < 12,
    state.getReg .x24 + BitVec.ofNat 64 (8 * word) ≠ BitVec.ofNat 64 (256 + 8 * i)
  values : ∀ word < 32 * count,
    accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true
  proofs : ∀ word < 71 * count,
    accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true
  capBase : ∀ word < 512,
    accessValid (state.getReg .x30 + BitVec.ofNat 64 (8 * word)) 8 = true

/-- The cap-node offset of an in-range index. -/
theorem cap_node_offset (value : Word) (small : value.toNat < 2^24) :
    (value >>> 17) <<< 5 = BitVec.ofNat 64 (32 * (value.toNat / 2^17)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  norm_num at small ⊢
  omega

private theorem shifted_address (base : Word) (offset word : Nat) :
    base + BitVec.ofNat 64 offset + BitVec.ofNat 64 (8 * word) =
      base + BitVec.ofNat 64 (offset + 8 * word) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem position_hash_registers (oracle : Oracle) (state : MachineState) :
    (positionHashState oracle state).pc = 4548 ∧
    (positionHashState oracle state).getReg .x8 = state.getReg .x8 + 256 ∧
    (positionHashState oracle state).getReg .x25 = state.getReg .x25 + 568 ∧
    (positionHashState oracle state).getReg .x20 = state.getMem (state.getReg .x24) >>> 17 ∧
    ∀ reg ∈ [Reg.x21, .x24, .x26, .x27, .x30],
      (positionHashState oracle state).getReg reg = state.getReg reg :=
  check_position_hash_registers state _ (check_evaluation_support oracle _)

theorem next_check_registers (oracle : Oracle) (state : MachineState) :
    (nextCheckState oracle state).getReg .x8 = state.getReg .x8 + 256 ∧
    (nextCheckState oracle state).getReg .x25 = state.getReg .x25 + 568 ∧
    (nextCheckState oracle state).getReg .x24 = state.getReg .x24 + 8 ∧
    (nextCheckState oracle state).getReg .x27 = state.getReg .x27 - 1 ∧
    (nextCheckState oracle state).getReg .x21 = state.getReg .x21 ∧
    (nextCheckState oracle state).getReg .x26 = state.getReg .x26 ∧
    (nextCheckState oracle state).getReg .x30 = state.getReg .x30 := by
  have regs := position_hash_registers oracle state
  let hashed := positionHashState oracle state
  let selected := checkCapSelectState hashed
  let compared := checkRootWordsState false selected 4
  have keep (reg : Reg) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) (not22 : reg ≠ .x22) :
      compared.getReg reg = hashed.getReg reg :=
    (check_root_words_preserves false selected 4 reg not6 not7).1.trans
      (check_cap_select_register hashed reg not7 not22)
  have other (reg : Reg) (not24 : reg ≠ .x24) (not27 : reg ≠ .x27) (not6 : reg ≠ .x6)
      (not7 : reg ≠ .x7) (not22 : reg ≠ .x22) :
      (nextCheckState oracle state).getReg reg = hashed.getReg reg := by
    change (checkPositionNextState compared).getReg reg = _
    simp only [checkPositionNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not27),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not24)]
    exact keep reg not6 not7 not22
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (other .x8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.2.1
  · exact (other .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans regs.2.2.1
  · change (checkPositionNextState compared).getReg .x24 = _
    simp only [checkPositionNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x27 ≠ .x24),
      MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0)]
    rw [keep .x24 (by decide) (by decide) (by decide), regs.2.2.2.2 .x24 (by simp)]
  · change (checkPositionNextState compared).getReg .x27 = _
    simp only [checkPositionNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0)]
    rw [keep .x27 (by decide) (by decide) (by decide), regs.2.2.2.2 .x27 (by simp)]
  · exact (other .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (regs.2.2.2.2 .x21 (by simp))
  · exact (other .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (regs.2.2.2.2 .x26 (by simp))
  · exact (other .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (regs.2.2.2.2 .x30 (by simp))

theorem position_select_memory (oracle : Oracle) (state : MachineState) :
    (positionSelectState oracle state).mem = (positionHashState oracle state).mem :=
  check_cap_select_memory _

private theorem latch_memory (state : MachineState) :
    (checkPositionNextState state).mem = state.mem := rfl

theorem next_check_mem (oracle : Oracle) (state : MachineState) :
    (nextCheckState oracle state).mem = (positionHashState oracle state).mem := by
  change (checkPositionNextState (checkRootWordsState false (positionSelectState oracle state) 4)).mem = _
  exact (latch_memory _).trans ((check_root_words_preserves false (positionSelectState oracle state) 4
    .x21 (by decide) (by decide)).2.trans (position_select_memory oracle state))

/-- Positions do not modify any memory word outside scratch. -/
theorem next_check_outside (oracle : Oracle) (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (nextCheckState oracle state).getMem address = state.getMem address := by
  have same : (nextCheckState oracle state).getMem address =
      (positionHashState oracle state).getMem address :=
    congrArg (fun mem => mem address) (next_check_mem oracle state)
  rw [same]
  exact check_position_hash_outside oracle state address scratch outside

/-- The selected cap node's address register. -/
theorem position_select_node (oracle : Oracle) (state : MachineState)
    (small : (state.getMem (state.getReg .x24)).toNat < 2^24) :
    (positionSelectState oracle state).getReg .x22 = state.getReg .x30 +
      BitVec.ofNat 64 (32 * ((state.getMem (state.getReg .x24)).toNat / 2^17)) := by
  have regs := position_hash_registers oracle state
  rw [positionSelectState, check_cap_select_node, regs.2.2.2.1, regs.2.2.2.2 .x30 (by simp),
    cap_node_offset _ small]

theorem position_select_scratch (oracle : Oracle) (state : MachineState)
    (scratch : state.getReg .x21 = 256) :
    (positionSelectState oracle state).getReg .x21 = 256 :=
  (check_cap_select_register _ .x21 (by decide) (by decide)).trans
    (((position_hash_registers oracle state).2.2.2.2 .x21 (by simp)).trans scratch)

/-- A successful iteration preserves the loop invariants for the remaining positions. -/
theorem check_loop_next_invariant (oracle : Oracle) (state : MachineState) (count : Nat)
    (bounded : count < 2 ^ 24) (invariant : CheckLoopInvariant state (count + 1)) :
    CheckLoopInvariant (nextCheckState oracle state) count := by
  have regs := next_check_registers oracle state
  have counter : (nextCheckState oracle state).getReg .x27 = BitVec.ofNat 64 count := by
    rw [regs.2.2.2.1, invariant.counter]
    change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
    congr 1
  have indexAddress (word : Nat) :
      (nextCheckState oracle state).getReg .x24 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x24 + BitVec.ofNat 64 (8 * (word + 1)) := by
    rw [regs.2.2.1, show 8 * (word + 1) = 8 + 8 * word by omega]
    exact shifted_address _ 8 word
  refine ⟨?_, counter, regs.2.2.2.2.1.trans invariant.scratch, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have zero : BitVec.ofNat 64 count = 0 ↔ count = 0 := by
      constructor
      · intro equal
        have numeric := congrArg BitVec.toNat equal
        change count % 18446744073709551616 = 0 at numeric
        omega
      · rintro rfl; rfl
    have latch := check_position_next_pc
      (checkRootWordsState false (positionSelectState oracle state) 4)
    have counted := check_position_next_counter
      (checkRootWordsState false (positionSelectState oracle state) 4)
    rw [← counted] at latch
    change (checkPositionNextState (checkRootWordsState false (positionSelectState oracle state) 4)).pc = _
    rw [latch]
    change (if (nextCheckState oracle state).getReg .x27 = 0 then (4616 : Word) else 4344) = _
    rw [counter]
    simp only [zero]
  · intro word smaller
    rw [indexAddress]
    exact invariant.indices (word + 1) (by omega)
  · intro word smaller
    rw [indexAddress, next_check_outside oracle state _ invariant.scratch
      (invariant.indexOutside (word + 1) (by omega))]
    exact invariant.indexBound (word + 1) (by omega)
  · intro word smaller
    rw [indexAddress]
    exact invariant.indexOutside (word + 1) (by omega)
  · intro word smaller
    have address : (nextCheckState oracle state).getReg .x8 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x8 + BitVec.ofNat 64 (8 * (32 + word)) := by
      rw [regs.1, show 8 * (32 + word) = 256 + 8 * word by omega]
      exact shifted_address _ 256 word
    rw [address]
    exact invariant.values (32 + word) (by omega)
  · intro word smaller
    have address : (nextCheckState oracle state).getReg .x25 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x25 + BitVec.ofNat 64 (8 * (71 + word)) := by
      rw [regs.2.1, show 8 * (71 + word) = 568 + 8 * word by omega]
      exact shifted_address _ 568 word
    rw [address]
    exact invariant.proofs (71 + word) (by omega)
  · rw [regs.2.2.2.2.2.2]
    exact invariant.capBase

attribute [local irreducible] checkRootWordsState checkPositionNextState checkPositionHash
  execute pathInstructions checkEvaluation checkLoopAccepts

set_option maxHeartbeats 1000000 in
/-- For every fixed oracle the position loop terminates. It succeeds exactly when every
position passes its cap-node comparison. At most 920 instructions, 1100 cycles, and 21
calls are used per position. -/
theorem check_loop_run (oracle : Oracle) (state : MachineState) (count : Nat)
    (bounded : count ≤ 2^24) (invariant : CheckLoopInvariant state count) (fuel : Nat) :
    (checkEvaluation oracle
      (execute (submission.image .check) (920*count+3+fuel) state false)).1.exit =
        (if checkLoopAccepts oracle count state then .success else .failure) ∧
    (checkEvaluation oracle
      (execute (submission.image .check) (920*count+3+fuel) state false)).1.cycles ≤ 1100*count+3 ∧
    (checkEvaluation oracle
      (execute (submission.image .check) (920*count+3+fuel) state false)).1.oracleCalls ≤ 21*count := by
  induction count generalizing state fuel with
  | zero =>
    have pc : state.pc = 4616 := by simpa using invariant.pc
    rw [show 920*0+3+fuel = 3+fuel by omega, check_exit state true pc, check_evaluation_pure]
    simp [checkLoopAccepts]
  | succ count ih =>
    have pc : state.pc = 4344 := by simpa using invariant.pc
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simpa using invariant.indices 0 (by omega)
    have indexSmall : (state.getMem (state.getReg .x24)).toNat < 2^24 := by
      simpa using invariant.indexBound 0 (by omega)
    have proofValid : ∀ word < 71,
        accessValid (state.getReg .x25+BitVec.ofNat 64 (8*word)) 8 = true :=
      fun word smaller => invariant.proofs word (by omega)
    have valueValid : ∀ word < 32,
        accessValid (state.getReg .x8+BitVec.ofNat 64 (8*word)) 8 = true :=
      fun word smaller => invariant.values word (by omega)
    have stepBound := (path_instruction_bounds (state.getMem (state.getReg .x24)) 17).2
    have regs := position_hash_registers oracle state
    have selectedPC : (positionSelectState oracle state).pc =
        BitVec.ofNat 64 (4096 + 4 * compareBase false) := rfl
    have selectedScratch : (positionSelectState oracle state).getReg .x21 = 256 :=
      position_select_scratch oracle state invariant.scratch
    have scratchValid : ∀ word < 4,
        accessValid ((positionSelectState oracle state).getReg .x21+BitVec.ofNat 64 (8*word)) 8 =
          true := by
      rw [selectedScratch]
      intro word smaller
      interval_cases word <;> decide
    have nodeValid : ∀ word < 4,
        accessValid ((positionSelectState oracle state).getReg (compareReg false) +
          BitVec.ofNat 64 (8*word)) 8 = true := by
      intro word smaller
      change accessValid ((positionSelectState oracle state).getReg .x22+BitVec.ofNat 64 (8*word)) 8 = true
      rw [position_select_node oracle state indexSmall, shifted_address]
      have node : (state.getMem (state.getReg .x24)).toNat / 2^17 < 128 := by omega
      have valid := invariant.capBase (4 * ((state.getMem (state.getReg .x24)).toNat / 2^17) + word)
        (by omega)
      rwa [show 8 * (4 * ((state.getMem (state.getReg .x24)).toNat / 2^17) + word) =
        32 * ((state.getMem (state.getReg .x24)).toNat / 2^17) + 8 * word by omega] at valid
    have budget : 920*(count+1)+3+fuel =
        116 + pathInstructions (state.getMem (state.getReg .x24)) 17 +
          (2+(15+(920*count+3+(fuel+(787-pathInstructions (state.getMem (state.getReg .x24)) 17))))) := by
      omega
    rw [budget, check_position_hash state pc indexValid invariant.scratch proofValid valueValid,
      evaluation_hash,
      show (checkEvaluation oracle (checkPositionHash state)).1 = positionHashState oracle state from rfl,
      check_cap_select (positionHashState oracle state) regs.1, evaluation_charge,
      show checkCapSelectState (positionHashState oracle state) = positionSelectState oracle state from rfl]
    by_cases agrees : rootWordsMatch false (positionSelectState oracle state) = true
    · have words := (root_words_match_iff false (positionSelectState oracle state)).mp agrees
      have comparedPC : (checkRootWordsState false (positionSelectState oracle state) 4).pc = 4604 :=
        (check_root_words_pc false _ selectedPC 4 (by decide) words).trans (by rfl)
      have nextInvariant := check_loop_next_invariant oracle state count (by omega) invariant
      rw [show 15+(920*count+3+(fuel+(787-pathInstructions (state.getMem (state.getReg .x24)) 17))) =
          12+(3+(920*count+3+(fuel+(787-pathInstructions (state.getMem (state.getReg .x24)) 17)))) by omega,
        check_root_matches false _ selectedPC scratchValid nodeValid words,
        evaluation_charge, check_position_next _ comparedPC, evaluation_charge,
        show checkPositionNextState (checkRootWordsState false (positionSelectState oracle state) 4) =
          nextCheckState oracle state from rfl]
      have rest := ih (nextCheckState oracle state) (by omega) nextInvariant
        (fuel+(787-pathInstructions (state.getMem (state.getReg .x24)) 17))
      simp only [Execution.charge]
      refine ⟨?_, ?_, ?_⟩
      · rw [rest.1]
        simp [checkLoopAccepts, agrees]
      · have := rest.2.1
        omega
      · have := rest.2.2
        omega
    · have words : ¬ ∀ word < 4,
          (positionSelectState oracle state).getMem ((positionSelectState oracle state).getReg .x21 +
            BitVec.ofNat 64 (8*word)) =
          (positionSelectState oracle state).getMem
            ((positionSelectState oracle state).getReg (compareReg false) + BitVec.ofNat 64 (8*word)) :=
        fun h => agrees ((root_words_match_iff false _).mpr h)
      obtain ⟨failed, run, exit, cycles, queries⟩ := check_root_rejects false _ selectedPC
        scratchValid nodeValid words
        (920*count+3+(fuel+(787-pathInstructions (state.getMem (state.getReg .x24)) 17))) false
      rw [run, check_evaluation_pure]
      have mismatch : rootWordsMatch false (positionSelectState oracle state) = false :=
        Bool.eq_false_iff.mpr agrees
      simp only [Execution.charge, exit]
      refine ⟨?_, ?_, ?_⟩
      · simp [checkLoopAccepts, mismatch]
      · omega
      · omega

/-- Buffer and control invariants right after the length gate and scratch setup. -/
structure CheckReadyInvariant (state : MachineState) (count : Nat) : Prop where
  pc : state.pc = if count = 0 then 4616 else 4164
  counter : state.getReg .x27 = BitVec.ofNat 64 count
  scratch : state.getReg .x21 = 256
  indices : ∀ word < count,
    accessValid (state.getReg .x24 + BitVec.ofNat 64 (8 * word)) 8 = true
  indexBound : ∀ word < count,
    (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * word))).toNat < 2^24
  indexOutside : ∀ word < count, ∀ i < 12,
    state.getReg .x24 + BitVec.ofNat 64 (8 * word) ≠ BitVec.ofNat 64 (256 + 8 * i)
  values : ∀ word < 32 * count,
    accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true
  proofs : ∀ word < 512 + 71 * count,
    accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true
  root : ∀ word < 4,
    accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true

theorem cap_phase_registers (oracle : Oracle) (state : MachineState) (pc : state.pc = 4164) :
    (capPhaseState oracle state).pc = 4296 ∧
    (capPhaseState oracle state).getReg .x25 = state.getReg .x25 + 4096 ∧
    (capPhaseState oracle state).getReg .x30 = state.getReg .x25 ∧
    ∀ reg, reg ∈ [Reg.x8, .x21, .x24, .x26, .x27] →
      (capPhaseState oracle state).getReg reg = state.getReg reg :=
  check_cap_phase_registers state _ pc (check_evaluation_support oracle _)

/-- After a matching cap chain, the position loop starts with its invariants. -/
theorem check_cap_loop_invariant (oracle : Oracle) (state : MachineState) (count : Nat)
    (positive : 0 < count) (invariant : CheckReadyInvariant state count)
    (pc : state.pc = 4164)
    (agrees : rootWordsMatch true (capPhaseState oracle state) = true) :
    CheckLoopInvariant (checkRootWordsState true (capPhaseState oracle state) 4) count := by
  have regs := cap_phase_registers oracle state pc
  have words := (root_words_match_iff true (capPhaseState oracle state)).mp agrees
  have keep (reg : Reg) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :=
    (check_root_words_preserves true (capPhaseState oracle state) 4 reg not6 not7).1
  have memory (address : Word) (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256+8*i)) :
      (checkRootWordsState true (capPhaseState oracle state) 4).getMem address = state.getMem address := by
    have same : (checkRootWordsState true (capPhaseState oracle state) 4).getMem address =
        (capPhaseState oracle state).getMem address :=
      congrArg (fun mem => mem address) (check_root_words_preserves true (capPhaseState oracle state) 4 .x21
        (by decide) (by decide)).2
    rw [same]
    exact cap_phase_outside oracle state address invariant.scratch outside
  have r24 : (checkRootWordsState true (capPhaseState oracle state) 4).getReg .x24 = state.getReg .x24 :=
    (keep .x24 (by decide) (by decide)).trans (regs.2.2.2 .x24 (by simp))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [if_neg (by omega)]
    exact (check_root_words_pc true (capPhaseState oracle state) (by rw [regs.1]; rfl) 4 (by decide)
      words).trans (by rfl)
  · exact ((keep .x27 (by decide) (by decide)).trans (regs.2.2.2 .x27 (by simp))).trans invariant.counter
  · exact ((keep .x21 (by decide) (by decide)).trans (regs.2.2.2 .x21 (by simp))).trans invariant.scratch
  · rw [r24]; exact invariant.indices
  · intro word smaller
    rw [r24, memory _ (invariant.indexOutside word smaller)]
    exact invariant.indexBound word smaller
  · rw [r24]; exact invariant.indexOutside
  · rw [(keep .x8 (by decide) (by decide)).trans (regs.2.2.2 .x8 (by simp))]
    exact invariant.values
  · intro word smaller
    have address : (checkRootWordsState true (capPhaseState oracle state) 4).getReg .x25 +
        BitVec.ofNat 64 (8 * word) = state.getReg .x25 + BitVec.ofNat 64 (8 * (512 + word)) := by
      rw [keep .x25 (by decide) (by decide), regs.2.1, show 8 * (512 + word) = 4096 + 8 * word by omega]
      exact shifted_address _ 4096 word
    rw [address]
    exact invariant.proofs (512 + word) (by omega)
  · intro word smaller
    rw [keep .x30 (by decide) (by decide), regs.2.2.1]
    exact invariant.proofs word (by omega)

set_option maxHeartbeats 1000000 in
/-- For every fixed oracle the checker terminates after the length gate, succeeding
exactly when the cap chain and every position pass. At most 64 + 21 calls per position. -/
theorem check_ready_run (oracle : Oracle) (state : MachineState) (count : Nat)
    (bounded : count ≤ 2^24) (invariant : CheckReadyInvariant state count) (fuel : Nat) :
    (checkEvaluation oracle
      (execute (submission.image .check) (1440+920*count+fuel) state false)).1.exit =
        (if checkReadyAccepts oracle count state then .success else .failure) ∧
    (checkEvaluation oracle
      (execute (submission.image .check) (1440+920*count+fuel) state false)).1.cycles ≤
        1100*count+1890 ∧
    (checkEvaluation oracle
      (execute (submission.image .check) (1440+920*count+fuel) state false)).1.oracleCalls ≤
        85*count := by
  by_cases empty : count = 0
  · subst count
    have pc : state.pc = 4616 := by simpa using invariant.pc
    rw [show 1440+920*0+fuel = 3+(1437+fuel) by omega, check_exit state true pc, check_evaluation_pure]
    simp [checkReadyAccepts]
  · have pc : state.pc = 4164 := by simpa [empty] using invariant.pc
    have regs := cap_phase_registers oracle state pc
    have capSource : ∀ word < 512,
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true :=
      fun word smaller => invariant.proofs word (by omega)
    rw [show 1440+920*count+fuel = 1419+(15+(920*count+3+(fuel+3))) by omega,
      check_cap_phase state pc invariant.scratch capSource, evaluation_hash,
      show (checkEvaluation oracle (checkCapLoop (checkCapSetupState state) 64)).1 =
        capPhaseState oracle state from rfl]
    have cappedPC : (capPhaseState oracle state).pc = BitVec.ofNat 64 (4096 + 4 * compareBase true) := by
      rw [regs.1]; rfl
    have scratchValid : ∀ word < 4,
        accessValid ((capPhaseState oracle state).getReg .x21+BitVec.ofNat 64 (8*word)) 8 = true := by
      rw [regs.2.2.2 .x21 (by simp), invariant.scratch]
      intro word smaller
      interval_cases word <;> decide
    have rootValid : ∀ word < 4,
        accessValid ((capPhaseState oracle state).getReg (compareReg true) +
          BitVec.ofNat 64 (8*word)) 8 = true := by
      change ∀ word < 4,
        accessValid ((capPhaseState oracle state).getReg .x26+BitVec.ofNat 64 (8*word)) 8 = true
      rw [regs.2.2.2 .x26 (by simp)]
      exact invariant.root
    by_cases agrees : rootWordsMatch true (capPhaseState oracle state) = true
    · have words := (root_words_match_iff true (capPhaseState oracle state)).mp agrees
      have loopInvariant := check_cap_loop_invariant oracle state count (by omega) invariant pc agrees
      rw [show 15+(920*count+3+(fuel+3)) = 12+(920*count+3+(fuel+6)) by omega,
        check_root_matches true _ cappedPC scratchValid rootValid words, evaluation_charge]
      have rest := check_loop_run oracle _ count bounded loopInvariant (fuel+6)
      simp only [Execution.charge]
      refine ⟨?_, ?_, ?_⟩
      · rw [rest.1]
        simp [checkReadyAccepts, empty, agrees]
      · have := rest.2.1
        omega
      · have := rest.2.2
        omega
    · have words : ¬ ∀ word < 4,
          (capPhaseState oracle state).getMem ((capPhaseState oracle state).getReg .x21 +
            BitVec.ofNat 64 (8*word)) =
          (capPhaseState oracle state).getMem
            ((capPhaseState oracle state).getReg (compareReg true) + BitVec.ofNat 64 (8*word)) :=
        fun h => agrees ((root_words_match_iff true _).mpr h)
      obtain ⟨failed, run, exit, cycles, queries⟩ := check_root_rejects true _ cappedPC
        scratchValid rootValid words (920*count+3+(fuel+3)) false
      rw [run, check_evaluation_pure]
      have mismatch : rootWordsMatch true (capPhaseState oracle state) = false :=
        Bool.eq_false_iff.mpr agrees
      simp only [Execution.charge, exit]
      refine ⟨?_, ?_, ?_⟩
      · simp [checkReadyAccepts, empty, mismatch]
      · omega
      · omega

end CommitGolfCandidate
