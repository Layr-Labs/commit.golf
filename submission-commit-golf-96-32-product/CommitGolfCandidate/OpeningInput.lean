import CommitGolfCandidate.Opening
import CommitGolf.Statements

/-! Connect the opening image's loop proofs to the trusted input loader. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem index_word (index : Index) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (BitVec.ofNat 8 (index.val / 2 ^ (8 * j))).toNat * 2 ^ (8 * j)) =
        BitVec.ofNat 64 index.val := by
  congr 1
  have bounded : index.val < 16777216 := index.isLt
  norm_num [Finset.sum_range_succ, BitVec.toNat_ofNat]
  omega

/-- Reading an aligned serialized index recovers exactly the corresponding element
of the sorted position set, for every trapdoor and position set. -/
theorem opening_input_index (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (offset : Nat) (bounded : offset < positions.card) :
    (submission.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (submission.layout.indices + 8 * offset)) =
        BitVec.ofNat 64 ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val := by
  let byteAt := fun address : Nat =>
    match (submission.inputBuffers .opening (trapdoor, positions)).find?
        (fun b => decide (b.address ≤ address ∧ address < b.address + b.length)) with
    | some b => b.byteAt (address - b.address)
    | none => if dataBase (submission.image .opening) ≤ address then
        (submission.image .opening).data[address - dataBase (submission.image .opening)]?.getD 0
      else 0
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have addressNat : (BitVec.ofNat 64 (submission.layout.indices + 8 * offset)).toNat =
      submission.layout.indices + 8 * offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH,
      LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
    omega
  change BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
    (byteAt ((BitVec.ofNat 64 (submission.layout.indices + 8 * offset)).toNat + j)).toNat *
      2 ^ (8 * j)) = _
  rw [addressNat]
  have bytes (j : Nat) (hj : j < 8) :
      byteAt (submission.layout.indices + 8 * offset + j) =
        BitVec.ofNat 8 (((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j)) := by
    have before : ¬ (submission.layout.trapdoor ≤ submission.layout.indices + 8 * offset + j ∧
        submission.layout.indices + 8 * offset + j <
          submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8) := by
      norm_num [submission, candidate, layout, sizes, trapdoorBytes, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES]
      omega
    have inside : submission.layout.indices ≤ submission.layout.indices + 8 * offset + j ∧
        submission.layout.indices + 8 * offset + j <
          submission.layout.indices + 8 * (positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      omega
    have selected : (submission.inputBuffers .opening (trapdoor, positions)).find?
        (fun b => decide (b.address ≤ submission.layout.indices + 8 * offset + j ∧
          submission.layout.indices + 8 * offset + j < b.address + b.length)) =
          some (positionsBuffer submission.layout.indices positions) := by
      simp only [Submission.inputBuffers, List.find?_cons, fixedBuffer]
      simp only [before, decide_false]
      simp only [positionsBuffer, inside]
      rfl
    simp only [byteAt, selected, positionsBuffer]
    have quotient : (submission.layout.indices + 8 * offset + j - submission.layout.indices) / 8 = offset := by omega
    have remainder : (submission.layout.indices + 8 * offset + j - submission.layout.indices) % 8 = j := by omega
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using bounded)]
  calc
    _ = BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
        (BitVec.ofNat 8 (((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j))).toNat * 2 ^ (8 * j)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [bytes j (Finset.mem_range.mp hj)]
    _ = _ := index_word _

/-- Exact opening cycle count as a function of the number of opened positions. -/
def openingCycles (count : Nat) : Nat :=
  if count = 0 then 32
  else if count = BATCH then 40614
  else 35 + 425 * count

/-- Exact final machine state of the submitted opening image on any valid ABI input. -/
def openingFinalState (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) : MachineState :=
  let ready := openingInitializedState (submission.initialState .opening (trapdoor, positions))
  if positions.card = 0 then
    openingExitState (openingDoneGateState ready)
  else if positions.card = BATCH then
    let afterPos := (openingPositionState 17)^[BATCH] (openingDepthState ready)
    openingCapExitState (openingCapPairState^[64] (openingCapSetupState (openingDoneGateState afterPos)))
  else
    let afterPos := (openingPositionState 24)^[positions.card] (openingDepthState ready)
    openingExitState (openingDoneGateState afterPos)

/-- Exact result of the submitted opening image on any valid ABI input. -/
def openingResult (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) : Execution :=
  ⟨.success, openingFinalState trapdoor positions, openingCycles positions.card, 0⟩

private theorem card_word_eq_iff (positions : Positions) (target : Nat) (targetSmall : target < 2^64) :
    (BitVec.ofNat 64 positions.card = BitVec.ofNat 64 target) ↔ positions.card = target := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have small : positions.card < 2^64 := by norm_num [LENGTH, LOG_LENGTH] at cardinal; omega
  constructor
  · intro h
    have n := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt targetSmall] at n
    exact n
  · intro h; rw [h]

private theorem opening_init_pc (state : MachineState) :
    (openingInitializedState state).pc = if state.getReg .x16 = 0 then 4328 else 4176 := rfl

private theorem opening_done_gate_pc (state : MachineState) :
    (openingDoneGateState state).pc = if state.getReg .x16 = 128 then 4336 else 4472 := rfl

private theorem opening_done_gate_x16 (state : MachineState) :
    (openingDoneGateState state).getReg .x16 = state.getReg .x16 := rfl

private theorem opening_done_gate_x9 (state : MachineState) :
    (openingDoneGateState state).getReg .x9 = state.getReg .x9 := rfl

private theorem opening_done_gate_x25 (state : MachineState) :
    (openingDoneGateState state).getReg .x25 = state.getReg .x25 := rfl

attribute [local irreducible] openingPositionState openingCapPairState openingInitializedState
  openingDepthState openingDoneGateState openingExitState openingCapExitState

set_option maxRecDepth 4096 in
private theorem opening_ready_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute (submission.image .opening)
      ((if positions.card = 0 then 9
        else if positions.card = BATCH then 40594
        else 425 * positions.card + 12) + fuel)
      (openingInitializedState (submission.initialState .opening (trapdoor, positions))) true =
        pure ⟨.success, openingFinalState trapdoor positions, openingCycles positions.card - 20, 0⟩ := by
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have initialCount : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have regs := opening_setup_registers initial
  have counter : ready.getReg .x27 = BitVec.ofNat 64 positions.card := regs.2.2.2.1
  have origCount : ready.getReg .x16 = BitVec.ofNat 64 positions.card := regs.2.2.2.2.2.2.1
  have heap : ready.getReg .x9 = BitVec.ofNat 64 submission.layout.trapdoor := regs.1
  have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 submission.layout.indices := regs.2.1
  have outputPointer : ready.getReg .x25 = BitVec.ofNat 64 submission.layout.proof := regs.2.2.1
  have leaves : ready.getReg .x19 = 16777216 := regs.2.2.2.2.1
  have salts : ready.getReg .x18 = BitVec.ofNat 64 (submission.layout.trapdoor + 1610612736) := by
    rw [regs.2.2.2.2.2.1]
    change BitVec.ofNat 64 submission.layout.trapdoor + BitVec.ofNat 64 1610612736 = _
    rw [BitVec.ofNat_add]
  have memory (address : Word) : ready.getMem address = initial.getMem address :=
    congrFun regs.2.2.2.2.2.2.2 address
  have readyPCeq : ready.pc = if initial.getReg .x16 = 0 then 4328 else 4176 :=
    opening_init_pc initial
  by_cases empty : positions.card = 0
  · simp only [empty, ↓reduceIte, openingFinalState, openingCycles]
    have readyPC : ready.pc = 4328 := by
      rw [readyPCeq, initialCount, empty]; rfl
    have not128 : ready.getReg .x16 ≠ 128 := by rw [origCount, empty]; decide
    have gatePC : (openingDoneGateState ready).pc = 4472 := by
      rw [opening_done_gate_pc, if_neg not128]
    rw [show 9 + fuel = 2 + (7 + fuel) by omega,
      opening_done_gate ready readyPC, opening_exit _ gatePC]
    simp [Execution.charge, ready, initial]
  · simp only [empty, ↓reduceIte]
    have nonzero : BitVec.ofNat 64 positions.card ≠ (0 : Word) := by
      intro h; exact empty ((card_word_eq_iff positions 0 (by decide)).mp h)
    have readyPC : ready.pc = 4176 := by
      rw [readyPCeq, initialCount, if_neg nonzero]
    let dReady := openingDepthState ready
    have dHeap : dReady.getReg .x9 = BitVec.ofNat 64 submission.layout.trapdoor :=
      (opening_depth_register ready .x9 (by decide) (by decide)).trans heap
    have dIdx : dReady.getReg .x24 = BitVec.ofNat 64 submission.layout.indices :=
      (opening_depth_register ready .x24 (by decide) (by decide)).trans indexPointer
    have dOut : dReady.getReg .x25 = BitVec.ofNat 64 submission.layout.proof :=
      (opening_depth_register ready .x25 (by decide) (by decide)).trans outputPointer
    have dCnt : dReady.getReg .x27 = BitVec.ofNat 64 positions.card :=
      (opening_depth_register ready .x27 (by decide) (by decide)).trans counter
    have dOrig : dReady.getReg .x16 = BitVec.ofNat 64 positions.card :=
      (opening_depth_register ready .x16 (by decide) (by decide)).trans origCount
    have dLeaves : dReady.getReg .x19 = 16777216 :=
      (opening_depth_register ready .x19 (by decide) (by decide)).trans leaves
    have dSalts : dReady.getReg .x18 = BitVec.ofNat 64 (submission.layout.trapdoor + 1610612736) :=
      (opening_depth_register ready .x18 (by decide) (by decide)).trans salts
    have dMem (address : Word) : dReady.getMem address = initial.getMem address :=
      (congrFun (opening_depth_memory ready) address).trans (memory address)
    have dIndices : ∀ offset < positions.card,
        (dReady.getMem (dReady.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
      intro offset bounded
      rw [dIdx, ← BitVec.ofNat_add, dMem, opening_input_index trapdoor positions offset bounded]
      have indexBound : ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val < 2 ^ 24 :=
        ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).isLt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact indexBound
    have dIndexSpace : (dReady.getReg .x24).toNat + 8 * positions.card ≤ (dReady.getReg .x25).toNat := by
      rw [dIdx, dOut]
      norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
      norm_num [LENGTH, LOG_LENGTH] at cardinal; omega
    have dIndexAligned : (dReady.getReg .x24).toNat % 8 = 0 := by rw [dIdx]; decide
    have dSaltBound : (dReady.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES := by rw [dSalts]; decide
    have dSaltAligned : (dReady.getReg .x18).toNat % 8 = 0 := by rw [dSalts]; decide
    have dHeapBound : (dReady.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES := by rw [dHeap]; decide
    have dHeapAligned : (dReady.getReg .x9).toNat % 8 = 0 := by rw [dHeap]; decide
    have dOutAligned : (dReady.getReg .x25).toNat % 8 = 0 := by rw [dOut]; decide
    by_cases cap : positions.card = BATCH
    · simp only [cap, ↓reduceIte, openingFinalState, openingCycles, empty]
      have eq128 : ready.getReg .x27 = 128 := by rw [counter, cap]; rfl
      have depthVal : dReady.getReg .x30 = BitVec.ofNat 64 17 := by
        rw [opening_depth_value, eq128]; rfl
      have dOutBound : (dReady.getReg .x25).toNat + (32 + 32 * 17) * BATCH ≤ MEMORY_BYTES := by
        rw [dOut]; decide
      let afterPos := (openingPositionState 17)^[BATCH] dReady
      have posPC : afterPos.pc = 4328 :=
        (opening_positions_finished 17 BATCH (by decide) dReady (by rw [dCnt, cap])).1
      have posOrig : afterPos.getReg .x16 = 128 := by
        rw [opening_positions_preserves_count, dOrig, cap]; rfl
      have posHeap : afterPos.getReg .x9 = BitVec.ofNat 64 submission.layout.trapdoor :=
        (opening_positions_preserves_heap 17 BATCH dReady).trans dHeap
      have posOut : afterPos.getReg .x25 = BitVec.ofNat 64 (submission.layout.proof + 73728) := by
        rw [opening_positions_output 17 BATCH dReady, dOut, ← BitVec.ofNat_add]; rfl
      let gated := openingDoneGateState afterPos
      have gatePC : gated.pc = 4336 := by rw [opening_done_gate_pc, posOrig]; rfl
      have gateHeap : gated.getReg .x9 = BitVec.ofNat 64 submission.layout.trapdoor :=
        (opening_done_gate_x9 afterPos).trans posHeap
      have gateOut : gated.getReg .x25 = BitVec.ofNat 64 (submission.layout.proof + 73728) :=
        (opening_done_gate_x25 afterPos).trans posOut
      let capSetup := openingCapSetupState gated
      have capRegs := opening_cap_setup_registers gated gatePC
      have capSrc : capSetup.getReg .x23 = BitVec.ofNat 64 (submission.layout.trapdoor + 6144) := by
        rw [capRegs.2.1, gateHeap]; rfl
      have capDst : capSetup.getReg .x25 = BitVec.ofNat 64 (submission.layout.proof + 73728) :=
        capRegs.2.2.1.trans gateOut
      have capEndPC : (openingCapPairState^[64] capSetup).pc = 4440 :=
        (opening_cap_finished 64 (by decide) (by decide) capSetup capRegs.2.2.2.1).1
      have sel := opening_depth_select ready readyPC (306 * 128 + (2 + (4 + (22 * 64 + (8 + fuel))))) true
      simp only [eq128, ↓reduceIte] at sel
      rw [show 40594 + fuel = 4 + (306 * 128 + (2 + (4 + (22 * 64 + (8 + fuel))))) by omega, sel]
      change (execute (submission.image .opening)
          ((17 + 17 * 17) * BATCH + (2 + (4 + (22 * 64 + (8 + fuel))))) dReady true >>=
            fun result => pure (result.charge 4 0)) = _
      rw [opening_positions_loop 17 (by decide) (by decide) BATCH (by decide) dReady
          (by rw [dCnt, cap]) depthVal (fun _ => opening_depth_pc ready)
          (by simpa [cap] using dIndices) (by simpa [cap] using dIndexSpace) dIndexAligned
          dLeaves dSaltBound dSaltAligned dHeapBound dHeapAligned dOutBound dOutAligned,
        opening_done_gate afterPos posPC,
        opening_cap_setup gated gatePC,
        opening_cap_loop 64 (by decide) capSetup capRegs.2.2.2.1 (fun _ => capRegs.1)
          (by rw [capSrc]; decide) (by rw [capSrc]; decide)
          (by rw [capDst]; decide) (by rw [capDst]; decide),
        opening_cap_exit _ capEndPC]
      simp [Execution.charge, afterPos, gated, capSetup, dReady, ready, initial, BATCH]
    · simp only [cap, ↓reduceIte, openingFinalState, openingCycles, empty]
      have ne128 : ready.getReg .x27 ≠ 128 := by
        rw [counter]; intro h; exact cap ((card_word_eq_iff positions 128 (by decide)).mp h)
      have depthVal : dReady.getReg .x30 = BitVec.ofNat 64 24 := by
        rw [opening_depth_value, if_neg ne128]; rfl
      have dOutBound : (dReady.getReg .x25).toNat + (32 + 32 * 24) * positions.card ≤ MEMORY_BYTES := by
        rw [dOut]
        norm_num [submission, candidate, layout, trapdoorBytes, MEMORY_BYTES,
          LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
        norm_num [LENGTH, LOG_LENGTH] at cardinal; omega
      let afterPos := (openingPositionState 24)^[positions.card] dReady
      have posPC : afterPos.pc = 4328 :=
        (opening_positions_finished 24 positions.card (by omega) dReady dCnt).1
      have posNot128 : afterPos.getReg .x16 ≠ 128 := by
        rw [opening_positions_preserves_count, dOrig]
        intro h; exact cap ((card_word_eq_iff positions 128 (by decide)).mp h)
      have gatePC : (openingDoneGateState afterPos).pc = 4472 := by
        rw [opening_done_gate_pc, if_neg posNot128]
      have sel := opening_depth_select ready readyPC (425 * positions.card + (2 + (7 + fuel))) true
      simp only [ne128, ↓reduceIte] at sel
      rw [show 425 * positions.card + 12 + fuel = 3 + (425 * positions.card + (2 + (7 + fuel))) by omega, sel]
      change (execute (submission.image .opening)
          ((17 + 17 * 24) * positions.card + (2 + (7 + fuel))) dReady true >>=
            fun result => pure (result.charge 3 0)) = _
      rw [opening_positions_loop 24 (by decide) (by decide) positions.card cardinal dReady
          dCnt depthVal (fun _ => opening_depth_pc ready)
          dIndices dIndexSpace dIndexAligned
          dLeaves dSaltBound dSaltAligned dHeapBound dHeapAligned dOutBound dOutAligned,
        opening_done_gate afterPos posPC,
        opening_exit _ gatePC]
      simp only [pure_bind, Execution.charge, Nat.add_zero]
      congr 2; omega

private theorem opening_execution_extra (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute (submission.image .opening)
      (20 + ((if positions.card = 0 then 9
        else if positions.card = BATCH then 40594
        else 425 * positions.card + 12) + fuel))
      (submission.initialState .opening (trapdoor, positions)) true =
        pure (openingResult trapdoor positions) := by
  rw [opening_setup _ rfl, opening_ready_execution]
  simp only [pure_bind, Execution.charge, openingResult]
  congr 2
  unfold openingCycles
  by_cases h0 : positions.card = 0
  · simp [h0]
  · by_cases h1 : positions.card = BATCH
    · simp [h0, h1, BATCH]
    · simp only [h0, h1, ↓reduceIte]; omega

private theorem run_opening_eq_execute (candidate : Submission)
    (input : Input candidate.sizes .opening) :
    candidate.run .opening input = execute (candidate.image .opening) (candidate.steps .opening)
      (candidate.initialState .opening input) true := rfl

set_option maxRecDepth 4096 in
/-- Every actual opening input succeeds, with exact cycle and query counts. -/
theorem opening_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    submission.run .opening (trapdoor, positions) = pure (openingResult trapdoor positions) := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  let need := 20 + (if positions.card = 0 then 9
    else if positions.card = BATCH then 40594
    else 425 * positions.card + 12)
  have fit : need ≤ submission.steps .opening := by
    have cardLe : positions.card ≤ 16777216 := cardinal
    have stepsVal : submission.steps .opening = 13421773824 := rfl
    dsimp only [need]
    rw [stepsVal]
    by_cases h0 : positions.card = 0
    · simp [h0]
    · by_cases h1 : positions.card = BATCH
      · simp [h0, h1, BATCH]
      · simp only [h0, h1, ↓reduceIte]; omega
  have steps : submission.steps .opening =
      20 + ((if positions.card = 0 then 9
        else if positions.card = BATCH then 40594
        else 425 * positions.card + 12) + (submission.steps .opening - need)) := by
    dsimp [need] at fit ⊢; omega
  exact (run_opening_eq_execute submission (trapdoor, positions)).trans
    ((congrArg (fun fuel => execute (submission.image .opening) fuel
      (submission.initialState .opening (trapdoor, positions)) true) steps).trans
        (opening_execution_extra trapdoor positions _))

/-- The machine returns `77824` proof bytes when `k = BATCH`, and `800 * k` otherwise. -/
theorem opening_result_length (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    ((openingResult trapdoor positions).state.getReg .x11).toNat =
      openingProofBytes positions.card := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  change ((openingFinalState trapdoor positions).getReg .x11).toNat = _
  unfold openingFinalState openingProofBytes
  by_cases empty : positions.card = 0
  · simp only [empty, ↓reduceIte, BATCH, show (0 : Nat) ≠ 128 by decide]
    apply opening_exit_length _ 0 (by decide)
    rw [opening_done_gate_x16, (opening_setup_registers _).2.2.2.2.2.2.1]
    change BitVec.ofNat 64 positions.card = 0; rw [empty]; rfl
  · simp only [empty, ↓reduceIte]
    by_cases cap : positions.card = BATCH
    · simp only [cap, ↓reduceIte]
      exact opening_cap_exit_length _
    · simp only [cap, ↓reduceIte]
      apply opening_exit_length _ positions.card cardinal
      rw [opening_done_gate_x16, opening_positions_preserves_count,
        opening_depth_register _ .x16 (by decide) (by decide),
        (opening_setup_registers _).2.2.2.2.2.2.1]
      rfl

theorem opening_proof_bytes_le (k : Nat) : openingProofBytes k ≤ 800 * k := by
  unfold openingProofBytes
  split <;> simp_all [BATCH]

/-- No opening is rejected or cut off, and its reported length fits the declared buffer. -/
theorem opening_result_succeeded (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    submission.openingSucceeded (openingResult trapdoor positions) = true := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  simp only [Submission.openingSucceeded, opening_result_length]
  change (true && decide (openingProofBytes positions.card ≤ submission.sizes.proof)) = true
  simp only [Bool.true_and, decide_eq_true_eq]
  have le800 := opening_proof_bytes_le positions.card
  change openingProofBytes positions.card ≤ 800 * LENGTH
  omega

/-- The scored batch's actual opening cost, proved for arbitrary trapdoors and sets. -/
theorem opening_batch_cycles (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (batch : positions.card = BATCH) :
    (openingResult trapdoor positions).cycles = 40614 := by
  simp [openingResult, openingCycles, batch, BATCH]

/-- Actual transmitted proof length, after the success and buffer-capacity checks. -/
theorem opening_proof_length (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    (submission.readProof (openingResult trapdoor positions)).length =
      openingProofBytes positions.card := by
  simp [Submission.readProof, opening_result_succeeded, opening_result_length]

private theorem scheme_opening_eq_map (candidate : Submission)
    (trapdoor : BitVec (8 * candidate.sizes.trapdoor)) (positions : Positions) :
    candidate.scheme.opening trapdoor positions =
      candidate.readProof <$> candidate.run .opening (trapdoor, positions) := rfl

/-- The scheme's opening operation is exactly the successful machine output. -/
theorem opening_scheme_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    submission.scheme.opening trapdoor positions =
      pure (submission.readProof (openingResult trapdoor positions)) := by
  rw [scheme_opening_eq_map, opening_execution]
  simp

private theorem oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

/-- Opening termination in the same probabilistic form required by the certificate. -/
theorem opening_termination (oracle : Oracle)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$> (oracle.run (submission.run .opening (trapdoor, positions))))) = 1 := by
  rw [opening_execution, oracle_run_pure]
  simp [openingResult]

/-- The certificate's proof-size requirement follows from the actual machine image. -/
theorem submission_proof_size : submission.scheme.ProofSize 77824 := by
  intro oracle message positions batch
  unfold Scheme.honest
  apply le_antisymm (prEvent_le_one _)
  apply le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _)
  rintro ⟨⟨root, trapdoor⟩, calls⟩ _
  dsimp only
  rw [opening_scheme_execution trapdoor positions, oracle_run_pure]
  simp [opening_proof_length trapdoor positions, openingProofBytes, batch]

/-- Exact resources for a scored opening: 40,614 cycles, zero queries, 77,824 proof bytes. -/
theorem opening_batch_resources (oracle : Oracle)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions)
    (batch : positions.card = BATCH) :
    (prEvent ((fun result => result.1.cycles = 40614 ∧ result.2 = 0 ∧
      (submission.readProof result.1).length = 77824) <$> (oracle.run (submission.run .opening (trapdoor, positions))))) = 1 := by
  rw [opening_execution, oracle_run_pure]
  simp [opening_batch_cycles trapdoor positions batch, opening_proof_length trapdoor positions,
    openingProofBytes, batch]

end CommitGolfCandidate
