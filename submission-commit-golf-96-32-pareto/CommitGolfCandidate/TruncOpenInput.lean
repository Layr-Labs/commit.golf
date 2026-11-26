import CommitGolfCandidate.PairInput

import CommitGolfCandidate.TruncOpenSuffix

import CommitGolfCandidate.TruncCheckFetch

namespace CommitGolfCandidate.Trunc.Open

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap

set_option maxRecDepth 18000

set_option maxHeartbeats 1600000

private theorem packedLengthNat (s : MachineState) : ((Wire.packedEnd s).getReg .x11).toNat=68096 := by rw [Wire.packedLength];rfl

def proofBytes (k : Nat) : Nat := if k = BATCH then 68096 else 784*k

def openingCycles (count : Nat) : Nat :=
  if count = 0 then 32
  else if count = BATCH then 109773
  else 35 + 421 * count

def openingFinalState (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) : MachineState :=
  let ready := openingInitializedState (Trunc.submission.initialState .opening (trapdoor, positions))
  if positions.card = 0 then
    openingExitState (openingDoneGateState ready)
  else if positions.card = BATCH then
    let afterPos := (openingPositionState 16)^[BATCH] (pair_openingDepthState ready)
    Wire.packedEnd (suffixState (openingCapPairState^[64] (openingCapSetupState (openingDoneGateState afterPos))))
  else
    let afterPos := (openingPositionState 24)^[positions.card] (pair_openingDepthState ready)
    openingExitState (openingDoneGateState afterPos)

def openingResult (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) : Execution :=
  ⟨.success, openingFinalState trapdoor positions, openingCycles positions.card, 0⟩

theorem card_word_eq_iff (positions : Positions) (target : Nat) (targetSmall : target < 2^64) :
    (BitVec.ofNat 64 positions.card = BitVec.ofNat 64 target) ↔ positions.card = target := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have small : positions.card < 2^64 := by norm_num [LENGTH, LOG_LENGTH] at cardinal; omega
  constructor
  · intro h
    have n := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt targetSmall] at n
    exact n
  · intro h; rw [h]

theorem opening_init_pc (state : MachineState) :
    (openingInitializedState state).pc = if state.getReg .x16 = 0 then 4312 else 4176 := rfl

theorem opening_done_gate_pc (state : MachineState) :
    (openingDoneGateState state).pc = if state.getReg .x16 = 128 then 4320 else 4456 := rfl

theorem opening_done_gate_x16 (state : MachineState) :
    (openingDoneGateState state).getReg .x16 = state.getReg .x16 := rfl

theorem opening_done_gate_x9 (state : MachineState) :
    (openingDoneGateState state).getReg .x9 = state.getReg .x9 := rfl

theorem opening_done_gate_x25 (state : MachineState) :
    (openingDoneGateState state).getReg .x25 = state.getReg .x25 := rfl

attribute [local irreducible] openingPositionState openingInitializedState openingCapPairState pair_openingDepthState Wire.packedEnd suffixState

theorem opening_ready_execution (law : Wire.PackRun) (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute (Trunc.submission.image .opening)
      ((if positions.card = 0 then 9
        else if positions.card = BATCH then 109753
        else 421 * positions.card + 12) + fuel)
      (openingInitializedState (Trunc.submission.initialState .opening (trapdoor, positions))) true =
        pure ⟨.success, openingFinalState trapdoor positions, openingCycles positions.card - 20, 0⟩ := by
  let initial := Trunc.submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have initialCount : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have regs := opening_setup_registers initial
  have counter : ready.getReg .x27 = BitVec.ofNat 64 positions.card := regs.2.2.2.1
  have origCount : ready.getReg .x16 = BitVec.ofNat 64 positions.card := regs.2.2.2.2.2.2.1
  have heap : ready.getReg .x9 = BitVec.ofNat 64 Trunc.submission.layout.trapdoor := regs.1
  have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 Trunc.submission.layout.indices := regs.2.1
  have outputPointer : ready.getReg .x25 = BitVec.ofNat 64 Trunc.submission.layout.proof := regs.2.2.1
  have leaves : ready.getReg .x19 = 16777216 := regs.2.2.2.2.1
  have salts : ready.getReg .x18 = BitVec.ofNat 64 (Trunc.submission.layout.trapdoor + 1610612736) := by
    rw [regs.2.2.2.2.2.1]
    change BitVec.ofNat 64 Trunc.submission.layout.trapdoor + BitVec.ofNat 64 1610612736 = _
    rw [BitVec.ofNat_add]
  have memory (address : Word) : ready.getMem address = initial.getMem address :=
    congrFun regs.2.2.2.2.2.2.2 address
  have readyPCeq : ready.pc = if initial.getReg .x16 = 0 then 4312 else 4176 :=
    opening_init_pc initial
  by_cases empty : positions.card = 0
  · simp only [empty, ↓reduceIte, openingFinalState, openingCycles]
    have readyPC : ready.pc = 4312 := by
      rw [readyPCeq, initialCount, empty]; rfl
    have not128 : ready.getReg .x16 ≠ 128 := by rw [origCount, empty]; decide
    have gatePC : (openingDoneGateState ready).pc = 4456 := by
      rw [opening_done_gate_pc, if_neg not128]
    rw [show 9 + fuel = 2 + (7 + fuel) by omega,
      pair_opening_done_gate ready readyPC, pair_opening_exit _ gatePC]
    simp [Execution.charge, ready, initial]
  · simp only [empty, ↓reduceIte]
    have nonzero : BitVec.ofNat 64 positions.card ≠ (0 : Word) := by
      intro h; exact empty ((card_word_eq_iff positions 0 (by decide)).mp h)
    have readyPC : ready.pc = 4176 := by
      rw [readyPCeq, initialCount, if_neg nonzero]
    let dReady := pair_openingDepthState ready
    have dHeap : dReady.getReg .x9 = BitVec.ofNat 64 Trunc.submission.layout.trapdoor :=
      (pair_opening_depth_register ready .x9 (by decide) (by decide)).trans heap
    have dIdx : dReady.getReg .x24 = BitVec.ofNat 64 Trunc.submission.layout.indices :=
      (pair_opening_depth_register ready .x24 (by decide) (by decide)).trans indexPointer
    have dOut : dReady.getReg .x25 = BitVec.ofNat 64 Trunc.submission.layout.proof :=
      (pair_opening_depth_register ready .x25 (by decide) (by decide)).trans outputPointer
    have dCnt : dReady.getReg .x27 = BitVec.ofNat 64 positions.card :=
      (pair_opening_depth_register ready .x27 (by decide) (by decide)).trans counter
    have dOrig : dReady.getReg .x16 = BitVec.ofNat 64 positions.card :=
      (pair_opening_depth_register ready .x16 (by decide) (by decide)).trans origCount
    have dLeaves : dReady.getReg .x19 = 16777216 :=
      (pair_opening_depth_register ready .x19 (by decide) (by decide)).trans leaves
    have dSalts : dReady.getReg .x18 = BitVec.ofNat 64 (Trunc.submission.layout.trapdoor + 1610612736) :=
      (pair_opening_depth_register ready .x18 (by decide) (by decide)).trans salts
    have dMem (address : Word) : dReady.getMem address = initial.getMem address :=
      (congrFun (pair_opening_depth_memory ready) address).trans (memory address)
    have dIndices : ∀ offset < positions.card,
        (dReady.getMem (dReady.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
      intro offset bounded
      rw [dIdx, ← BitVec.ofNat_add, dMem]
      change ((CommitGolfCandidate.submission.initialState .opening (trapdoor, positions)).getMem
        (BitVec.ofNat 64 (CommitGolfCandidate.submission.layout.indices + 8*offset))).toNat < 2^24
      rw [opening_input_index trapdoor positions offset bounded]
      have indexBound : ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val < 2 ^ 24 :=
        ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).isLt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact indexBound
    have dIndexSpace : (dReady.getReg .x24).toNat + 8 * positions.card ≤ (dReady.getReg .x25).toNat := by
      rw [dIdx, dOut]
      norm_num [Trunc.submission, PairCap.submission, CommitGolfCandidate.submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
      norm_num [LENGTH, LOG_LENGTH] at cardinal; omega
    have dIndexAligned : (dReady.getReg .x24).toNat % 8 = 0 := by rw [dIdx]; decide
    have dSaltBound : (dReady.getReg .x18).toNat + 2 ^ 28 ≤ MEMORY_BYTES := by rw [dSalts]; decide
    have dSaltAligned : (dReady.getReg .x18).toNat % 8 = 0 := by rw [dSalts]; decide
    have dHeapBound : (dReady.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES := by rw [dHeap]; decide
    have dHeapAligned : (dReady.getReg .x9).toNat % 8 = 0 := by rw [dHeap]; decide
    have dOutAligned : (dReady.getReg .x25).toNat % 8 = 0 := by rw [dOut]; decide
    by_cases cap : positions.card = BATCH
    · simp only [cap, ↓reduceIte, openingFinalState, openingCycles, empty]
      have eq128 : ready.getReg .x27 = 128 := by rw [counter, cap]; rfl
      have depthVal : dReady.getReg .x30 = BitVec.ofNat 64 16 := by
        rw [pair_opening_depth_value, eq128]; rfl
      have dOutBound : (dReady.getReg .x25).toNat + (16 + 32 * 16) * BATCH ≤ MEMORY_BYTES := by
        rw [dOut]; decide
      let afterPos := (openingPositionState 16)^[BATCH] dReady
      have posPC : afterPos.pc = 4312 :=
        (opening_positions_finished 16 BATCH (by decide) dReady (by rw [dCnt, cap])).1
      have posOrig : afterPos.getReg .x16 = 128 := by
        rw [opening_positions_preserves_count, dOrig, cap]; rfl
      have posHeap : afterPos.getReg .x9 = BitVec.ofNat 64 Trunc.submission.layout.trapdoor :=
        (opening_positions_preserves_heap 16 BATCH dReady).trans dHeap
      have posOut : afterPos.getReg .x25 = BitVec.ofNat 64 (Trunc.submission.layout.proof + 67584) := by
        rw [opening_positions_output 16 BATCH dReady, dOut, ← BitVec.ofNat_add]; rfl
      let gated := openingDoneGateState afterPos
      have gatePC : gated.pc = 4320 := by rw [opening_done_gate_pc, posOrig]; rfl
      have gateHeap : gated.getReg .x9 = BitVec.ofNat 64 Trunc.submission.layout.trapdoor :=
        (opening_done_gate_x9 afterPos).trans posHeap
      have gateOut : gated.getReg .x25 = BitVec.ofNat 64 (Trunc.submission.layout.proof + 67584) :=
        (opening_done_gate_x25 afterPos).trans posOut
      let capSetup := openingCapSetupState gated
      have capRegs := opening_cap_setup_registers gated gatePC
      have capSrc : capSetup.getReg .x23 = BitVec.ofNat 64 (Trunc.submission.layout.trapdoor + 6144) := by
        rw [capRegs.2.1, gateHeap]; rfl
      have capDst : capSetup.getReg .x25 = BitVec.ofNat 64 (Trunc.submission.layout.proof + 67584) :=
        capRegs.2.2.1.trans gateOut
      have capEndPC : (openingCapPairState^[64] capSetup).pc = 4424 :=
        (opening_cap_finished 64 (by decide) (by decide) capSetup capRegs.2.2.2.1).1
      have sel := pair_opening_depth_select ready readyPC (285 * 128 + (2 + (4 + (22 * 64 + (71855 + fuel))))) true
      simp only [eq128, ↓reduceIte] at sel
      rw [show 109753 + fuel = 4 + (285 * 128 + (2 + (4 + (22 * 64 + (71855 + fuel))))) by omega, sel]
      change (execute (Trunc.submission.image .opening)
          ((13 + 17 * 16) * BATCH + (2 + (4 + (22 * 64 + (71855 + fuel))))) dReady true >>=
            fun result => pure (result.charge 4 0)) = _
      rw [pair_opening_positions_loop 16 (by decide) (by decide) BATCH (by decide) dReady
          (by rw [dCnt, cap]) depthVal (fun _ => pair_opening_depth_pc ready)
          (by simpa [cap] using dIndices) (by simpa [cap] using dIndexSpace) dIndexAligned
          dLeaves dSaltBound dSaltAligned dHeapBound dHeapAligned dOutBound dOutAligned,
        pair_opening_done_gate afterPos posPC,
        pair_opening_cap_setup gated gatePC,
        pair_opening_cap_loop 64 (by decide) capSetup capRegs.2.2.2.1 (fun _ => capRegs.1)
          (by rw [capSrc]; decide) (by rw [capSrc]; decide)
          (by rw [capDst]; decide) (by rw [capDst]; decide),
        suffixRun law _ capEndPC]
      simp [Execution.charge, afterPos, gated, capSetup, dReady, ready, initial, BATCH]
    · simp only [cap, ↓reduceIte, openingFinalState, openingCycles, empty]
      have ne128 : ready.getReg .x27 ≠ 128 := by
        rw [counter]; intro h; exact cap ((card_word_eq_iff positions 128 (by decide)).mp h)
      have depthVal : dReady.getReg .x30 = BitVec.ofNat 64 24 := by
        rw [pair_opening_depth_value, if_neg ne128]; rfl
      have dOutBound : (dReady.getReg .x25).toNat + (16 + 32 * 24) * positions.card ≤ MEMORY_BYTES := by
        rw [dOut]
        norm_num [Trunc.submission, PairCap.submission, CommitGolfCandidate.submission, candidate, layout, trapdoorBytes, MEMORY_BYTES,
          LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
        norm_num [LENGTH, LOG_LENGTH] at cardinal; omega
      let afterPos := (openingPositionState 24)^[positions.card] dReady
      have posPC : afterPos.pc = 4312 :=
        (opening_positions_finished 24 positions.card (by omega) dReady dCnt).1
      have posNot128 : afterPos.getReg .x16 ≠ 128 := by
        rw [opening_positions_preserves_count, dOrig]
        intro h; exact cap ((card_word_eq_iff positions 128 (by decide)).mp h)
      have gatePC : (openingDoneGateState afterPos).pc = 4456 := by
        rw [opening_done_gate_pc, if_neg posNot128]
      have sel := pair_opening_depth_select ready readyPC (421 * positions.card + (2 + (7 + fuel))) true
      simp only [ne128, ↓reduceIte] at sel
      rw [show 421 * positions.card + 12 + fuel = 3 + (421 * positions.card + (2 + (7 + fuel))) by omega, sel]
      change (execute (Trunc.submission.image .opening)
          ((13 + 17 * 24) * positions.card + (2 + (7 + fuel))) dReady true >>=
            fun result => pure (result.charge 3 0)) = _
      rw [pair_opening_positions_loop 24 (by decide) (by decide) positions.card cardinal dReady
          dCnt depthVal (fun _ => pair_opening_depth_pc ready)
          dIndices dIndexSpace dIndexAligned
          dLeaves dSaltBound dSaltAligned dHeapBound dHeapAligned dOutBound dOutAligned,
        pair_opening_done_gate afterPos posPC,
        pair_opening_exit _ gatePC]
      simp only [pure_bind, Execution.charge, Nat.add_zero]
      congr 2; omega

theorem opening_execution_extra (law : Wire.PackRun) (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute (Trunc.submission.image .opening)
      (20 + ((if positions.card = 0 then 9
        else if positions.card = BATCH then 109753
        else 421 * positions.card + 12) + fuel))
      (Trunc.submission.initialState .opening (trapdoor, positions)) true =
        pure (openingResult trapdoor positions) := by
  rw [pair_opening_setup _ rfl, opening_ready_execution law]
  simp only [pure_bind, Execution.charge, openingResult]
  congr 2
  unfold openingCycles
  by_cases h0 : positions.card = 0
  · simp [h0]
  · by_cases h1 : positions.card = BATCH
    · simp [h0, h1, BATCH]
    · simp only [h0, h1, ↓reduceIte]; omega

theorem run_opening_eq_execute (candidate : Submission)
    (input : Input candidate.sizes .opening) :
    candidate.run .opening input = execute (candidate.image .opening) (candidate.steps .opening)
      (candidate.initialState .opening input) true := rfl

theorem opening_execution (law : Wire.PackRun) (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) :
    Trunc.submission.run .opening (trapdoor, positions) = pure (openingResult trapdoor positions) := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  let need := 20 + (if positions.card = 0 then 9
    else if positions.card = BATCH then 109753
    else 421 * positions.card + 12)
  have fit : need ≤ Trunc.submission.steps .opening := by
    have cardLe : positions.card ≤ 16777216 := cardinal
    have stepsVal : Trunc.submission.steps .opening = 13421773824 := rfl
    dsimp only [need]
    rw [stepsVal]
    by_cases h0 : positions.card = 0
    · simp [h0]
    · by_cases h1 : positions.card = BATCH
      · simp [h0, h1, BATCH]
      · simp only [h0, h1, ↓reduceIte]; omega
  have steps : Trunc.submission.steps .opening =
      20 + ((if positions.card = 0 then 9
        else if positions.card = BATCH then 109753
        else 421 * positions.card + 12) + (Trunc.submission.steps .opening - need)) := by
    dsimp [need] at fit ⊢; omega
  exact (run_opening_eq_execute Trunc.submission (trapdoor, positions)).trans
    ((congrArg (fun fuel => execute (Trunc.submission.image .opening) fuel
      (Trunc.submission.initialState .opening (trapdoor, positions)) true) steps).trans
        (opening_execution_extra law trapdoor positions _))



theorem opening_result_length (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) :
    ((openingResult trapdoor positions).state.getReg .x11).toNat =
      proofBytes positions.card := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  change ((openingFinalState trapdoor positions).getReg .x11).toNat = _
  unfold openingFinalState proofBytes
  by_cases empty : positions.card = 0
  · simp only [empty, ↓reduceIte, BATCH, show (0 : Nat) ≠ 128 by decide]
    apply opening_exit_length _ 0 (by decide)
    rw [opening_done_gate_x16, (opening_setup_registers _).2.2.2.2.2.2.1]
    change BitVec.ofNat 64 positions.card = 0; rw [empty]; rfl
  · simp only [empty, ↓reduceIte]
    by_cases cap : positions.card = BATCH
    · simp only [cap, ↓reduceIte]
      exact packedLengthNat _
    · simp only [cap, ↓reduceIte]
      apply opening_exit_length _ positions.card cardinal
      rw [opening_done_gate_x16, opening_positions_preserves_count,
        pair_opening_depth_register _ .x16 (by decide) (by decide),
        (opening_setup_registers _).2.2.2.2.2.2.1]
      rfl

theorem opening_proof_bytes_le (k : Nat) : proofBytes k ≤ 784 * k := by
  unfold proofBytes
  split <;> simp_all [BATCH]

theorem opening_result_succeeded (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) :
    Trunc.submission.openingSucceeded (openingResult trapdoor positions) = true := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  simp only [Submission.openingSucceeded, opening_result_length]
  change (true && decide (proofBytes positions.card ≤ Trunc.submission.sizes.proof)) = true
  simp only [Bool.true_and, decide_eq_true_eq]
  have le784 := opening_proof_bytes_le positions.card
  change proofBytes positions.card ≤ 784 * LENGTH
  omega

theorem opening_batch_cycles (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) (batch : positions.card = BATCH) :
    (openingResult trapdoor positions).cycles = 109773 := by
  simp [openingResult, openingCycles, batch, BATCH]

theorem opening_proof_length (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) :
    (Trunc.submission.readProof (openingResult trapdoor positions)).length =
      proofBytes positions.card := by
  simp [Submission.readProof, opening_result_succeeded, opening_result_length]

theorem scheme_opening_eq_map (candidate : Submission)
    (trapdoor : BitVec (8 * candidate.sizes.trapdoor)) (positions : Positions) :
    candidate.scheme.opening trapdoor positions =
      candidate.readProof <$> candidate.run .opening (trapdoor, positions) := rfl

theorem opening_scheme_execution (law : Wire.PackRun) (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor))
    (positions : Positions) :
    Trunc.submission.scheme.opening trapdoor positions =
      pure (Trunc.submission.readProof (openingResult trapdoor positions)) := by
  rw [scheme_opening_eq_map, opening_execution law]
  simp

theorem oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

theorem opening_termination (law : Wire.PackRun) (oracle : Oracle)
    (trapdoor : BitVec (8 * Trunc.submission.sizes.trapdoor)) (positions : Positions) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$> (oracle.run (Trunc.submission.run .opening (trapdoor, positions))))) = 1 := by
  rw [opening_execution law, oracle_run_pure]
  simp [openingResult]

theorem submission_proof_size (law : Wire.PackRun) : Trunc.submission.scheme.ProofSize 68096 := by
  intro oracle message positions batch
  unfold Scheme.honest
  apply le_antisymm (prEvent_le_one _)
  apply le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _)
  rintro ⟨⟨root, trapdoor⟩, calls⟩ _
  dsimp only
  rw [opening_scheme_execution law trapdoor positions, oracle_run_pure]
  simp [opening_proof_length trapdoor positions, proofBytes, batch]

end CommitGolfCandidate.Trunc.Open
