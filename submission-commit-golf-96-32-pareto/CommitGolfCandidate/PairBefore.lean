import CommitGolfCandidate.PairInput
import CommitGolfCandidate.OpeningOutput
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
def beforeState (trapdoor : BitVec (8*submission.sizes.trapdoor)) (positions : Positions) :=
  let ready := openingInitializedState (submission.initialState .opening (trapdoor, positions))
  let d := pair_openingDepthState ready
  let records := (openingPositionState 16)^[BATCH] d
  openingCapPairState^[64] (openingCapSetupState (openingDoneGateState records))

private theorem opening_exit_memory (state : MachineState) :
    (openingExitState state).mem = state.mem := rfl

private theorem opening_done_gate_memory (state : MachineState) :
    (openingDoneGateState state).mem = state.mem := rfl

private theorem opening_done_gate_pc (state : MachineState) :
    (openingDoneGateState state).pc = if state.getReg .x16 = 128 then 4320 else 4456 := rfl

private theorem opening_done_gate_x9 (state : MachineState) :
    (openingDoneGateState state).getReg .x9 = state.getReg .x9 := rfl

private theorem opening_done_gate_x25 (state : MachineState) :
    (openingDoneGateState state).getReg .x25 = state.getReg .x25 := rfl

private theorem initial_heap (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    (program.initialState .opening (trapdoor, positions)).getReg .x12 =
      BitVec.ofNat 64 program.layout.trapdoor := rfl

private theorem initial_indices (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    (program.initialState .opening (trapdoor, positions)).getReg .x13 =
      BitVec.ofNat 64 program.layout.indices := rfl

private theorem initial_output (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    (program.initialState .opening (trapdoor, positions)).getReg .x15 =
      BitVec.ofNat 64 program.layout.proof := rfl

attribute [local irreducible] openingPositionState openingInitializedState pair_openingDepthState
  openingCapPairState openingDoneGateState openingCapSetupState openingExitState
  openingCapExitState Nat.iterate

private theorem setup_data_records (committed : MachineState) (positions : Positions) (pathDepth : Nat)
    (depthBound : pathDepth ≤ 24) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    let dReady := pair_openingDepthState (openingInitializedState (submission.initialState .opening (trapdoor, positions)))
    ∀ ordinal < positions.card,
      readBuffer ((openingPositionState pathDepth)^[positions.card] dReady)
        (submission.layout.proof+(16+32*pathDepth)*ordinal) 16 =
          readBuffer committed (5905584160+16*openingIndex positions ordinal) 16 ∧
      ∀ level < pathDepth,
        readBuffer ((openingPositionState pathDepth)^[positions.card] dReady)
          (submission.layout.proof+(16+32*pathDepth)*ordinal+16+32*level) 32 =
            readBuffer committed
              (4294971424+heapOffset (((LENGTH+openingIndex positions ordinal)/2^level) ^^^ 1)) 32 := by
  let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  let dReady := pair_openingDepthState ready
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have cardinalSmall : positions.card ≤ 16777216 := cardinal
  have regs := opening_setup_registers initial
  have heap : dReady.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (pair_opening_depth_register ready .x9 (by decide) (by decide)).trans
      (regs.1.trans (initial_heap submission trapdoor positions))
  have indices : dReady.getReg .x24 = BitVec.ofNat 64 6442455072 :=
    (pair_opening_depth_register ready .x24 (by decide) (by decide)).trans
      (regs.2.1.trans (initial_indices submission trapdoor positions))
  have output : dReady.getReg .x25 = BitVec.ofNat 64 10871640096 :=
    (pair_opening_depth_register ready .x25 (by decide) (by decide)).trans
      (regs.2.2.1.trans (initial_output submission trapdoor positions))
  have leaves : dReady.getReg .x19 = BitVec.ofNat 64 LENGTH :=
    (pair_opening_depth_register ready .x19 (by decide) (by decide)).trans regs.2.2.2.2.1
  have salts : dReady.getReg .x18 = BitVec.ofNat 64 5905584160 := by
    rw [pair_opening_depth_register ready .x18 (by decide) (by decide), regs.2.2.2.2.2.1,
      initial_heap submission trapdoor positions]; rfl
  have memory : dReady.mem = initial.mem :=
    (pair_opening_depth_memory ready).trans regs.2.2.2.2.2.2.2
  have indexData (ordinal : Nat) (present : ordinal < positions.card) :
      dReady.getMem (BitVec.ofNat 64 (6442455072+8*ordinal)) =
        BitVec.ofNat 64 (openingIndex positions ordinal) := by
    rw [show dReady.getMem = initial.getMem from congrArg (fun mem address => mem address) memory]
    change (CommitGolfCandidate.submission.initialState .opening (trapdoor, positions)).getMem _ = _
    exact (opening_input_index trapdoor positions ordinal present).trans (by
      simp only [openingIndex, dif_pos present])
  have heapData (slot : Nat) (inside : slot < 2^25) :
      readBuffer dReady (4294971424+heapOffset slot) 32 =
        readBuffer committed (4294971424+heapOffset slot) 32 := by
    rw [read_buffer_memory_congr _ _ memory]
    have within := heap_offset_bound slot (2^24) (by omega)
    exact opening_input_roundtrip committed positions (heapOffset slot) (by
      change heapOffset slot+32 ≤ 2147483648; omega)
  have saltData (index : Nat) (inside : index < LENGTH) :
      readBuffer dReady (5905584160+16*index) 16 = readBuffer committed (5905584160+16*index) 16 := by
    have small : index < 16777216 := inside
    rw [read_buffer_memory_congr _ _ memory]
    have result := opening_input_roundtrip_salt committed positions (1610612736+16*index) (by
      change 1610612736+16*index+16 ≤ 2147483648; omega)
    change readBuffer initial (4294971424+(1610612736+16*index)) 16 =
      readBuffer committed (4294971424+(1610612736+16*index)) 16 at result
    simpa only [← Nat.add_assoc] using result
  have outBound : 10871640096 + (16 + 32 * pathDepth) * positions.card ≤ MEMORY_BYTES := by
    have : (16 + 32 * pathDepth) * positions.card ≤ 784 * positions.card :=
      Nat.mul_le_mul_right _ (by omega)
    change 10871640096 + _ ≤ 2^36; omega
  exact opening_all_records pathDepth dReady
    (fun slot => readBuffer committed (4294971424+heapOffset slot) 32)
    (fun index => readBuffer committed (5905584160+16*index) 16)
    (openingIndex positions) 4294971424 5905584160 6442455072 10871640096 positions.card
    heap salts leaves indices output (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) outBound
    indexData (fun ordinal _ => opening_index_bound positions ordinal) heapData saltData


theorem beforePayload (committed : MachineState) (positions : Positions)
    (batch : positions.card = BATCH) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    (∀ ordinal < BATCH,
      readBuffer (beforeState trapdoor positions)
        (submission.layout.proof+528*ordinal) 16 =
          readBuffer committed (5905584160+16*openingIndex positions ordinal) 16 ∧
      ∀ level < 16,
        readBuffer (beforeState trapdoor positions)
          (submission.layout.proof+528*ordinal+16+32*level) 32 =
            readBuffer committed
              (4294971424+heapOffset (((LENGTH+openingIndex positions ordinal)/2^level) ^^^ 1)) 32) ∧
    (∀ slot < 128,
      readBuffer (beforeState trapdoor positions)
        (submission.layout.proof+67584+32*slot) 32 =
          readBuffer committed (4294971424+heapOffset (128+slot)) 32) := by
  dsimp only
  let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  let dReady := pair_openingDepthState ready
  let afterPos := (openingPositionState 16)^[BATCH] dReady
  let gated := openingDoneGateState afterPos
  let capSetup := openingCapSetupState gated
  have nonempty : positions.card ≠ 0 := by rw [batch]; decide
  have finalMem : (beforeState trapdoor positions).mem =
      (openingCapPairState^[64] capSetup).mem := by
    rfl
  have regs := opening_setup_registers initial
  have dHeap : dReady.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (pair_opening_depth_register ready .x9 (by decide) (by decide)).trans
      (regs.1.trans (initial_heap submission trapdoor positions))
  have dOut : dReady.getReg .x25 = BitVec.ofNat 64 10871640096 :=
    (pair_opening_depth_register ready .x25 (by decide) (by decide)).trans
      (regs.2.2.1.trans (initial_output submission trapdoor positions))
  have dCnt : dReady.getReg .x27 = BitVec.ofNat 64 BATCH := by
    rw [pair_opening_depth_register ready .x27 (by decide) (by decide), regs.2.2.2.1, ← batch]; rfl
  have dOrig : dReady.getReg .x16 = BitVec.ofNat 64 BATCH := by
    rw [pair_opening_depth_register ready .x16 (by decide) (by decide), regs.2.2.2.2.2.2.1, ← batch]; rfl
  have posPC : afterPos.pc = 4312 :=
    (opening_positions_finished 16 BATCH (by decide) dReady dCnt).1
  have posOrig : afterPos.getReg .x16 = 128 := by
    rw [opening_positions_preserves_count, dOrig]; rfl
  have gatePC : gated.pc = 4320 := by rw [opening_done_gate_pc, posOrig]; rfl
  have posHeap : afterPos.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (opening_positions_preserves_heap 16 BATCH dReady).trans dHeap
  have posOut : afterPos.getReg .x25 = BitVec.ofNat 64 (10871640096 + 67584) := by
    rw [opening_positions_output 16 BATCH dReady, dOut, ← BitVec.ofNat_add]; rfl
  have capRegs := opening_cap_setup_registers gated gatePC
  have capSrc : capSetup.getReg .x23 = BitVec.ofNat 64 (4294971424 + 6144) := by
    rw [capRegs.2.1, opening_done_gate_x9, posHeap]; rfl
  have capDst : capSetup.getReg .x25 = BitVec.ofNat 64 (10871640096 + 67584) := by
    rw [capRegs.2.2.1, opening_done_gate_x25, posOut]
  have capMem : capSetup.mem = afterPos.mem :=
    capRegs.2.2.2.2.trans (opening_done_gate_memory afterPos)
  have dMem : dReady.mem = initial.mem :=
    (pair_opening_depth_memory ready).trans regs.2.2.2.2.2.2.2
  have posPreserves (addr : Nat) (aligned : addr % 8 = 0) (below : addr + 32 ≤ 10871640096) :
      readBuffer afterPos addr 32 = readBuffer initial addr 32 := by
    apply read_digest_congr _ _ _ aligned
    intro i hi
    have h := opening_positions_memory_below 16 BATCH dReady (BitVec.ofNat 64 (addr + 8 * i))
      (by rw [dOut]; decide)
      (by rw [dOut, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : addr + 8 * i < 2^64),
            Nat.mod_eq_of_lt (by decide : 10871640096 < 2^64)]; omega)
    exact h.trans (congrFun dMem _)
  have capPreservesSalt (addr : Nat) (aligned : addr % 8 = 0) (below : addr + 16 ≤ 10871640096 + 67584) :
      readBuffer (openingCapPairState^[64] capSetup) addr 16 = readBuffer afterPos addr 16 := by
    rw [← read_buffer_memory_congr _ _ capMem]
    apply read_salt_congr _ _ _ aligned
    intro i hi
    apply opening_cap_loop_memory_below 64 capSetup
    · rw [capDst]; decide
    · rw [capDst, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : addr + 8 * i < 2^64),
        Nat.mod_eq_of_lt (by decide : 10871640096 + 67584 < 2^64)]
      omega
  have capPreserves (addr : Nat) (aligned : addr % 8 = 0) (below : addr + 32 ≤ 10871640096 + 67584) :
      readBuffer (openingCapPairState^[64] capSetup) addr 32 = readBuffer afterPos addr 32 := by
    rw [← read_buffer_memory_congr _ _ capMem]
    apply read_digest_congr _ _ _ aligned
    intro i hi
    apply opening_cap_loop_memory_below 64 capSetup
    · rw [capDst]; decide
    · rw [capDst, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : addr + 8 * i < 2^64),
        Nat.mod_eq_of_lt (by decide : 10871640096 + 67584 < 2^64)]
      omega
  constructor
  · intro ordinal present
    have recs := setup_data_records committed positions 16 (by decide) ordinal (by rw [batch]; exact present)
    have eqAfter : ((openingPositionState 16)^[positions.card] dReady) = afterPos := by rw [batch]
    rw [eqAfter] at recs
    constructor
    · rw [read_buffer_memory_congr _ _ finalMem]
      change readBuffer (openingCapPairState^[64] capSetup) (10871640096 + 528 * ordinal) 16 = _
      rw [capPreservesSalt _ (by omega) (by change _ ≤ 10871640096 + 67584; change ordinal < 128 at present; omega)]
      exact recs.1
    · intro level inside
      rw [read_buffer_memory_congr _ _ finalMem]
      change readBuffer (openingCapPairState^[64] capSetup) (10871640096 + 528 * ordinal + 16 + 32 * level) 32 = _
      rw [capPreserves _ (by omega) (by change _ ≤ 10871640096 + 67584; change ordinal < 128 at present; omega)]
      exact recs.2 level inside
  · have capData (p : Nat) (hp : p < 64) :
        readBuffer capSetup (4294971424 + 6144 + 96 * p) 32 =
          readBuffer committed (4294971424 + heapOffset (128 + 2 * p)) 32 ∧
        readBuffer capSetup (4294971424 + 6144 + 96 * p + 32) 32 =
          readBuffer committed (4294971424 + heapOffset (128 + (2 * p + 1))) 32 := by
      have offE : 6144 + 96 * p = heapOffset (128 + 2 * p) := by unfold heapOffset; omega
      have offO : 6144 + 96 * p + 32 = heapOffset (128 + (2 * p + 1)) := by unfold heapOffset; omega
      constructor
      · rw [read_buffer_memory_congr _ _ capMem, posPreserves _ (by omega) (by omega),
          Nat.add_assoc, offE]
        exact opening_input_roundtrip committed positions _ (by unfold heapOffset; change _ ≤ 2147483648; omega)
      · rw [read_buffer_memory_congr _ _ capMem, posPreserves _ (by omega) (by omega),
          show 4294971424 + 6144 + 96 * p + 32 = 4294971424 + (6144 + 96 * p + 32) by omega, offO]
        exact opening_input_roundtrip committed positions _ (by unfold heapOffset; change _ ≤ 2147483648; omega)
    have copied := opening_cap_records capSetup
      (fun s => readBuffer committed (4294971424 + heapOffset (128 + s)) 32)
      (4294971424 + 6144) (10871640096 + 67584) 64
      capSrc capDst (by decide) (by decide) (by decide) (by decide) capData
    intro slot hs
    rw [read_buffer_memory_congr _ _ finalMem]
    have pair := copied (slot / 2) (by omega)
    by_cases even : slot % 2 = 0
    · have eqSlot : 2 * (slot / 2) = slot := by omega
      have eqAddr : submission.layout.proof + 67584 + 32 * slot =
          10871640096 + 67584 + 64 * (slot / 2) := by
        change 10871640096 + 67584 + 32 * slot = _; omega
      have h := pair.1
      rw [eqSlot] at h
      rw [eqAddr]
      exact h
    · have eqSlot : 2 * (slot / 2) + 1 = slot := by omega
      have eqAddr : submission.layout.proof + 67584 + 32 * slot =
          10871640096 + 67584 + 64 * (slot / 2) + 32 := by
        change 10871640096 + 67584 + 32 * slot = _; omega
      have h := pair.2
      rw [eqSlot] at h
      rw [eqAddr]
      exact h



/-- Writes to records and the initial cap are entirely above the loaded indices and heap. -/
theorem beforeWord (committed : MachineState) (positions : Positions) (batch : positions.card = BATCH)
    (address : Word) (low : address.toNat < 10871640096) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    (beforeState trapdoor positions).getMem address =
      (submission.initialState .opening (trapdoor, positions)).getMem address := by
  dsimp only
  let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  let dReady := pair_openingDepthState ready
  let afterPos := (openingPositionState 16)^[BATCH] dReady
  let gated := openingDoneGateState afterPos
  let capSetup := openingCapSetupState gated
  have nonempty : positions.card ≠ 0 := by rw [batch]; decide
  have regs := opening_setup_registers initial
  have dHeap : dReady.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (pair_opening_depth_register ready .x9 (by decide) (by decide)).trans
      (regs.1.trans (initial_heap submission trapdoor positions))
  have dOut : dReady.getReg .x25 = BitVec.ofNat 64 10871640096 :=
    (pair_opening_depth_register ready .x25 (by decide) (by decide)).trans
      (regs.2.2.1.trans (initial_output submission trapdoor positions))
  have dCnt : dReady.getReg .x27 = BitVec.ofNat 64 BATCH := by
    rw [pair_opening_depth_register ready .x27 (by decide) (by decide), regs.2.2.2.1, ← batch]; rfl
  have dOrig : dReady.getReg .x16 = BitVec.ofNat 64 BATCH := by
    rw [pair_opening_depth_register ready .x16 (by decide) (by decide), regs.2.2.2.2.2.2.1, ← batch]; rfl
  have posPC : afterPos.pc = 4312 :=
    (opening_positions_finished 16 BATCH (by decide) dReady dCnt).1
  have posOrig : afterPos.getReg .x16 = 128 := by
    rw [opening_positions_preserves_count, dOrig]; rfl
  have gatePC : gated.pc = 4320 := by rw [opening_done_gate_pc, posOrig]; rfl
  have posHeap : afterPos.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (opening_positions_preserves_heap 16 BATCH dReady).trans dHeap
  have posOut : afterPos.getReg .x25 = BitVec.ofNat 64 (10871640096 + 67584) := by
    rw [opening_positions_output 16 BATCH dReady, dOut, ← BitVec.ofNat_add]; rfl
  have capRegs := opening_cap_setup_registers gated gatePC
  have capSrc : capSetup.getReg .x23 = BitVec.ofNat 64 (4294971424 + 6144) := by
    rw [capRegs.2.1, opening_done_gate_x9, posHeap]; rfl
  have capDst : capSetup.getReg .x25 = BitVec.ofNat 64 (10871640096 + 67584) := by
    rw [capRegs.2.2.1, opening_done_gate_x25, posOut]
  have capMem : capSetup.mem = afterPos.mem :=
    capRegs.2.2.2.2.trans (opening_done_gate_memory afterPos)
  have dMem : dReady.mem = initial.mem :=
    (pair_opening_depth_memory ready).trans regs.2.2.2.2.2.2.2

  change ((openingCapPairState^[64]) capSetup).getMem address = _
  rw [opening_cap_loop_memory_below 64 _ _ (by rw [capDst]; decide) (by
    rw [capDst]; change address.toNat < 10871707680; omega)]
  change capSetup.mem address = _
  rw [capMem]
  change ((openingPositionState 16)^[BATCH] dReady).getMem address = _
  rw [opening_positions_memory_below _ _ _ _ (by rw [dOut]; decide) (by rw [dOut]; exact low)]
  exact congrFun dMem address

theorem batchState (td : BitVec (8*submission.sizes.trapdoor)) (ps : Positions)
    (batch : ps.card = BATCH) :
    (openingResult td ps).state = suffixState (beforeState td ps) := by
  change openingFinalState td ps = _
  unfold openingFinalState
  rw [if_neg (by rw [batch]; decide), if_pos batch]
  rfl

end CommitGolfCandidate.PairCap
