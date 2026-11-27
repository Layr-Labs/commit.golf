import CommitGolfCandidate.C3POpenPrepass
import CommitGolfCandidate.TwoPermutationPackedOpeningProofBytes
import CommitGolfCandidate.TwoPermutationPackedOpeningRecordRun
import CommitGolfCandidate.TwoPermutationPackedOpeningRecords
import CommitGolfCandidate.TwoPermutationPackedCapBytes

/-! # The paired opener's whole run

Word 2 still skips everything for an empty opening (the leader's `opening_empty_run`). Otherwise the
leader's first twelve setup words run (`execute_setup12`), then the pre-pass (`prePass`, one inverse
call per position), and then the leader's records, cap and exit from word 13
(`opening_records_run`), for the trapdoor `trapdoorOf s P` that the pre-pass leaves in memory. -/
namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.C3Leaves
open Prepass
open Opening (OpeningLayout SameOpeningInput sortedIndex trapdoorBase indicesBase nonceBase proofBase markBase
  RecordMarks groupsBefore machineMarks)
-- Sequential elaboration, as in C3PAdmission (the verifier builds with parallel elaboration on two CPUs).
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option pp.maxSteps 4000

/-- The trapdoor the pre-pass leaves in memory. -/
def trapdoorOf (s : Submission) (P : MachineState) : BitVec (8 * s.sizes.trapdoor) :=
  readBuffer P trapdoorBase s.sizes.trapdoor

/-- The sorted index at ordinal `j`, as a number. -/
def preIdx (positions : Positions) (j : Nat) : Nat :=
  if h : j < positions.card then (sortedIndex positions j h).val else 0

theorem read_one_word (state : MachineState) (word : Nat) :
    readBuffer state (8 * word) 8 = memoryView state word := by
  have sliced := CommitGolfCandidate.read_buffer_slice state (8 * word) 32 0 8 (by decide)
  have extracted := CommitGolfCandidate.read_digest_word state (8 * word) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero, memoryView, wordAddress] using sliced.symm.trans extracted

theorem setup12_registers (state : MachineState) (nonempty : state.getReg .x16 ≠ 0#64) :
    let after := setupPrefix state 12
    after.getReg .x20 = state.getReg .x15 ∧ after.getReg .x21 = state.getReg .x15 ∧
    after.getReg .x8 = state.getReg .x13 ∧ after.getReg .x9 = state.getReg .x12 ∧
    after.getReg .x18 = state.getReg .x16 ∧ after.getReg .x16 = state.getReg .x16 ∧
    after.getReg .x19 = BitVec.ofNat 64 LENGTH ∧
    after.getReg .x22 = state.getReg .x12 + BitVec.ofNat 64 (80 * LENGTH) ∧
    after.getReg .x23 = 1 ∧ after.getReg .x25 = state.getReg .x12 ∧
    after.getReg .x26 = BitVec.ofNat 64 markBase ∧ after.mem = state.mem := by
  simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, signExtend12, LENGTH,
    LOG_LENGTH, Opening.markBase, beq_iff_eq, nonempty, Opening.getReg_setReg, Opening.getReg_setMem, reg_zero] <;> rfl

theorem sorted_nodup_values (positions : Positions) (j j' : Nat) (hj : j < positions.card) (hj' : j' < positions.card)
    (same : (sortedIndex positions j hj).val = (sortedIndex positions j' hj').val) : j = j' := by
  have nodup := Finset.sort_nodup positions (· ≤ ·)
  have equal : sortedIndex positions j hj = sortedIndex positions j' hj' := Fin.ext same
  unfold sortedIndex at equal
  exact (List.Nodup.getElem_inj_iff nodup).mp equal

/-- The pre-pass precondition after the leader's first twelve setup words. -/
theorem pre_ready (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (positive : 0 < positions.card) :
    PreReady (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card (preIdx positions) := by
  let initial := s.initialState .opening (trapdoor, positions)
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have countValue : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have nonempty : initial.getReg .x16 ≠ 0#64 := countValue ▸ nonempty_count positions positive
  have trapPointer : initial.getReg .x12 = BitVec.ofNat 64 trapdoorBase :=
    congrArg (BitVec.ofNat 64) layout.trapdoor
  have indexPointer : initial.getReg .x13 = BitVec.ofNat 64 indicesBase :=
    congrArg (BitVec.ofNat 64) layout.indices
  obtain ⟨_, _, r8, r9, r18, r16, _, r22, _, _, _, mem⟩ := setup12_registers initial nonempty
  refine ⟨?_, r8.trans indexPointer, r9.trans trapPointer, r16.trans countValue, r18.trans countValue, ?_, ?_, ?_, ?_,
    positive, cardinal⟩
  · rw [setup_pc12 initial rfl nonempty]; rfl
  · rw [r22, trapPointer, ← BitVec.ofNat_add]
  · intro j hj
    have value := Opening.input_index s layout trapdoor positions j hj
    have address : wordAddress (IW + j) = BitVec.ofNat 64 (indicesBase + 8 * j) := by
      unfold wordAddress IW; congr 1; norm_num [indicesBase, trapdoorBase, Opening.trapdoorBytes, LENGTH, LOG_LENGTH]; omega
    have view : memoryView (setupPrefix initial 12) (IW + j) = initial.getMem (wordAddress (IW + j)) := by
      unfold memoryView; simp only [MachineState.getMem, mem]
    rw [view, address, value]
    simp only [preIdx, dif_pos hj]
    rfl
  · intro j hj
    simp only [preIdx, dif_pos hj]
    exact (sortedIndex positions j hj).isLt
  · intro j hj j' hj' same
    simp only [preIdx, dif_pos hj, dif_pos hj'] at same
    exact sorted_nodup_values positions j j' hj hj' same

/-- Input bytes past the trapdoor buffer do not depend on the trapdoor. -/
theorem input_byte_trapdoor_free (s : Submission) (layout : OpeningLayout s)
    (t t' : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (address : Nat)
    (beyond : trapdoorBase + Opening.trapdoorBytes ≤ address) :
    inputByte s .opening (t, positions) address = inputByte s .opening (t', positions) address := by
  have outside : ¬ (trapdoorBase ≤ address ∧ address < trapdoorBase + (8 * Opening.trapdoorBytes + 7) / 8) := by omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, layout.trapdoor, layout.trapdoorSize,
    outside, decide_false]

theorem initial_trapdoor_free (s : Submission) (layout : OpeningLayout s)
    (t t' : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (address : Nat)
    (beyond : trapdoorBase + Opening.trapdoorBytes ≤ address) (bounded : address < 2 ^ 63) :
    (s.initialState .opening (t, positions)).getMem (BitVec.ofNat 64 address) =
      (s.initialState .opening (t', positions)).getMem (BitVec.ofNat 64 address) := by
  rw [initial_input_word s .opening (t, positions) _ (by omega),
    initial_input_word s .opening (t', positions) _ (by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [input_byte_trapdoor_free s layout t t' positions (address + j) (by omega)]

/-- After the pre-pass, the memory on `[trapdoorBase, proofBase)` is the input memory of `trapdoorOf s P`. -/
theorem prepass_same_input (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (positive : 0 < positions.card) (ys : Nat → Sampling.Block) (P : MachineState)
    (ended : PreEnd (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card
      (preIdx positions) ys P) :
    SameOpeningInput (s.initialState .opening (trapdoorOf s P, positions)) P := by
  let initial := s.initialState .opening (trapdoor, positions)
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have len : LENGTH = 2 ^ 24 := rfl
  intro a lo hi al
  obtain ⟨w, rfl⟩ : ∃ w, a = 8 * w := ⟨a / 8, by omega⟩
  have tb : trapdoorBase = 8 * TDw := rfl
  have tbytes : Opening.trapdoorBytes = 232 * 2 ^ 24 + 4096 := by unfold Opening.trapdoorBytes; rfl
  have pb : proofBase < 8 * 2 ^ 33 := by norm_num [proofBase, indicesBase, trapdoorBase, Opening.trapdoorBytes, LENGTH, LOG_LENGTH]
  by_cases inside : 8 * w + 8 ≤ trapdoorBase + Opening.trapdoorBytes
  · have slice := Opening.input_trapdoor_slice s layout (trapdoorOf s P) positions (8 * w - trapdoorBase) 8
      (by omega)
    rw [show trapdoorBase + (8 * w - trapdoorBase) = 8 * w by omega, read_one_word] at slice
    change memoryView _ w = _ at slice
    change P.getMem (wordAddress w) = (s.initialState .opening (trapdoorOf s P, positions)).getMem (wordAddress w)
    change _ = memoryView _ w
    rw [slice, trapdoorOf, layout.trapdoorSize,
      CommitGolfCandidate.read_buffer_slice P trapdoorBase Opening.trapdoorBytes (8 * w - trapdoorBase) 8 (by omega),
      show trapdoorBase + (8 * w - trapdoorBase) = 8 * w by omega, read_one_word]
    rfl
  · have beyond : trapdoorBase + Opening.trapdoorBytes ≤ 8 * w := by
      have : Opening.trapdoorBytes % 8 = 0 := by rw [tbytes]; decide
      omega
    have iw : IW = TDw + Opening.trapdoorBytes / 8 := by rw [tbytes]; rfl
    have nwv : NW = 704643588 := rfl
    have hwv : HW = 603980292 := rfl
    have tdw : TDw = 536871428 := rfl
    have frame := ended.frame w (by omega) (Or.inr (by unfold scratchW; omega))
      (Or.inr (by unfold Lw; rw [tbytes] at beyond; omega))
      (fun j hj => by
        have := (pre_ready s layout trapdoor positions positive).idxSmall
        constructor <;> (rw [tbytes] at beyond; have := this j hj; omega))
      (fun j hj t ht => by
        have small := (pre_ready s layout trapdoor positions positive).idxSmall j hj
        have := xor_one_small _ (show preIdx positions j < 2 ^ 24 by omega)
        rw [tbytes] at beyond; omega)
    have nonempty : initial.getReg .x16 ≠ 0#64 :=
      (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, setupMem⟩ := setup12_registers initial nonempty
    change P.getMem (wordAddress w) = _
    change memoryView P w = _
    rw [frame]
    change (setupPrefix initial 12).getMem (wordAddress w) = _
    simp only [MachineState.getMem, setupMem]
    exact initial_trapdoor_free s layout trapdoor (trapdoorOf s P) positions (8 * w) beyond (by omega)

/-! ### The record boundary at word 13 -/

theorem prepass_marks (s : Submission) (layout : OpeningLayout s) (image : s.image .opening = openingImage)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (positive : 0 < positions.card)
    (ys : Nat → Sampling.Block) (P : MachineState)
    (ended : PreEnd (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card
      (preIdx positions) ys P) :
    RecordMarks positions P 0 := by
  let initial := s.initialState .opening (trapdoor, positions)
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have nonempty : initial.getReg .x16 ≠ 0#64 :=
    (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, mem12⟩ :=
    setup12_registers (s.initialState .opening (trapdoor, positions)) nonempty
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, mem13⟩ := setup_registers (s.initialState .opening (trapdoor, positions))
  intro node bounded
  have marked := initial_record_marks s layout image trapdoor positions node bounded
  have address : BitVec.ofNat 64 (markBase + 8 * node) = wordAddress (512 + node) := by
    unfold wordAddress markBase; congr 1; omega
  have hwv : HW = 603980292 := rfl
  have nwv : NW = 704643588 := rfl
  have frame := ended.frame (512 + node) (by omega) (Or.inl (by unfold scratchW; omega))
    (Or.inl (by unfold Lw; omega))
    (fun j hj => by constructor <;> omega)
    (fun j hj t ht => by omega)
  unfold Opening.machineMarks at marked ⊢
  rw [address] at marked ⊢
  change memoryView P (512 + node) = _
  rw [frame, ← marked]
  simp only [memoryView, MachineState.getMem]
  rw [mem12, mem13]

theorem prepass_boundary (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (positive : 0 < positions.card)
    (ys : Nat → Sampling.Block) (P : MachineState)
    (ended : PreEnd (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card
      (preIdx positions) ys P) :
    RecordBoundary s (trapdoorOf s P) positions P 0 := by
  let initial := s.initialState .opening (trapdoor, positions)
  have nonempty : initial.getReg .x16 ≠ 0#64 :=
    (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
  have trapPointer : initial.getReg .x12 = BitVec.ofNat 64 trapdoorBase :=
    congrArg (BitVec.ofNat 64) abi.trapdoor
  have indexPointer : initial.getReg .x13 = BitVec.ofNat 64 indicesBase :=
    congrArg (BitVec.ofNat 64) abi.indices
  have proofPointer : initial.getReg .x15 = BitVec.ofNat 64 proofBase :=
    congrArg (BitVec.ofNat 64) abi.proof
  have countValue : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  obtain ⟨r20, r21, r8, r9, r18, _, r19, r22, r23, r25, r26, _⟩ := setup12_registers initial nonempty
  have K (g : Reg) (h5 : g ≠ .x5) (h6 : g ≠ .x6) (h7 : g ≠ .x7) (h10 : g ≠ .x10) (h11 : g ≠ .x11) (h12 : g ≠ .x12)
      (h13 : g ≠ .x13) (h14 : g ≠ .x14) (h15 : g ≠ .x15) (h16 : g ≠ .x1) (h17 : g ≠ .x17) (h27 : g ≠ .x27)
      (h28 : g ≠ .x28) (h29 : g ≠ .x29) (h30 : g ≠ .x30) (h31 : g ≠ .x31) :
      P.getReg g = (setupPrefix initial 12).getReg g :=
    ended.keep g h5 h6 h7 h10 h11 h12 h13 h14 h15 h16 h17 h27 h28 h29 h30 h31
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, prepass_same_input s abi.toOpeningLayout trapdoor positions positive ys P ended,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [if_neg (by omega)]; exact ended.pc
  · rw [K .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r9, trapPointer]
  · rw [K .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r8, indexPointer]
    simp
  · rw [K .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r22, trapPointer,
      ← BitVec.ofNat_add]
    rfl
  · rw [K .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r21, proofPointer]
    simp [recordBase]
  · rw [K .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r19]
  · rw [K .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r18, countValue]
    simp
  · rw [K .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r26]
  · rw [K .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r23]; rfl
  · rw [K .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r25, trapPointer]
  · rw [ended.x27]; rfl
  · rw [K .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r20, proofPointer]

/-! ### The whole run -/

theorem prepass_pad (s : Submission) (abi : OpeningABI s) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (positive : 0 < positions.card) (ys : Nat → Sampling.Block) (P : MachineState)
    (ended : PreEnd (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card
      (preIdx positions) ys P) :
    ∀ a, proofBase ≤ a → a < MEMORY_BYTES → P.getByte (BitVec.ofNat 64 a) = 0 := by
  let initial := s.initialState .opening (trapdoor, positions)
  intro a above fit
  have nonempty : initial.getReg .x16 ≠ 0#64 :=
    (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, mem12⟩ := setup12_registers initial nonempty
  have small := (pre_ready s abi.toOpeningLayout trapdoor positions positive).idxSmall
  have pb : proofBase = 12616474720 := by norm_num [proofBase, indicesBase, trapdoorBase, Opening.trapdoorBytes, LENGTH, LOG_LENGTH]
  have mb : MEMORY_BYTES = 68719476736 := rfl
  have tbytes : Opening.trapdoorBytes = 232 * 2 ^ 24 + 4096 := by unfold Opening.trapdoorBytes; rfl
  have same : memoryView P (a / 8) = memoryView initial (a / 8) := by
    have cb := (pre_ready s abi.toOpeningLayout trapdoor positions positive).cardBound
    have hL : LENGTH = 16777216 := rfl
    have saltFrame : ∀ j < positions.card,
        a / 8 ≠ NW + 2 * preIdx positions j ∧ a / 8 ≠ NW + 2 * preIdx positions j + 1 := by
      intro j hj
      have h1 := small j hj
      unfold NW TDw
      constructor <;> omega
    have mateFrame : ∀ j < positions.card, ∀ t < 4, a / 8 ≠ HW + 4 * (preIdx positions j ^^^ 1) + t := by
      intro j hj t ht
      have h1 := small j hj
      have h2 := xor_one_small _ (show preIdx positions j < 2 ^ 24 by omega)
      unfold HW TDw
      omega
    rw [ended.frame (a / 8) (by omega) (Or.inr (by unfold scratchW; omega))
      (Or.inr (by unfold Lw; change positions.card ≤ 16777216 at cb; omega)) saltFrame mateFrame]
    simp only [memoryView, MachineState.getMem]
    exact congrFun mem12 _
  rw [TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame initial P a same]
  exact initial_padding s abi trapdoor positions a above fit

theorem prepass_count (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (positive : 0 < positions.card) (ys : Nat → Sampling.Block) (P : MachineState)
    (ended : PreEnd (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card
      (preIdx positions) ys P) :
    P.getReg .x16 = R1b.Machine.W positions.card := by
  let initial := s.initialState .opening (trapdoor, positions)
  have nonempty : initial.getReg .x16 ≠ 0#64 :=
    (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
  obtain ⟨_, _, _, _, _, r16, _, _, _, _, _, _⟩ := setup12_registers initial nonempty
  rw [ended.keep .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r16]
  rfl

def openSteps (positions : Positions) (len : Nat) : Nat := 12 + (prepassSteps positions.card + restSteps positions len)

theorem paired_fuel_fits (positions : Positions) (len : Nat) :
    openSteps positions len ≤ 17179934720 := by
  have cardinal : positions.card ≤ 16777216 := by
    have bound : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact bound
  have cap := opening_cap_cycles_bound (groupsBefore positions positions.card)
  have tail : R1b.Opening.tailSteps positions.card len ≤ 11192 := by
    unfold R1b.Opening.tailSteps; split_ifs <;> omega
  unfold openSteps prepassSteps restSteps restCycles
  omega

/-- Every reachable end of a nonempty opening: the pre-pass state `P`, then R1b's records, cap and codec
for `trapdoorOf s P`. -/
theorem paired_opening_support (s : Submission) (abi : OpeningABI s) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (positive : 0 < positions.card) (result : Execution)
    (reached : result ∈ support (s.run .opening (trapdoor, positions))) :
    ∃ (P : MachineState) (ys : Nat → Sampling.Block),
      PreEnd (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card (preIdx positions) ys P ∧
      result.exit = .success ∧
      result.cycles = 12 + (prepassCycles positions.card +
        restCost positions (proofFromTrapdoor (s := s) (trapdoorOf s P) positions).length) ∧
      result.oracleCalls = positions.card ∧ RestWire s (trapdoorOf s P) positions result.state := by
  let initial := s.initialState .opening (trapdoor, positions)
  have nonempty : initial.getReg .x16 ≠ 0#64 :=
    (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
  have ready := pre_ready s abi.toOpeningLayout trapdoor positions positive
  change result ∈ support (execute (s.image .opening) (s.steps .opening) initial true) at reached
  rw [abi.image, show s.steps .opening = 12 + (prepassSteps positions.card + (s.steps .opening - (12 + prepassSteps positions.card))) by
      have := (paired_fuel_fits positions 0).trans abi.fuel; unfold openSteps at this; omega,
    execute_setup12 initial rfl _ true nonempty, prepass_run _ _ _ ready] at reached
  simp only [bind_assoc, mem_support_bind_iff, support_pure, Set.mem_singleton_iff, pure_bind] at reached
  obtain ⟨P, hP, res, hres, rfl⟩ := reached
  obtain ⟨ys, ended⟩ := prepass_support _ _ _ ready P hP
  let len := (proofFromTrapdoor (s := s) (trapdoorOf s P) positions).length
  obtain ⟨final, run, rest⟩ := opening_rest_run (execute_records_from_step execute_record) s abi
    (trapdoorOf s P) positions positive P (prepass_boundary s abi trapdoor positions positive ys P ended)
    (prepass_marks s abi.toOpeningLayout abi.image trapdoor positions positive ys P ended)
    (prepass_pad s abi trapdoor positions positive ys P ended) (prepass_count s trapdoor positions positive ys P ended)
  have budget := (paired_fuel_fits positions len).trans abi.fuel
  rw [show s.steps .opening - (12 + prepassSteps positions.card) = restSteps positions len +
      (s.steps .opening - openSteps positions len) by unfold openSteps at budget ⊢; omega, run, support_pure,
    Set.mem_singleton_iff] at hres
  subst hres
  refine ⟨P, ys, ended, rfl, ?_, ?_, rest⟩
  · simp only [Execution.charge] <;> omega
  · simp only [Execution.charge] <;> omega

/-- The run against a fixed oracle: one end state, the honest pre-pass answers. -/
theorem paired_opening_fixed (s : Submission) (abi : OpeningABI s) (oracle : Oracle)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (positive : 0 < positions.card) :
    ∃ (P : MachineState) (result : Execution),
      fixedOracleRun oracle (s.run .opening (trapdoor, positions)) = pure result ∧
      PreEnd (setupPrefix (s.initialState .opening (trapdoor, positions)) 12) positions.card (preIdx positions)
        (honestYs oracle (memoryView (setupPrefix (s.initialState .opening (trapdoor, positions)) 12))
          (preIdx positions)) P ∧
      result.exit = .success ∧ RestWire s (trapdoorOf s P) positions result.state := by
  let initial := s.initialState .opening (trapdoor, positions)
  have nonempty : initial.getReg .x16 ≠ 0#64 :=
    (show initial.getReg .x16 = BitVec.ofNat 64 positions.card from rfl) ▸ nonempty_count positions positive
  have ready := pre_ready s abi.toOpeningLayout trapdoor positions positive
  obtain ⟨P, fixed, ended⟩ := prepass_fixed oracle _ _ _ ready
  let len := (proofFromTrapdoor (s := s) (trapdoorOf s P) positions).length
  obtain ⟨final, run, rest⟩ := opening_rest_run (execute_records_from_step execute_record) s abi
    (trapdoorOf s P) positions positive P (prepass_boundary s abi trapdoor positions positive _ P ended)
    (prepass_marks s abi.toOpeningLayout abi.image trapdoor positions positive _ P ended)
    (prepass_pad s abi trapdoor positions positive _ P ended) (prepass_count s trapdoor positions positive _ P ended)
  have budget := (paired_fuel_fits positions len).trans abi.fuel
  refine ⟨P, ((⟨.success, final, restCost positions len, 0⟩ : Execution).charge (prepassCycles positions.card)
    positions.card).charge 12 0, ?_, ended, rfl, rest⟩
  change fixedOracleRun oracle (execute (s.image .opening) (s.steps .opening) initial true) = _
  rw [abi.image, show s.steps .opening = 12 + (prepassSteps positions.card + (restSteps positions len +
      (s.steps .opening - openSteps positions len))) by unfold openSteps at budget ⊢; omega,
    execute_setup12 initial rfl _ true nonempty, prepass_run _ _ _ ready]
  simp only [bind_assoc]
  rw [fixed_oracle_run_bind, fixed, pure_bind, run]
  simp only [pure_bind, fixed_oracle_run_pure]
  rfl

end TwoPermutationPrototype.PackedOpening
