import CommitGolfCandidate.PentaOpenPass
import CommitGolfCandidate.QuadOpeningABI

/-! Penta counter-mode opener header (words 0..2, displaced setup words 479..487,
prefix configuration 488..497, key copy 498..503): 28 steps and 28 cycles from the
opening input to the prefix loop's `Ready` state at word 504. -/
namespace TwoPermutationPrototype.PentaOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open QOpening (OpeningLayout trapdoorBase proofBase indicesBase nonceBase input_trapdoor_slice)
open QuadOpening (lui_salts tableBase initial_registers)
set_option maxRecDepth 24000
set_option maxHeartbeats 2500000

def layoutJumpRows : List Row :=
  [(0, .ADDI .x21 .x15 0), (1, .BEQ .x16 .x0 588), (2, .JAL .x0 1908)]

def layoutSetupA : List Row :=
  [(479, .ADDI .x8 .x13 0), (480, .ADDI .x9 .x12 0), (481, .ADDI .x18 .x16 0),
   (482, .LUI .x22 442369), (483, .ADD .x22 .x9 .x22)]

def layoutSetupB : List Row :=
  [(484, .ADDI .x19 .x0 5), (485, .ADDI .x23 .x0 368),
   (486, .LUI .x26 1), (487, .ADDI .x26 .x26 636)]

def layoutRows : List Row := layoutJumpRows ++ layoutSetupA ++ layoutSetupB

def configA : List Row :=
  [(488, .ADDI .x10 .x0 1024), (489, .ADDI .x12 .x0 1536), (490, .ADDI .x11 .x0 200),
   (491, .ADDI .x13 .x0 1), (492, .ADDI .x5 .x0 0)]

def configB : List Row :=
  [(493, .ADDI .x14 .x8 0), (494, .ADDI .x17 .x18 0),
   (495, .LUI .x24 1), (496, .ADDI .x27 .x24 (-1)), (497, .ADDI .x29 .x0 11)]

def configRows : List Row := configA ++ configB

def keyRows : List Row :=
  [(498, .LD .x31 .x22 8), (499, .SD .x10 .x31 8),
   (500, .LD .x31 .x22 16), (501, .SD .x10 .x31 16),
   (502, .LD .x31 .x22 24), (503, .SD .x10 .x31 24)]

def headerRows : List Row := layoutRows ++ configRows ++ keyRows
def header (s : MachineState) : MachineState := walkRows s headerRows

def keyOf {n : Nat} (td : BitVec n) : BitVec 192 := td.extractLsb' (8 * 1811943432) 192

theorem nested_slice {n outer width start len : Nat} (word : BitVec n) (bound : start + len ≤ width) :
    (word.extractLsb' outer width).extractLsb' start len = word.extractLsb' (outer + start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have mid : start + j < width := by omega
  simp [mid, hj, Nat.add_assoc]

theorem header_fetch : presentRows headerRows := by
  have raw : ∀ i : Fin headerRows.length, let r := headerRows[i]; r.1 < 527 ∧
    (openingImage.code[r.1]?).bind QOpening.decodeBase = some r.2 := by decide +kernel
  intro p hp; obtain ⟨j, hj, eq⟩ := List.mem_iff_getElem.mp hp; subst p
  intro st pc; exact prefix_fetch_base _ _ _ (raw ⟨j, hj⟩).1 pc (raw ⟨j, hj⟩).2

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

private theorem walk_join (s : MachineState) (xs ys : List Row) :
    walkRows s (xs ++ ys) = walkRows (walkRows s xs) ys := by
  simp only [walkRows, List.foldl_append]

private theorem setReg_x0_eq (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl
private theorem setPC_setPC (s : MachineState) (a b : Word) : (s.setPC a).setPC b = s.setPC b := rfl

private theorem layout_jump_step (s : MachineState) (pc : s.pc = address 0) (nz : s.getReg .x16 ≠ 0#64) :
    legal layoutJumpRows s ∧ walkRows s layoutJumpRows = (s.setReg .x21 (s.getReg .x15)).setPC (address 479) := by
  have h1 : execInstrBr s (.ADDI .x21 .x15 0) = (s.setReg .x21 (s.getReg .x15)).setPC (address 1) := by
    simp only [execInstrBr, pc]
    rw [show signExtend12 0 = 0#64 by decide, BitVec.add_zero]
    rfl
  have h16 : ((s.setReg .x21 (s.getReg .x15)).setPC (address 1)).getReg .x16 ≠ 0#64 := by
    simpa [Opening.getReg_setReg, MachineState.getReg_setPC] using nz
  have h2 : execInstrBr ((s.setReg .x21 (s.getReg .x15)).setPC (address 1)) (.BEQ .x16 .x0 588) =
      (s.setReg .x21 (s.getReg .x15)).setPC (address 2) := by
    have neq : (((s.setReg .x21 (s.getReg .x15)).setPC (address 1)).getReg .x16 == 0) = false :=
      beq_false_of_ne h16
    simp only [execInstrBr, open_zero, neq, Bool.false_eq_true, ite_false, pc_of_set, setPC_setPC]
    rfl
  have h3 : execInstrBr ((s.setReg .x21 (s.getReg .x15)).setPC (address 2)) (.JAL .x0 1908) =
      (s.setReg .x21 (s.getReg .x15)).setPC (address 479) := by
    simp only [execInstrBr, setReg_x0_eq, pc_of_set, setPC_setPC]
    exact congrArg (s.setReg .x21 (s.getReg .x15)).setPC
      (by decide : address 2 + signExtend21 1908#21 = address 479)
  refine ⟨?_, ?_⟩
  · refine ⟨pc, rfl, ?_, rfl, ?_, rfl, trivial⟩
    · rw [h1]; rfl
    · rw [h1, h2]; rfl
  · simp only [walkRows, layoutJumpRows, List.foldl_cons, List.foldl_nil, h1, h2, h3]

theorem layout_ok (s : MachineState) (pc : s.pc = address 0) (nz : s.getReg .x16 ≠ 0#64) :
    legal layoutRows s := by
  obtain ⟨ok0, eq0⟩ := layout_jump_step s pc nz
  have okA : ∀ t : MachineState, t.pc = address 479 →
      legal layoutSetupA t ∧ (walkRows t layoutSetupA).pc = address 484 := fun t hpc =>
    ⟨by simp [layoutSetupA, legal, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, hpc, address],
     by simp [walkRows, layoutSetupA, execInstrBr, hpc, address]⟩
  have okB : ∀ t : MachineState, t.pc = address 484 → legal layoutSetupB t := fun t hpc => by
    simp [layoutSetupB, legal, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, hpc, address]
  unfold layoutRows
  apply legal_append
  · apply legal_append _ _ _ ok0
    rw [eq0]; exact (okA _ rfl).1
  · rw [walk_join, eq0]; exact okB _ (okA _ rfl).2

private theorem setupA_frame (s : MachineState) (pc : s.pc = address 479) :
    let t := walkRows s layoutSetupA
    t.pc = address 484 ∧ t.mem = s.mem ∧
    t.getReg .x8 = s.getReg .x13 ∧ t.getReg .x9 = s.getReg .x12 ∧
    t.getReg .x18 = s.getReg .x16 ∧ t.getReg .x22 = s.getReg .x12 + (442369#64 <<< 12) ∧
    (∀ k, k ∉ ([.x8, .x9, .x18, .x22] : List Reg) → t.getReg k = s.getReg k) := by
  refine ⟨by simp [walkRows, layoutSetupA, execInstrBr, pc, address],
    by simp [walkRows, layoutSetupA, execInstrBr],
    by simp [walkRows, layoutSetupA, execInstrBr, signExtend12],
    by simp [walkRows, layoutSetupA, execInstrBr, signExtend12],
    by simp [walkRows, layoutSetupA, execInstrBr, signExtend12],
    by simp [walkRows, layoutSetupA, execInstrBr, signExtend12], ?_⟩
  intro k h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [walkRows, layoutSetupA, execInstrBr, Ne.symm h.1, Ne.symm h.2.1, Ne.symm h.2.2.1, Ne.symm h.2.2.2]

private theorem setupB_frame (s : MachineState) (pc : s.pc = address 484) :
    let t := walkRows s layoutSetupB
    t.pc = address 488 ∧ t.mem = s.mem ∧
    t.getReg .x19 = 5#64 ∧ t.getReg .x23 = 368#64 ∧ t.getReg .x26 = BitVec.ofNat 64 tableBase ∧
    (∀ k, k ∉ ([.x19, .x23, .x26] : List Reg) → t.getReg k = s.getReg k) := by
  refine ⟨by simp [walkRows, layoutSetupB, execInstrBr, pc, address],
    by simp [walkRows, layoutSetupB, execInstrBr],
    by simp [walkRows, layoutSetupB, execInstrBr, signExtend12],
    by simp [walkRows, layoutSetupB, execInstrBr, signExtend12],
    by simp [walkRows, layoutSetupB, execInstrBr, signExtend12]; decide, ?_⟩
  intro k h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [walkRows, layoutSetupB, execInstrBr, Ne.symm h.1, Ne.symm h.2.1, Ne.symm h.2.2]

theorem layout_frame_gen (init : MachineState) (p : Positions)
    (pc₀ : init.pc = address 0)
    (trap : init.getReg .x12 = BitVec.ofNat 64 trapdoorBase)
    (indices : init.getReg .x13 = BitVec.ofNat 64 indicesBase)
    (proof : init.getReg .x15 = BitVec.ofNat 64 proofBase)
    (count : init.getReg .x16 = BitVec.ofNat 64 p.card)
    (nonzero : init.getReg .x16 ≠ 0#64) :
    let l := walkRows init layoutRows
    l.pc = address 488 ∧ l.mem = init.mem ∧ Base l p := by
  dsimp only
  have step0 := (layout_jump_step init pc₀ nonzero).2
  have leq : walkRows init layoutRows = walkRows (walkRows (walkRows init layoutJumpRows) layoutSetupA) layoutSetupB := by
    unfold layoutRows; rw [walk_join, walk_join]
  rw [leq, step0]
  let s1 := (init.setReg .x21 (init.getReg .x15)).setPC (address 479)
  have s1pc : s1.pc = address 479 := rfl
  have s1mem : s1.mem = init.mem := by simp [s1]
  have s1r (k : Reg) (hk : k ≠ .x21) : s1.getReg k = init.getReg k := by simp [s1, Ne.symm hk]
  have s1_x21 : s1.getReg .x21 = init.getReg .x15 := by simp [s1]
  obtain ⟨s2pc, s2mem, s2_8, s2_9, s2_18, s2_22, s2keep⟩ := setupA_frame s1 s1pc
  obtain ⟨lpc, lmem, l_19, l_23, l_26, lkeep⟩ := setupB_frame (walkRows s1 layoutSetupA) s2pc
  refine ⟨lpc, lmem.trans (s2mem.trans s1mem), ?_⟩
  refine ⟨?_, ?_, ?_, l_19, ?_, ?_, ?_, l_23, l_26⟩
  · exact (lkeep _ (by decide)).trans (s2_8.trans ((s1r _ (by decide)).trans indices))
  · exact (lkeep _ (by decide)).trans (s2_9.trans ((s1r _ (by decide)).trans trap))
  · exact (lkeep _ (by decide)).trans (s2_18.trans ((s1r _ (by decide)).trans count))
  · exact (lkeep _ (by decide)).trans ((s2keep _ (by decide)).trans ((s1r _ (by decide)).trans proof))
  · exact (lkeep _ (by decide)).trans ((s2keep _ (by decide)).trans (s1_x21.trans proof))
  · rw [lkeep _ (by decide), s2_22, s1r _ (by decide), trap]
    have h442 : (442369#64 <<< 12) = BitVec.ofNat 64 1811943424 := by decide
    rw [h442, ← BitVec.ofNat_add]; rfl

private theorem configA_step (s : MachineState) (pc : s.pc = address 488) :
    let t := walkRows s configA
    legal configA s ∧ t.pc = address 493 ∧ t.mem = s.mem ∧
    t.getReg .x10 = 1024#64 ∧ t.getReg .x12 = 1536#64 ∧ t.getReg .x11 = 200#64 ∧
    t.getReg .x13 = 1#64 ∧ t.getReg .x5 = 0#64 ∧
    (∀ k, k ∉ ([.x10, .x12, .x11, .x13, .x5] : List Reg) → t.getReg k = s.getReg k) := by
  refine ⟨by simp [configA, legal, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, address],
    by simp [walkRows, configA, execInstrBr, pc, address],
    by simp [walkRows, configA, execInstrBr],
    by simp [walkRows, configA, execInstrBr, signExtend12],
    by simp [walkRows, configA, execInstrBr, signExtend12],
    by simp [walkRows, configA, execInstrBr, signExtend12],
    by simp [walkRows, configA, execInstrBr, signExtend12],
    by simp [walkRows, configA, execInstrBr, signExtend12], ?_⟩
  intro k h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [walkRows, configA, execInstrBr, Ne.symm h.1, Ne.symm h.2.1, Ne.symm h.2.2.1, Ne.symm h.2.2.2.1, Ne.symm h.2.2.2.2]

private theorem configB_step (s : MachineState) (pc : s.pc = address 493) :
    let t := walkRows s configB
    legal configB s ∧ t.pc = address 498 ∧ t.mem = s.mem ∧
    t.getReg .x14 = s.getReg .x8 ∧ t.getReg .x17 = s.getReg .x18 ∧
    t.getReg .x24 = 4096#64 ∧ t.getReg .x27 = 4095#64 ∧ t.getReg .x29 = 11#64 ∧
    (∀ k, k ∉ ([.x14, .x17, .x24, .x27, .x29] : List Reg) → t.getReg k = s.getReg k) := by
  refine ⟨by simp [configB, legal, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, pc, address],
    by simp [walkRows, configB, execInstrBr, pc, address],
    by simp [walkRows, configB, execInstrBr],
    by simp [walkRows, configB, execInstrBr, signExtend12],
    by simp [walkRows, configB, execInstrBr, signExtend12],
    by simp [walkRows, configB, execInstrBr],
    by simp [walkRows, configB, execInstrBr, signExtend12],
    by simp [walkRows, configB, execInstrBr, signExtend12], ?_⟩
  intro k h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [walkRows, configB, execInstrBr, Ne.symm h.1, Ne.symm h.2.1, Ne.symm h.2.2.1, Ne.symm h.2.2.2.1, Ne.symm h.2.2.2.2]

theorem config_ok (s : MachineState) (pc : s.pc = address 488) : legal configRows s := by
  obtain ⟨okA, pcA, _⟩ := configA_step s pc
  exact legal_append s configA configB okA (configB_step (walkRows s configA) pcA).1

theorem config_frame (s : MachineState) (pc : s.pc = address 488) (p : Positions) (b : Base s p) :
    let t := walkRows s configRows
    t.pc = address 498 ∧ t.mem = s.mem ∧ Base t p ∧ Registers t 0 p.card := by
  dsimp only
  rw [show walkRows s configRows = walkRows (walkRows s configA) configB from walk_join s configA configB]
  obtain ⟨_, pcA, memA, r10, r12, r11, r13, r5, keepA⟩ := configA_step s pc
  obtain ⟨_, pcB, memB, r14, r17, r24, r27, r29, keepB⟩ := configB_step (walkRows s configA) pcA
  have keep (k : Reg) (hA : k ∉ ([.x10, .x12, .x11, .x13, .x5] : List Reg))
      (hB : k ∉ ([.x14, .x17, .x24, .x27, .x29] : List Reg)) :
      (walkRows (walkRows s configA) configB).getReg k = s.getReg k :=
    (keepB k hB).trans (keepA k hA)
  refine ⟨pcB, memB.trans memA,
    ⟨(keep _ (by decide) (by decide)).trans b.indices, (keep _ (by decide) (by decide)).trans b.heap,
     (keep _ (by decide) (by decide)).trans b.count, (keep _ (by decide) (by decide)).trans b.five,
     (keep _ (by decide) (by decide)).trans b.begin, (keep _ (by decide) (by decide)).trans b.dest,
     (keep _ (by decide) (by decide)).trans b.salts, (keep _ (by decide) (by decide)).trans b.groupWidth,
     (keep _ (by decide) (by decide)).trans b.table⟩,
    ⟨(keepB _ (by decide)).trans r10, (keepB _ (by decide)).trans r12, (keepB _ (by decide)).trans r5,
     (keepB _ (by decide)).trans r11, (keepB _ (by decide)).trans r13,
     r14.trans ((keepA _ (by decide)).trans (b.indices.trans (by decide))),
     r17.trans ((keepA _ (by decide)).trans b.count),
     (keep _ (by decide) (by decide)).trans (b.salts.trans (by decide)),
     r24, r27, r29⟩⟩

def keyCopy (s : MachineState) :=
  ((s.setMem 1032 (s.getMem 6106914856)).setMem 1040 (s.getMem 6106914864)).setMem 1048 (s.getMem 6106914872)

theorem key_ok (s : MachineState) (p : Positions) (pc : s.pc = address 498) (r : Registers s 0 p.card) :
    legal keyRows s := by
  simp [keyRows, legal, ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
    r.salt, r.input, pc, address, signExtend12]; decide

theorem key_frame (s : MachineState) (p : Positions) (pc : s.pc = address 498) (r : Registers s 0 p.card) :
    let t := walkRows s keyRows
    t.pc = address 504 ∧ t.mem = (keyCopy s).mem ∧ ∀ k, k ≠ .x31 → t.getReg k = s.getReg k := by
  refine ⟨?_, ?_, ?_⟩
  · simp [walkRows, keyRows, execInstrBr, pc, address]
  · simp [walkRows, keyRows, execInstrBr, mem_of_store, keyCopy, r.input, r.salt, signExtend12,
      MachineState.getMem_setMem_ne (by decide : (6106914864#64) ≠ 1032#64),
      MachineState.getMem_setMem_ne (by decide : (6106914872#64) ≠ 1032#64),
      MachineState.getMem_setMem_ne (by decide : (6106914872#64) ≠ 1040#64)]
  · intro k ne; simp [walkRows, keyRows, execInstrBr, Ne.symm ne]

theorem low_zero (sub : Submission) (abi : QuadOpening.OpeningABI sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (w : Nat) (low : w < 1024) :
    memoryView (sub.initialState .opening (td, p)) w = 0 := by
  change (sub.initialState .opening (td, p)).getMem (BitVec.ofNat 64 (8 * w)) = _
  rw [initial_input_word sub .opening (td, p) (8 * w) (by omega)]
  have zero (j : Nat) (hj : j < 8) : inputByte sub .opening (td, p) (8 * w + j) = 0 := by
    have lo : ¬sub.layout.trapdoor ≤ 8 * w + j := by rw [abi.trapdoor]; change ¬4294971424 ≤ _; omega
    have ix : ¬sub.layout.indices ≤ 8 * w + j := by rw [abi.indices]; change ¬6375350304 ≤ _; omega
    have img : (sub.image .opening).data = [] := by rw [abi.image]; rfl
    simp [inputByte, Submission.inputBuffers, fixedBuffer, positionsBuffer, lo, ix, img]
  rw [Finset.sum_eq_zero (fun j hj => by rw [zero _ (Finset.mem_range.mp hj)]; simp)]; rfl

theorem key_words (sub : Submission) (layout : OpeningLayout sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (j : Fin 3) :
    (sub.initialState .opening (td, p)).getMem (BitVec.ofNat 64 (6106914856 + 8 * j.val)) =
      (keyOf td).extractLsb' (64 * j.val) 64 := by
  have hj := j.isLt
  rw [← word_at _ _ (by omega),
    show 6106914856 + 8 * j.val = trapdoorBase + (1811943432 + 8 * j.val) by
      unfold trapdoorBase LENGTH LOG_LENGTH; omega,
    input_trapdoor_slice sub layout td p _ _ (by change _ ≤ 2080378880; omega)]
  unfold keyOf
  rw [nested_slice _ (by omega : 64 * j.val + 64 ≤ 192)]
  congr 1; omega

private theorem key_outside (s : MachineState) (w : Word) (a : w ≠ 1032) (b : w ≠ 1040) (c : w ≠ 1048) :
    (keyCopy s).getMem w = s.getMem w := by
  unfold keyCopy
  exact (MachineState.getMem_setMem_ne c).trans ((MachineState.getMem_setMem_ne b).trans (MachineState.getMem_setMem_ne a))

private theorem key_cell (s : MachineState) (j : Fin 3) :
    memoryView (keyCopy s) (129 + j.val) = s.getMem (BitVec.ofNat 64 (6106914856 + 8 * j.val)) := by
  fin_cases j <;> unfold memoryView keyCopy <;> rfl

end TwoPermutationPrototype.PentaOpening

namespace TwoPermutationPrototype.PentaOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open QOpening (OpeningLayout trapdoorBase proofBase indicesBase nonceBase)
open QuadOpening (initial_registers)
set_option maxRecDepth 24000
set_option maxHeartbeats 2500000

attribute [local irreducible] walkRows keyCopy header

structure HeaderRegisters (s : MachineState) (p : Positions) where
  pc : s.pc = address 504
  r : Registers s 0 p.card
  b : Base s p

private theorem keyCopy_mem_eq {a b : MachineState} (h : a.mem = b.mem) :
    (keyCopy a).mem = (keyCopy b).mem := by
  unfold keyCopy MachineState.setMem MachineState.getMem
  rw [h]

private theorem header_combine (init l c t : MachineState) (p : Positions)
    (hl : l = walkRows init layoutRows) (hc : c = walkRows l configRows) (_ht : t = walkRows c keyRows)
    (heq : header init = t)
    (okL : legal layoutRows init) (okC : legal configRows l) (okK : legal keyRows c)
    (lmem : l.mem = init.mem) (cmem : c.mem = l.mem)
    (cb : Base c p) (cr : Registers c 0 p.card)
    (tpc : t.pc = address 504) (tmem : t.mem = (keyCopy c).mem)
    (keep : ∀ k, k ≠ .x31 → t.getReg k = c.getReg k) :
    legal headerRows init ∧ Nonempty (HeaderRegisters (header init) p) ∧ (header init).mem = (keyCopy init).mem := by
  refine ⟨?_, ?_, ?_⟩
  · unfold headerRows
    apply legal_append
    · exact legal_append init _ _ okL (hl ▸ okC)
    · rw [walk_join, ← hl, ← hc]; exact okK
  · rw [heq]
    exact ⟨⟨tpc,
      ⟨(keep _ (by decide)).trans cr.input, (keep _ (by decide)).trans cr.output,
       (keep _ (by decide)).trans cr.selector, (keep _ (by decide)).trans cr.width,
       (keep _ (by decide)).trans cr.primitive, (keep _ (by decide)).trans cr.index,
       (keep _ (by decide)).trans cr.leftReg, (keep _ (by decide)).trans cr.salt,
       (keep _ (by decide)).trans cr.base, (keep _ (by decide)).trans cr.periodReg,
       (keep _ (by decide)).trans cr.divReg⟩,
      ⟨(keep _ (by decide)).trans cb.indices, (keep _ (by decide)).trans cb.heap,
       (keep _ (by decide)).trans cb.count, (keep _ (by decide)).trans cb.five,
       (keep _ (by decide)).trans cb.begin, (keep _ (by decide)).trans cb.dest,
       (keep _ (by decide)).trans cb.salts, (keep _ (by decide)).trans cb.groupWidth,
       (keep _ (by decide)).trans cb.table⟩⟩⟩
  · rw [heq]; exact tmem.trans (keyCopy_mem_eq (cmem.trans lmem))

theorem header_core (init : MachineState) (p : Positions)
    (pc₀ : init.pc = address 0)
    (trap : init.getReg .x12 = BitVec.ofNat 64 trapdoorBase)
    (indices : init.getReg .x13 = BitVec.ofNat 64 indicesBase)
    (proof : init.getReg .x15 = BitVec.ofNat 64 proofBase)
    (count : init.getReg .x16 = BitVec.ofNat 64 p.card)
    (nonzero : init.getReg .x16 ≠ 0#64) :
    legal headerRows init ∧ Nonempty (HeaderRegisters (header init) p) ∧ (header init).mem = (keyCopy init).mem := by
  obtain ⟨lpc, lmem, lb⟩ := layout_frame_gen init p pc₀ trap indices proof count nonzero
  obtain ⟨cpc, cmem, cb, cr⟩ := config_frame (walkRows init layoutRows) lpc p lb
  obtain ⟨tpc, tmem, keep⟩ := key_frame (walkRows (walkRows init layoutRows) configRows) p cpc cr
  have heq : header init = walkRows (walkRows (walkRows init layoutRows) configRows) keyRows := by
    unfold header headerRows; rw [walk_join, walk_join]
  exact header_combine init (walkRows init layoutRows) (walkRows (walkRows init layoutRows) configRows)
    (walkRows (walkRows (walkRows init layoutRows) configRows) keyRows) p
    rfl rfl rfl heq (layout_ok init pc₀ nonzero) (config_ok _ lpc) (key_ok _ p cpc cr)
    lmem cmem cb cr tpc tmem keep

end TwoPermutationPrototype.PentaOpening

namespace TwoPermutationPrototype.PentaOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open QOpening (OpeningLayout trapdoorBase proofBase indicesBase nonceBase)
open QuadOpening (initial_registers)
set_option maxRecDepth 24000
set_option maxHeartbeats 2500000

attribute [local irreducible] walkRows keyCopy header

theorem header_valid (sub : Submission) (abi : QuadOpening.OpeningABI sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (nz : 0 < p.card) :
    let init := sub.initialState .opening (td, p)
    legal headerRows init ∧ Ready sub td p (keyOf td) (header init) 0 := by
  let init := sub.initialState .opening (td, p)
  have card : p.card ≤ 16777216 := by change p.card ≤ LENGTH; simpa [Index] using Finset.card_le_univ p
  obtain ⟨pc₀, trap, indices, proof, count⟩ := initial_registers sub abi.toOpeningLayout td p
  have nr : init.getReg .x16 ≠ 0#64 := by
    rw [count]
    intro same
    have := QOpening.nat_address_injective (by omega) (by decide) same
    omega
  obtain ⟨valid, ⟨regs⟩, mem⟩ := header_core init p pc₀ trap indices proof count nr
  refine ⟨valid, ⟨regs.r, regs.b, ?_, ?_, ?_⟩⟩
  · simpa only [passPC, ite_eq_right (Nat.ne_of_lt nz)] using regs.pc
  · intro w fit guard _ _
    have neq (j : Nat) (hj : 129 ≤ j ∧ j ≤ 131) : wordAddress w ≠ wordAddress j :=
      fun h => (by have := wordAddress_injective_of_bound (by omega) (by omega) h; omega : False)
    change (header init).mem _ = _; rw [mem]
    change (keyCopy init).getMem (wordAddress w) = _
    exact key_outside init _ (neq 129 (by decide)) (neq 130 (by decide)) (neq 131 (by decide))
  · intro j lo hi
    change (header init).mem _ = _; rw [mem]
    by_cases stored : j ≤ 3
    · let ix : Fin 3 := ⟨j - 1, by omega⟩
      change memoryView (keyCopy init) (128 + j) = _
      rw [show 128 + j = 129 + ix.val by dsimp [ix]; omega, key_cell init ix]
      exact key_words sub abi.toOpeningLayout td p ix
    · have neq (n : Nat) (hn : 129 ≤ n ∧ n ≤ 131) : wordAddress (128 + j) ≠ wordAddress n :=
        fun h => (by have := wordAddress_injective_of_bound (by omega) (by omega) h; omega : False)
      change (keyCopy init).getMem (wordAddress (128 + j)) = _
      rw [key_outside init _ (neq 129 (by decide)) (neq 130 (by decide)) (neq 131 (by decide))]
      change memoryView init (128 + j) = _
      rw [low_zero sub abi td p _ (by omega)]
      apply BitVec.eq_of_getLsbD_eq; intro b hb
      simp [PentaGrouped.keyBlock, hb, show 192 ≤ 64 * (j - 1) + b by omega]

theorem header_run (sub : Submission) (abi : QuadOpening.OpeningABI sub)
    (td : BitVec (8 * sub.sizes.trapdoor)) (p : Positions) (nz : 0 < p.card) (fuel : Nat) :
    let s := sub.initialState .opening (td, p)
    execute openingImage (28 + fuel) s true = (do let z ← execute openingImage fuel (header s) true; return z.charge 28 0) := by
  simpa only [header, show headerRows.length = 28 by decide, show price headerRows = 28 by decide] using
    walk_rows_run _ headerRows (header_valid sub abi td p nz).1 header_fetch fuel true

end TwoPermutationPrototype.PentaOpening
