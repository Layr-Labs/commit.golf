import CommitGolfCandidate.HybWrapBlocks
import CommitGolfCandidate.PentaWrapLoader
import CommitGolfCandidate.QuadHeaderAssembly
import CommitGolfCandidate.QuadCheckerExit

/-! The wrapper's entry (words 0 and 464-486): the empty case jumps to the donor with `x6 = 1944`,
a wrong length jumps to the donor's reject, and otherwise `x24-x29` save `x10-x15` and the table
pointers are set. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions
open TwoPermutationPrototype.PentaWrap (WrapLayout loaderReg loader_reg loader_pc)
open TwoPermutationPrototype.Quad.Checker (loaderReference packedImage HeaderStart execute_header_reject
  headerRejectState)

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem loader_layout : WrapLayout loaderReference := ⟨rfl, rfl⟩

theorem image_wrap : WrapImage packedImage := quad_wrap_image

abbrev start (input : CheckInput) : MachineState := loaderReference.initialState .check input

theorem start_reg (input : CheckInput) (r : Reg) :
    (start input).getReg r = loaderReg input.positions.card input.proof.length r :=
  loader_reg loader_layout input r

/-- Proof byte base. -/
def PB : Nat := 10804535392

theorem set_pc_reg (s : MachineState) (p : Word) (r : Reg) : (s.setPC p).getReg r = s.getReg r := rfl
theorem set_pc_view (s : MachineState) (p : Word) : memoryView (s.setPC p) = memoryView s := rfl

theorem branch_step (s : MachineState) (i : Instr) (br : i.isBranch = true ∨ (∃ rd off, i = .JAL rd off)) :
    ordinaryStep s (.base i) = some (execInstrBr s i) := by
  rcases br with b | ⟨rd, off, rfl⟩
  · cases i <;> simp_all [Instr.isBranch, ordinaryStep, memoryArgumentsValid, memAccess]
  · simp [ordinaryStep, memoryArgumentsValid, memAccess]

theorem beq_exec (s : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr s (.BEQ r₁ r₂ imm) =
      s.setPC (if s.getReg r₁ = s.getReg r₂ then s.pc + signExtend13 imm else s.pc + 4) := by
  simp only [execInstrBr]; split <;> simp_all

theorem bne_exec (s : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr s (.BNE r₁ r₂ imm) =
      s.setPC (if s.getReg r₁ = s.getReg r₂ then s.pc + 4 else s.pc + signExtend13 imm) := by
  simp only [execInstrBr]; split <;> simp_all

theorem jal_exec (s : MachineState) (imm : BitVec 21) :
    execInstrBr s (.JAL .x0 imm) = s.setPC (s.pc + signExtend21 imm) := by
  simp only [execInstrBr]
  congr 1

theorem word_eq_iff (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]

theorem card_small (input : CheckInput) : input.positions.card ≤ 16777216 := Quad.Checker.checker_positions_bound input

/-! ### Word 0 and the empty test -/

def jumped (input : CheckInput) : MachineState := execInstrBr (start input) (.JAL .x0 1856)

theorem jumped_pc (input : CheckInput) : (jumped input).pc = BitVec.ofNat 64 (4096+4*(464+0)) := by
  unfold jumped; rw [jal_exec, set_pc_pc', loader_pc]; decide
where set_pc_pc' (s : MachineState) (p : Word) : (s.setPC p).pc = p := rfl

theorem jumped_reg (input : CheckInput) (r : Reg) : (jumped input).getReg r = (start input).getReg r := by
  unfold jumped; rw [jal_exec]; rfl

theorem jumped_view (input : CheckInput) : memoryView (jumped input) = memoryView (start input) := by
  unfold jumped; rw [jal_exec]; rfl

theorem jump_obs (o : Oracle) (input : CheckInput) :
    Obs o packedImage (start input) (jumped input) 1 1 0 [] := by
  have cell : fetch packedImage (start input) = some (.base (.JAL .x0 1856)) := by
    have numeric : (start input).pc.toNat = 4096 := by rw [loader_pc]; rfl
    rw [fetch, numeric, ite_eq_left (by omega), show (4096-4096)/4 = 0 by rfl]
    have decoded := image_wrap.entry
    cases entry : packedImage.code[0]? with
    | none => simp [entry] at decoded
    | some word => simpa only [entry, Option.bind_some] using decoded
  exact Obs.step o packedImage _ _ _ cell (branch_step _ _ (Or.inr ⟨_, _, rfl⟩))

def tested (input : CheckInput) : MachineState := execInstrBr (jumped input) (.BNE .x16 .x0 8)

theorem tested_pc (input : CheckInput) :
    (tested input).pc = if input.positions.card = 0 then BitVec.ofNat 64 (4096+4*(464+1))
      else BitVec.ofNat 64 (4096+4*(464+2)) := by
  unfold tested
  rw [bne_exec, jumped_reg, start_reg, jumped_pc]
  have small := card_small input
  show (if BitVec.ofNat 64 input.positions.card = 0#64 then _ else _) = _
  by_cases zero : input.positions.card = 0
  · rw [if_pos (by rw [zero]), if_pos zero]; decide
  · rw [if_neg (by rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, word_eq_iff _ _ (by omega) (by decide)]; exact zero),
      if_neg zero]; decide

theorem tested_reg (input : CheckInput) (r : Reg) : (tested input).getReg r = (start input).getReg r := by
  unfold tested; rw [bne_exec]; exact jumped_reg input r

theorem tested_view (input : CheckInput) : memoryView (tested input) = memoryView (start input) := by
  unfold tested; rw [bne_exec, set_pc_view]; exact jumped_view input

theorem test_obs (o : Oracle) (input : CheckInput) :
    Obs o packedImage (jumped input) (tested input) 1 1 0 [] :=
  Obs.step o packedImage _ _ _ (wrap_fetch image_wrap _ 0 _ rfl (jumped_pc input)) (branch_step _ _ (Or.inl rfl))

/-! ### The empty case -/

def emptyOps : List Action := [.lui .x6 (hi20 1944) (BitVec.ofNat 64 0), .offset .x6 .x6 (lo12 1944) (BitVec.ofNat 64 1944)]

theorem empty_code : wrapCode[1]? = some (.JAL .x0 14196) ∧ WrapAt 3550 (liCode .x6 1944) ∧
    wrapCode[3552]? = some (.JAL .x0 2081092) := by decide

theorem wrap_empty (o : Oracle) (input : CheckInput) (empty : input.positions.card = 0) :
    ∃ t cycles, Obs o packedImage (start input) t 6 cycles 0 [] ∧ HeaderStart input t := by
  have pcT : (tested input).pc = BitVec.ofNat 64 (4096+4*(464+1)) := by rw [tested_pc, if_pos empty]
  let e := execInstrBr (tested input) (.JAL .x0 14196)
  have hop := Obs.step o packedImage (tested input) e _ (wrap_fetch image_wrap _ 1 _ empty_code.1 pcT)
    (branch_step _ _ (Or.inr ⟨_, _, rfl⟩))
  have pcE : e.pc = BitVec.ofNat 64 (4096+4*(464+3550)) := by
    show (execInstrBr (tested input) (.JAL .x0 14196)).pc = _
    rw [jal_exec, pcT]; rfl
  have eReg : ∀ r, e.getReg r = (start input).getReg r := by
    intro r; show (execInstrBr (tested input) (.JAL .x0 14196)).getReg r = _
    rw [jal_exec, set_pc_reg, tested_reg]
  have valid : validFixed o emptyOps e := by
    refine ⟨show ((hi20 1944).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 0 by decide, ?_, trivial⟩
    show (putReg e .x6 (BitVec.ofNat 64 0)).getReg .x6 + signExtend12 (lo12 1944) = _
    rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]; decide
  have ops := Obs.ops o packedImage emptyOps (464+3550) e pcE
    (wrap_fetch_ops image_wrap empty_code.2.1 emptyOps rfl) valid
  let u := fixedOps o emptyOps e
  have upc : u.pc = BitVec.ofNat 64 (4096+4*(464+3552)) := by
    rw [fixed_ops_pc, pc_after _ _ _ pcE]; rfl
  have ureg : ∀ r, r ≠ .x6 → u.getReg r = (start input).getReg r := by
    intro r hr
    show (putReg (putReg e .x6 _) .x6 _).getReg r = _
    rw [put_reg_reg, if_neg (by intro h; exact hr h.1.symm), put_reg_reg, if_neg (by intro h; exact hr h.1.symm),
      eReg]
  have u6 : u.getReg .x6 = BitVec.ofNat 64 1944 := by
    show (putReg (putReg e .x6 _) .x6 _).getReg .x6 = _
    rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  let t := execInstrBr u (.JAL .x0 2081092)
  have jump := Obs.step o packedImage u t _ (wrap_fetch image_wrap _ 3552 _ empty_code.2.2 upc)
    (branch_step _ _ (Or.inr ⟨_, _, rfl⟩))
  refine ⟨t, _, ((jump_obs o input).trans ((test_obs o input).trans (hop.trans (ops.trans jump)))), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · show (execInstrBr u (.JAL .x0 2081092)).pc = _
    rw [jal_exec, upc]; rfl
  · show (execInstrBr u (.JAL .x0 2081092)).getReg .x6 = _
    rw [jal_exec, set_pc_reg, u6]
  · intro r hr
    show (execInstrBr u (.JAL .x0 2081092)).getReg r = _
    rw [jal_exec, set_pc_reg, ureg r hr]

/-! ### The length test -/

def lenOps (k : Nat) : List Action :=
  [.offset .x30 .x16 8 (BitVec.ofNat 64 (k+8)), .offset .x31 .x0 752 (BitVec.ofNat 64 752),
   .alu (.MUL .x30 .x30 .x31) .x30 (BitVec.ofNat 64 ((k+8)*752)), .offset .x30 .x30 704 (BitVec.ofNat 64 ((k+8)*752+704))]

theorem len_code : WrapAt 2 [.ADDI .x30 .x16 8, .ADDI .x31 .x0 752, .MUL .x30 .x30 .x31, .ADDI .x30 .x30 704] ∧
    wrapCode[6]? = some (.BEQ .x17 .x30 8) ∧ wrapCode[7]? = some (.JAL .x0 14184) ∧
    wrapCode[3553]? = some (.JAL .x0 2082540) := by decide

/-- The state after the length computation (`x30 = 752k + 6720`). -/
def measured (o : Oracle) (input : CheckInput) : MachineState :=
  fixedOps o (lenOps input.positions.card) (execInstrBr (tested input) (.BNE .x16 .x0 8))

theorem measured_facts (o : Oracle) (input : CheckInput) (pos : input.positions.card ≠ 0) :
    let t := fixedOps o (lenOps input.positions.card) (tested input)
    Obs o packedImage (start input) t 6 (opCycles (lenOps input.positions.card) + 2) 0 [] ∧
      t.pc = BitVec.ofNat 64 (4096+4*(464+6)) ∧ memoryView t = memoryView (start input) ∧
      t.getReg .x30 = BitVec.ofNat 64 (752*input.positions.card+6720) ∧
      ∀ r, r ≠ .x30 → r ≠ .x31 → t.getReg r = (start input).getReg r := by
  intro t
  have small := card_small input
  have pcT : (tested input).pc = BitVec.ofNat 64 (4096+4*(464+2)) := by rw [tested_pc, if_neg pos]
  have k16 : (tested input).getReg .x16 = BitVec.ofNat 64 input.positions.card := by
    rw [tested_reg, start_reg]; rfl
  have valid : validFixed o (lenOps input.positions.card) (tested input) := by
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · show (tested input).getReg .x16 + signExtend12 8 = _
      rw [k16, show (8 : BitVec 12) = BitVec.ofNat 12 8 from rfl, add_small _ 8 (by decide) (by omega)]
    · show (fixedStep o (tested input) _).getReg .x0 + signExtend12 752 = _
      rw [reg_zero]; decide
    · apply alu_mul
      simp only [fixedStep, put_reg_reg]
      simp only [reduceCtorEq, false_and, if_false, ne_eq, not_false_eq_true, and_self, if_true]
      exact word_mul _ _ (by omega) (by decide)
    · show (fixedStep o (fixedStep o (fixedStep o (tested input) _) _) _).getReg .x30 + signExtend12 704 = _
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true]
      rw [show (704 : BitVec 12) = BitVec.ofNat 12 704 from rfl, add_small _ 704 (by decide) (by omega)]
  have ops := Obs.ops o packedImage (lenOps input.positions.card) (464+2) (tested input) pcT
    (wrap_fetch_ops image_wrap len_code.1 _ rfl) valid
  refine ⟨((jump_obs o input).trans ((test_obs o input).trans ops)).cast rfl (by omega) rfl rfl, ?_, ?_, ?_, ?_⟩
  · rw [fixed_ops_pc, pc_after _ _ _ pcT]; rfl
  · simp only [t, lenOps, fixedOps, List.foldl_cons, List.foldl_nil, fixedStep, put_reg_view, tested_view]
  · simp only [t, lenOps, fixedOps, List.foldl_cons, List.foldl_nil, fixedStep, put_reg_reg, ne_eq, reduceCtorEq,
      not_false_eq_true, and_self, if_true, false_and, if_false]
    congr 1; ring
  · intro r hr h31
    simp only [t, lenOps, fixedOps, List.foldl_cons, List.foldl_nil, fixedStep, put_reg_reg]
    simp only [show ¬ (Reg.x30 = r ∧ Reg.x30 ≠ .x0) from fun h => hr h.1.symm,
      show ¬ (Reg.x31 = r ∧ Reg.x31 ≠ .x0) from fun h => h31 h.1.symm, if_false, tested_reg]

/-- A wrong length: the wrapper jumps to the donor's reject (no oracle call). -/
theorem wrap_reject (o : Oracle) (input : CheckInput) (adm : input.proof.length < 2^64)
    (pos : input.positions.card ≠ 0) (wrong : input.proof.length ≠ 752*input.positions.card+6720) (fuel : Nat) :
    ∃ result : Execution,
      checkEvaluation o (recordRows (execute packedImage (12+fuel) (start input) false)) = ((result, []), 0) ∧
        result.exit = .failure := by
  obtain ⟨obs, pcM, _, x30, regs⟩ := measured_facts o input pos
  generalize fixedOps o (lenOps input.positions.card) (tested input) = m at obs pcM x30 regs
  have small := card_small input
  let b := execInstrBr m (.BEQ .x17 .x30 8)
  have pcB : b.pc = BitVec.ofNat 64 (4096+4*(464+7)) := by
    show (execInstrBr m (.BEQ .x17 .x30 8)).pc = _
    rw [beq_exec, regs .x17 (by decide) (by decide), start_reg, x30]
    show (if BitVec.ofNat 64 input.proof.length = _ then _ else _) = _
    rw [if_neg (by rw [word_eq_iff _ _ adm (by omega)]; exact wrong), pcM]; rfl
  have step₁ := Obs.step o packedImage m b _ (wrap_fetch image_wrap _ 6 _ len_code.2.1 pcM) (branch_step _ _ (Or.inl rfl))
  let j := execInstrBr b (.JAL .x0 14184)
  have pcJ : j.pc = BitVec.ofNat 64 (4096+4*(464+3553)) := by
    show (execInstrBr b (.JAL .x0 14184)).pc = _
    rw [jal_exec, pcB]; rfl
  have step₂ := Obs.step o packedImage b j _ (wrap_fetch image_wrap _ 7 _ len_code.2.2.1 pcB)
    (branch_step _ _ (Or.inr ⟨_, _, rfl⟩))
  let r := execInstrBr j (.JAL .x0 2082540)
  have pcR : r.pc = 0x15b0 := by
    show (execInstrBr j (.JAL .x0 2082540)).pc = _
    rw [jal_exec, pcJ]; rfl
  have step₃ := Obs.step o packedImage j r _ (wrap_fetch image_wrap _ 3553 _ len_code.2.2.2 pcJ)
    (branch_step _ _ (Or.inr ⟨_, _, rfl⟩))
  have whole := obs.trans (step₁.trans (step₂.trans step₃))
  have run := whole (3+fuel)
  rw [show 6 + (1 + (1 + 1)) + (3 + fuel) = 12+fuel by omega, execute_header_reject r pcR fuel,
    record_rows_pure, check_evaluation_pure] at run
  exact ⟨_, run, rfl⟩

/-! ### Save and table setup -/

def setupOps (k : Nat) : List Action :=
  [.offset .x31 .x0 0 (BitVec.ofNat 64 0),
   .offset .x24 .x10 0 (BitVec.ofNat 64 4096), .offset .x25 .x11 0 (BitVec.ofNat 64 4294971392),
   .offset .x26 .x12 0 (BitVec.ofNat 64 4294971424), .offset .x27 .x13 0 (BitVec.ofNat 64 6375350304),
   .offset .x28 .x14 0 (BitVec.ofNat 64 6509568096), .offset .x29 .x15 0 (BitVec.ofNat 64 PB),
   .offset .x30 .x30 2048 (BitVec.ofNat 64 (752*k+4672)), .offset .x30 .x30 2048 (BitVec.ofNat 64 (752*k+2624)),
   .offset .x30 .x30 2048 (BitVec.ofNat 64 (752*k+576)), .offset .x30 .x30 3520 (BitVec.ofNat 64 (752*k)),
   .alu (.ADD .x6 .x29 .x30) .x6 (BitVec.ofNat 64 (PB+752*k)),
   .lui .x7 (hi20 (H+40)) (BitVec.ofNat 64 268435456), .offset .x7 .x7 (lo12 (H+40)) (BitVec.ofNat 64 (H+40))]

theorem setup_code : WrapAt 8 (saveCode ++ tableSetup) := by decide

/-- The state at the table copy (word 486). -/
structure EntryDone (input : CheckInput) (t : MachineState) : Prop where
  pc : t.pc = BitVec.ofNat 64 (4096+4*(464+22))
  view : memoryView t = memoryView (start input)
  x6 : t.getReg .x6 = BitVec.ofNat 64 (PB + 752*input.positions.card)
  x7 : t.getReg .x7 = BitVec.ofNat 64 (H+40)
  x24 : t.getReg .x24 = BitVec.ofNat 64 4096
  x25 : t.getReg .x25 = BitVec.ofNat 64 4294971392
  x26 : t.getReg .x26 = BitVec.ofNat 64 4294971424
  x27 : t.getReg .x27 = BitVec.ofNat 64 6375350304
  x28 : t.getReg .x28 = BitVec.ofNat 64 6509568096
  x29 : t.getReg .x29 = BitVec.ofNat 64 PB
  x2 : t.getReg .x2 = (start input).getReg .x2
  x16 : t.getReg .x16 = BitVec.ofNat 64 input.positions.card
  x17 : t.getReg .x17 = (start input).getReg .x17

theorem wrap_entry (o : Oracle) (input : CheckInput) (adm : input.proof.length < 2^64)
    (pos : input.positions.card ≠ 0) (exact : input.proof.length = 752*input.positions.card+6720) :
    ∃ t cycles, Obs o packedImage (start input) t 21 cycles 0 [] ∧ EntryDone input t := by
  obtain ⟨obs, pcM, viewM, x30, regs⟩ := measured_facts o input pos
  generalize fixedOps o (lenOps input.positions.card) (tested input) = m at obs pcM viewM x30 regs
  have small := card_small input
  let b := execInstrBr m (.BEQ .x17 .x30 8)
  have pcB : b.pc = BitVec.ofNat 64 (4096+4*(464+8)) := by
    show (execInstrBr m (.BEQ .x17 .x30 8)).pc = _
    rw [beq_exec, regs .x17 (by decide) (by decide), start_reg, x30]
    show (if BitVec.ofNat 64 input.proof.length = _ then _ else _) = _
    rw [if_pos (by rw [exact]), pcM]; rfl
  have bReg : ∀ r, b.getReg r = m.getReg r := fun r => by
    show (execInstrBr m (.BEQ .x17 .x30 8)).getReg r = _; rw [beq_exec]; rfl
  have step₁ := Obs.step o packedImage m b _ (wrap_fetch image_wrap _ 6 _ len_code.2.1 pcM) (branch_step _ _ (Or.inl rfl))
  have rb : ∀ r, r ≠ .x30 → r ≠ .x31 → b.getReg r = loaderReg input.positions.card input.proof.length r := fun r hr h31 => by
    rw [bReg, regs r hr h31, start_reg]
  have b30 : b.getReg .x30 = BitVec.ofNat 64 (752*input.positions.card+6720) := by rw [bReg, x30]
  have valid : validFixed o (setupOps input.positions.card) b := by
    simp only [setupOps, validFixed, Action.valid, fixedStep, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true,
      and_self, if_true, false_and, if_false, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [reg_zero]; decide
    · rw [rb .x10 (by decide) (by decide)]; simp only [loaderReg]; decide
    · rw [rb .x11 (by decide) (by decide)]; simp only [loaderReg]; decide
    · rw [rb .x12 (by decide) (by decide)]; simp only [loaderReg]; decide
    · rw [rb .x13 (by decide) (by decide)]; simp only [loaderReg]; decide
    · rw [rb .x14 (by decide) (by decide)]; simp only [loaderReg]; decide
    · rw [rb .x15 (by decide) (by decide)]; simp only [loaderReg, PB]; decide
    · rw [b30, show (2048 : BitVec 12) = BitVec.ofNat 12 2048 from rfl,
        add_neg _ 2048 (by decide) (by decide) (by omega) (by omega)]
      congr 1
    · rw [show (2048 : BitVec 12) = BitVec.ofNat 12 2048 from rfl,
        add_neg _ 2048 (by decide) (by decide) (by omega) (by omega)]
      congr 1
    · rw [show (2048 : BitVec 12) = BitVec.ofNat 12 2048 from rfl,
        add_neg _ 2048 (by decide) (by decide) (by omega) (by omega)]
      congr 1
    · rw [show (3520 : BitVec 12) = BitVec.ofNat 12 3520 from rfl,
        add_neg _ 3520 (by decide) (by decide) (by omega) (by omega)]
      congr 1
    · apply alu_add
      simp only [put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true, false_and, if_false]
      rw [word_add _ _ (by unfold PB; omega)]
    · decide
    · decide
  have ops := Obs.ops o packedImage (setupOps input.positions.card) (464+8) b pcB
    (wrap_fetch_ops image_wrap setup_code _ rfl) valid
  refine ⟨_, _, (obs.trans (step₁.trans ops)).cast rfl rfl rfl rfl, ?_⟩
  have bview : memoryView b = memoryView (start input) := by
    show memoryView (execInstrBr m (.BEQ .x17 .x30 8)) = _; rw [beq_exec, set_pc_view, viewM]
  have regsB : ∀ r, r ≠ .x30 → r ≠ .x31 → b.getReg r = (start input).getReg r := fun r hr h31 => by rw [bReg, regs r hr h31]
  constructor
  · rw [fixed_ops_pc, pc_after _ _ _ pcB]; rfl
  · simp only [setupOps, fixedOps, List.foldl_cons, List.foldl_nil, fixedStep, put_reg_view, bview]
  all_goals simp only [setupOps, fixedOps, List.foldl_cons, List.foldl_nil, fixedStep, put_reg_reg, ne_eq, reduceCtorEq,
      not_false_eq_true, and_self, if_true, false_and, if_false]
  all_goals first | rfl | (rw [regsB _ (by decide) (by decide)]) | skip
  rw [start_reg]; rfl

end TwoPermutationPrototype.HybWrap
