import CommitGolfCandidate.TwoPermutationPackedRecordLeafPrelude
import CommitGolfCandidate.TwoPermutationLeafMask

/-! The checker cuts its own leaf digest to 245 bits before the lower path.
Word 58 (`addi s5,s5,16`, the first lower-setup instruction) jumps to an
out-of-line stub at word 542: `addi s5,s5,16; ld t6,24(s7); slli t6,t6,11;
srli t6,t6,11; sd t6,24(s7); jal 59`. The other four lower-setup instructions then
run unchanged, so no other checker PC moves. -/
namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (beginLowerCode beginLower lower_setup_post lower_setup_register)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

/-- Fetch from anywhere in the checker image (up to word 547). -/
theorem trunc_fetch (s : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 548) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch packedImage s = some (.base instruction) := by
  have numeric : s.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, if_pos (by omega)]
  rw [show (4096 + 4 * index - 4096) / 4 = index by omega]
  cases entry : packedImage.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

section Steps
variable (t : MachineState) (r : Reg)

private theorem pc_addi (rd rs : Reg) (i : BitVec 12) : (execInstrBr t (.ADDI rd rs i)).pc = t.pc + 4 := by
  cases rd <;> rfl
private theorem pc_add (rd a b : Reg) : (execInstrBr t (.ADD rd a b)).pc = t.pc + 4 := by cases rd <;> rfl
private theorem pc_ld (rd rs : Reg) (i : BitVec 12) : (execInstrBr t (.LD rd rs i)).pc = t.pc + 4 := by
  cases rd <;> rfl
private theorem pc_slli (rd rs : Reg) (i : BitVec 6) : (execInstrBr t (.SLLI rd rs i)).pc = t.pc + 4 := by
  cases rd <;> rfl
private theorem pc_srli (rd rs : Reg) (i : BitVec 6) : (execInstrBr t (.SRLI rd rs i)).pc = t.pc + 4 := by
  cases rd <;> rfl
private theorem pc_sd (a b : Reg) (i : BitVec 12) : (execInstrBr t (.SD a b i)).pc = t.pc + 4 := rfl
private theorem pc_jal (off : BitVec 21) : (execInstrBr t (.JAL .x0 off)).pc = t.pc + signExtend21 off := rfl

private theorem reg_addi (rd rs : Reg) (i : BitVec 12) (ne : rd ≠ r) :
    (execInstrBr t (.ADDI rd rs i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
private theorem reg_add (rd a b : Reg) (ne : rd ≠ r) : (execInstrBr t (.ADD rd a b)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
private theorem reg_ld (rd rs : Reg) (i : BitVec 12) (ne : rd ≠ r) :
    (execInstrBr t (.LD rd rs i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
private theorem reg_slli (rd rs : Reg) (i : BitVec 6) (ne : rd ≠ r) :
    (execInstrBr t (.SLLI rd rs i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
private theorem reg_srli (rd rs : Reg) (i : BitVec 6) (ne : rd ≠ r) :
    (execInstrBr t (.SRLI rd rs i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ ne]
private theorem reg_sd (a b : Reg) (i : BitVec 12) : (execInstrBr t (.SD a b i)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, Opening.getReg_setMem]
private theorem reg_jal (off : BitVec 21) : (execInstrBr t (.JAL .x0 off)).getReg r = t.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC]; rfl

private theorem mem_addi (rd rs : Reg) (i : BitVec 12) : (execInstrBr t (.ADDI rd rs i)).mem = t.mem := by
  cases rd <;> rfl
private theorem mem_add (rd a b : Reg) : (execInstrBr t (.ADD rd a b)).mem = t.mem := by cases rd <;> rfl
private theorem mem_ld (rd rs : Reg) (i : BitVec 12) : (execInstrBr t (.LD rd rs i)).mem = t.mem := by
  cases rd <;> rfl
private theorem mem_slli (rd rs : Reg) (i : BitVec 6) : (execInstrBr t (.SLLI rd rs i)).mem = t.mem := by
  cases rd <;> rfl
private theorem mem_srli (rd rs : Reg) (i : BitVec 6) : (execInstrBr t (.SRLI rd rs i)).mem = t.mem := by
  cases rd <;> rfl
private theorem mem_jal (off : BitVec 21) : (execInstrBr t (.JAL .x0 off)).mem = t.mem := rfl

end Steps

/-- Jump to the stub and advance the proof cursor (stub word 542). -/
def stubEnter (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.JAL .x0 1936)) (.ADDI .x21 .x21 16)
/-- `ld t6,24(s7)`. -/
def stubLoad (s : MachineState) : MachineState := execInstrBr (stubEnter s) (.LD .x31 .x23 24)
/-- `slli t6,t6,11; srli t6,t6,11`. -/
def stubMask (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (stubLoad s) (.SLLI .x31 .x31 11)) (.SRLI .x31 .x31 11)
/-- `sd t6,24(s7); jal 59`. -/
def stubBack (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (stubMask s) (.SD .x23 .x31 24)) (.JAL .x0 2095200)
/-- The lower setup with the leaf truncation stub. -/
def truncLower (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20))
    (.ADDI .x11 .x0 64)) (.ADDI .x13 .x0 0)) (.ADDI .x29 .x0 16)

section Facts
variable (s : MachineState) (pc : s.pc = 0x10e8)
include pc

private theorem enter_pc0 : (execInstrBr s (.JAL .x0 1936)).pc = BitVec.ofNat 64 (4096+4*542) := by
  rw [pc_jal, pc]; decide
private theorem enter_pc : (stubEnter s).pc = BitVec.ofNat 64 (4096+4*543) := by
  unfold stubEnter; rw [pc_addi, enter_pc0 s pc]; decide
private theorem load_pc : (stubLoad s).pc = BitVec.ofNat 64 (4096+4*544) := by
  unfold stubLoad; rw [pc_ld, enter_pc s pc]; decide
private theorem slli_pc : (execInstrBr (stubLoad s) (.SLLI .x31 .x31 11)).pc = BitVec.ofNat 64 (4096+4*545) := by
  rw [pc_slli, load_pc s pc]; decide
private theorem mask_pc : (stubMask s).pc = BitVec.ofNat 64 (4096+4*546) := by
  unfold stubMask; rw [pc_srli, slli_pc s pc]; decide
private theorem store_pc : (execInstrBr (stubMask s) (.SD .x23 .x31 24)).pc = BitVec.ofNat 64 (4096+4*547) := by
  rw [pc_sd, mask_pc s pc]; decide
private theorem back_pc : (stubBack s).pc = BitVec.ofNat 64 (4096+4*59) := by
  unfold stubBack; rw [pc_jal, store_pc s pc]; decide
private theorem add_pc : (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20)).pc = BitVec.ofNat 64 (4096+4*60) := by
  rw [pc_add, back_pc s pc]; decide
private theorem size_pc :
    (execInstrBr (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20)) (.ADDI .x11 .x0 64)).pc =
      BitVec.ofNat 64 (4096+4*61) := by
  rw [pc_addi, add_pc s pc]; decide
private theorem kind_pc :
    (execInstrBr (execInstrBr (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20)) (.ADDI .x11 .x0 64))
      (.ADDI .x13 .x0 0)).pc = BitVec.ofNat 64 (4096+4*62) := by
  rw [pc_addi, size_pc s pc]; decide

theorem trunc_lower_pc : (truncLower s).pc = 4348 := by
  unfold truncLower; rw [pc_addi, kind_pc s pc]; decide

end Facts

private theorem enter_x23 (s : MachineState) : (stubEnter s).getReg .x23 = s.getReg .x23 := by
  unfold stubEnter; rw [reg_addi _ _ _ _ _ (by decide), reg_jal]
private theorem mask_x23 (s : MachineState) : (stubMask s).getReg .x23 = s.getReg .x23 := by
  unfold stubMask stubLoad
  rw [reg_srli _ _ _ _ _ (by decide), reg_slli _ _ _ _ _ (by decide), reg_ld _ _ _ _ _ (by decide), enter_x23]

private theorem step_one (t next : MachineState) (I : Instr) (k : Nat) (hk : k < 548)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*k))
    (dec : (packedImage.code[k]?).bind decodeInstruction = some (.base I))
    (step : ordinaryStep t (.base I) = some next) (cyc : instructionCycles (.base I) = 1) (fuel : Nat) :
    execute packedImage (fuel+1) t false =
      (do let result ← execute packedImage fuel next false; return result.charge 1 0) := by
  rw [execute_ordinary_step _ _ _ _ _ _ (trunc_fetch t k I hk pc dec) step, cyc]

theorem execute_trunc_lower (state : MachineState) (pc : state.pc = 0x10e8)
    (digest : state.getReg .x23 = 12288) (fuel : Nat) :
    execute packedImage (11+fuel) state false =
      (do let result ← execute packedImage fuel (truncLower state) false
          return result.charge 11 0) := by
  have pc58 : state.pc = BitVec.ofNat 64 (4096+4*58) := by rw [pc]; decide
  have loadValid : accessValid ((stubEnter state).getReg .x23 + signExtend12 24) 8 = true := by
    rw [enter_x23, digest]; decide
  have storeValid : accessValid ((stubMask state).getReg .x23 + signExtend12 24) 8 = true := by
    rw [mask_x23, digest]; decide
  have stepLoad : ordinaryStep (stubEnter state) (.base (.LD .x31 .x23 24)) = some (stubLoad state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, loadValid, ite_true]; rfl
  have stepStore : ordinaryStep (stubMask state) (.base (.SD .x23 .x31 24)) =
      some (execInstrBr (stubMask state) (.SD .x23 .x31 24)) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, storeValid, ite_true]
  rw [show 11+fuel = ((((((((((fuel+1)+1)+1)+1)+1)+1)+1)+1)+1)+1)+1 by omega,
    step_one _ _ (.JAL .x0 1936) 58 (by decide) pc58 rfl rfl rfl,
    step_one _ (stubEnter state) (.ADDI .x21 .x21 16) 542 (by decide) (enter_pc0 state pc) rfl rfl rfl,
    step_one _ (stubLoad state) (.LD .x31 .x23 24) 543 (by decide) (enter_pc state pc) rfl stepLoad rfl,
    step_one _ _ (.SLLI .x31 .x31 11) 544 (by decide) (load_pc state pc) rfl rfl rfl,
    step_one _ (stubMask state) (.SRLI .x31 .x31 11) 545 (by decide) (slli_pc state pc) rfl rfl rfl,
    step_one _ _ (.SD .x23 .x31 24) 546 (by decide) (mask_pc state pc) rfl stepStore rfl,
    step_one _ (stubBack state) (.JAL .x0 2095200) 547 (by decide) (store_pc state pc) rfl rfl rfl,
    step_one _ _ (.ADD .x6 .x6 .x20) 59 (by decide) (back_pc state pc) rfl rfl rfl,
    step_one _ _ (.ADDI .x11 .x0 64) 60 (by decide) (add_pc state pc) rfl rfl rfl,
    step_one _ _ (.ADDI .x13 .x0 0) 61 (by decide) (size_pc state pc) rfl rfl rfl,
    step_one _ (truncLower state) (.ADDI .x29 .x0 16) 62 (by decide) (kind_pc state pc) rfl rfl rfl]
  simp only [bind_assoc, pure_bind, Execution.charge, Nat.zero_add]
  have arith : ∀ c : Nat, 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + c)))))))))) = 11 + c :=
    fun c => by omega
  simp only [arith]

theorem trunc_lower_register (state : MachineState) (reg : Reg)
    (noPointer : reg ≠ .x21) (noNode : reg ≠ .x6) (noSize : reg ≠ .x11)
    (noKind : reg ≠ .x13) (noCounter : reg ≠ .x29) (noTemp : reg ≠ .x31) :
    (truncLower state).getReg reg = state.getReg reg := by
  unfold truncLower stubBack stubMask stubLoad stubEnter
  rw [reg_addi _ _ _ _ _ (Ne.symm noCounter), reg_addi _ _ _ _ _ (Ne.symm noKind),
    reg_addi _ _ _ _ _ (Ne.symm noSize), reg_add _ _ _ _ _ (Ne.symm noNode), reg_jal, reg_sd,
    reg_srli _ _ _ _ _ (Ne.symm noTemp), reg_slli _ _ _ _ _ (Ne.symm noTemp), reg_ld _ _ _ _ _ (Ne.symm noTemp),
    reg_addi _ _ _ _ _ (Ne.symm noPointer), reg_jal]

theorem trunc_lower_post (state : MachineState) :
    let next := truncLower state
    next.getReg .x21 = state.getReg .x21+16 ∧
    next.getReg .x6 = state.getReg .x6+state.getReg .x20 ∧
    next.getReg .x11 = 64 ∧ next.getReg .x13 = 0 ∧ next.getReg .x29 = 16 := by
  have back (r : Reg) (h : r ≠ .x31) : (stubBack state).getReg r = (stubEnter state).getReg r := by
    unfold stubBack stubMask stubLoad
    rw [reg_jal, reg_sd, reg_srli _ _ _ _ _ (Ne.symm h), reg_slli _ _ _ _ _ (Ne.symm h), reg_ld _ _ _ _ _ (Ne.symm h)]
  have enter21 : (stubEnter state).getReg .x21 = state.getReg .x21+16 := by
    unfold stubEnter
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x21 ≠ .x0 by decide)]
    rfl
  have enter (r : Reg) (h : r ≠ .x21) : (stubEnter state).getReg r = state.getReg r := by
    unfold stubEnter; rw [reg_addi _ _ _ _ _ (Ne.symm h), reg_jal]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold truncLower
    rw [reg_addi _ _ _ _ _ (by decide), reg_addi _ _ _ _ _ (by decide), reg_addi _ _ _ _ _ (by decide),
      reg_add _ _ _ _ _ (by decide), back _ (by decide), enter21]
  · unfold truncLower
    rw [reg_addi _ _ _ _ _ (by decide), reg_addi _ _ _ _ _ (by decide), reg_addi _ _ _ _ _ (by decide)]
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x6 ≠ .x0 by decide)]
    rw [back _ (by decide), back _ (by decide), enter _ (by decide), enter _ (by decide)]
  · unfold truncLower
    rw [reg_addi _ _ _ _ _ (by decide), reg_addi _ _ _ _ _ (by decide)]
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x11 ≠ .x0 by decide)]
    rfl
  · unfold truncLower
    rw [reg_addi _ _ _ _ _ (by decide)]
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x13 ≠ .x0 by decide)]
    rfl
  · unfold truncLower
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x29 ≠ .x0 by decide)]
    rfl

theorem trunc_lower_mem (state : MachineState) (digest : state.getReg .x23 = 12288) (a : Word) :
    (truncLower state).mem a = if a = wordAddress 1539 then state.mem a &&& leafMask else state.mem a := by
  have stored : (truncLower state).mem =
      ((stubMask state).setMem ((stubMask state).getReg .x23 + signExtend12 24)
        ((stubMask state).getReg .x31)).mem := by
    unfold truncLower stubBack
    rw [mem_addi, mem_addi, mem_addi, mem_add, mem_jal]
    rfl
  have value : (stubMask state).getReg .x31 =
      (state.mem (state.getReg .x23 + signExtend12 24) <<< (11 : Nat)) >>> (11 : Nat) := by
    unfold stubMask stubLoad
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x31 ≠ .x0 by decide),
      MachineState.getMem]
    rw [enter_x23, show (stubEnter state).mem = state.mem by unfold stubEnter; rw [mem_addi, mem_jal]]
    rfl
  have sameMem : (stubMask state).mem = state.mem := by
    unfold stubMask stubLoad stubEnter
    rw [mem_srli, mem_slli, mem_ld, mem_addi, mem_jal]
  have addr : state.getReg .x23 + signExtend12 24 = wordAddress 1539 := by rw [digest]; decide
  rw [stored, mask_x23, value, addr, shift_mask]
  simp only [MachineState.setMem, sameMem]
  by_cases hit : a = wordAddress 1539
  · subst hit; simp
  · simp [hit]

theorem trunc_lower_frame (state : MachineState) (digest : state.getReg .x23 = 12288) (word : Nat)
    (bound : word < 2^61) (away : word ≠ 1539) :
    memoryView (truncLower state) word = memoryView state word := by
  change (truncLower state).mem (wordAddress word) = state.mem (wordAddress word)
  rw [trunc_lower_mem state digest, if_neg]
  intro same
  have n := congrArg BitVec.toNat same
  simp only [wordAddress, BitVec.toNat_ofNat] at n
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at n
  omega

private theorem buffer_of_words (state : MachineState) (start : Nat) (expected : BitVec 256)
    (words : ∀ k < 4, memoryView state (start+k)=expected.extractLsb' (64*k) 64) :
    readBuffer state (8*start) 32=expected := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let k := bit/64
  have bound : k<4 := by dsimp [k];omega
  have chunk := read_buffer_slice state (8*start) 32 (8*k) 8 (by omega)
  rw [show 8*start+8*k=8*(start+k) by omega,TwoPermutationPrototype.Checker.read_word,words k bound] at chunk
  have bits := congrArg (fun w : BitVec 64 => w.getLsbD (bit%64)) chunk
  have numeric : 64*k+bit%64=bit := by dsimp [k];omega
  simpa only [←Nat.mul_assoc, Nat.reduceMul, BitVec.getLsbD_extractLsb',show bit%64<64 by omega,
    decide_true,Bool.true_and,numeric] using bits

/-- After the stub the digest buffer holds the leaf digest cut to 245 bits. -/
theorem trunc_lower_digest (state : MachineState) (digest : state.getReg .x23 = 12288) :
    readBuffer (truncLower state) 12288 32 =
      BitVec.ofNat 256 ((readBuffer state 12288 32).toNat % 2^245) := by
  rw [show (12288 : Nat) = 8*1536 from rfl]
  apply buffer_of_words _ 1536
  intro k hk
  have word := read_digest_word state (8*1536) k (by decide) (by omega)
  have place : wordAddress (1536+k) = BitVec.ofNat 64 (8*1536+8*k) := by
    unfold wordAddress; congr 1; omega
  change (truncLower state).mem (wordAddress (1536+k)) = _
  rw [trunc_lower_mem state digest]
  by_cases top : k = 3
  · subst top
    rw [if_pos rfl, trunc_top_word, word, place]
    rfl
  · rw [if_neg, trunc_low_word _ k (by omega), word, place]
    · rfl
    · intro same
      have n := congrArg BitVec.toNat same
      simp only [wordAddress, BitVec.toNat_ofNat] at n
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at n
      omega

end TwoPermutationPrototype.Packed.RecordLeaf
