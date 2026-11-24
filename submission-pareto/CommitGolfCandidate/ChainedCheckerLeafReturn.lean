import CommitGolfCandidate.ChainedCheckerLeafData
import CommitGolfCandidate.TwoPermutationLeafMask

/-! Delivered word2432 return: nonce advance, 238-bit leaf mask and lower setup. -/
namespace CommitGolfCandidate.Chained.Native.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling SplitCodec
private abbrev packedImage : Image := Artifact.submission.image .check
set_option maxRecDepth 8192

/-- Fetch from anywhere in the delivered checker image. -/
theorem trunc_fetch (s : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index<3012) (pc : s.pc=BitVec.ofNat 64 (4096+4*index))
    (decoded : chainedCheckerOps.getD index .EBREAK=instruction) :
    fetch packedImage s=some (.base instruction) := by
  rw [packedImage,checking_manifest_image,←decoded]
  apply chained_checker_ops_at index (by rw [chained_checker_ops_length]; exact bounded) s
  rw [pc,BitVec.ofNat_add]
  rfl

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

/-- Jump to the stub and advance the proof cursor (stub word 2751). -/
def stubEnter (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (.JAL .x0 1276)) (.ADDI .x21 .x21 16)
/-- `ld t6,24(s7)`. -/
def stubLoad (s : MachineState) : MachineState := execInstrBr (stubEnter s) (.LD .x31 .x23 24)
/-- `slli t6,t6,18; srli t6,t6,18`. -/
def stubMask (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (stubLoad s) (.SLLI .x31 .x31 18)) (.SRLI .x31 .x31 18)
/-- `sd t6,24(s7); jal 2433`. -/
def stubBack (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (stubMask s) (.SD .x23 .x31 24)) (.JAL .x0 2095860)
/-- The lower setup with the leaf truncation stub. -/
def truncLower (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20))
    (.ADDI .x11 .x0 64)) (.ADDI .x13 .x0 0)) (.ADDI .x29 .x0 16)

section Facts
variable (s : MachineState) (pc : s.pc = (4096+4*2432))
include pc

private theorem enter_pc0 : (execInstrBr s (.JAL .x0 1276)).pc = BitVec.ofNat 64 (4096+4*2751) := by
  rw [pc_jal, pc]; decide
private theorem enter_pc : (stubEnter s).pc = BitVec.ofNat 64 (4096+4*2752) := by
  unfold stubEnter; rw [pc_addi, enter_pc0 s pc]; decide
private theorem load_pc : (stubLoad s).pc = BitVec.ofNat 64 (4096+4*2753) := by
  unfold stubLoad; rw [pc_ld, enter_pc s pc]; decide
private theorem slli_pc : (execInstrBr (stubLoad s) (.SLLI .x31 .x31 18)).pc = BitVec.ofNat 64 (4096+4*2754) := by
  rw [pc_slli, load_pc s pc]; decide
private theorem mask_pc : (stubMask s).pc = BitVec.ofNat 64 (4096+4*2755) := by
  unfold stubMask; rw [pc_srli, slli_pc s pc]; decide
private theorem store_pc : (execInstrBr (stubMask s) (.SD .x23 .x31 24)).pc = BitVec.ofNat 64 (4096+4*2756) := by
  rw [pc_sd, mask_pc s pc]; decide
private theorem back_pc : (stubBack s).pc = BitVec.ofNat 64 (4096+4*2433) := by
  unfold stubBack; rw [pc_jal, store_pc s pc]; decide
private theorem add_pc : (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20)).pc = BitVec.ofNat 64 (4096+4*2434) := by
  rw [pc_add, back_pc s pc]; decide
private theorem size_pc :
    (execInstrBr (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20)) (.ADDI .x11 .x0 64)).pc =
      BitVec.ofNat 64 (4096+4*2435) := by
  rw [pc_addi, add_pc s pc]; decide
private theorem kind_pc :
    (execInstrBr (execInstrBr (execInstrBr (stubBack s) (.ADD .x6 .x6 .x20)) (.ADDI .x11 .x0 64))
      (.ADDI .x13 .x0 0)).pc = BitVec.ofNat 64 (4096+4*2436) := by
  rw [pc_addi, size_pc s pc]; decide

theorem trunc_lower_pc : (truncLower s).pc = 4096+4*2437 := by
  unfold truncLower; rw [pc_addi, kind_pc s pc]; decide

end Facts

private theorem enter_x23 (s : MachineState) : (stubEnter s).getReg .x23 = s.getReg .x23 := by
  unfold stubEnter; rw [reg_addi _ _ _ _ _ (by decide), reg_jal]
private theorem mask_x23 (s : MachineState) : (stubMask s).getReg .x23 = s.getReg .x23 := by
  unfold stubMask stubLoad
  rw [reg_srli _ _ _ _ _ (by decide), reg_slli _ _ _ _ _ (by decide), reg_ld _ _ _ _ _ (by decide), enter_x23]

private theorem step_one (t next : MachineState) (I : Instr) (k : Nat) (hk : k < 3012)
    (pc : t.pc = BitVec.ofNat 64 (4096+4*k))
    (dec : chainedCheckerOps.getD k .EBREAK=I)
    (step : ordinaryStep t (.base I) = some next) (cyc : instructionCycles (.base I) = 1) (fuel : Nat) :
    execute packedImage (fuel+1) t false =
      (do let result ← execute packedImage fuel next false; return result.charge 1 0) := by
  rw [execute_ordinary_step _ _ _ _ _ _ (trunc_fetch t k I hk pc dec) step, cyc]

theorem execute_trunc_lower (state : MachineState) (pc : state.pc = (4096+4*2432))
    (digest : state.getReg .x23 = 12288) (fuel : Nat) :
    execute packedImage (11+fuel) state false =
      (do let result ← execute packedImage fuel (truncLower state) false
          return result.charge 11 0) := by
  have pc58 : state.pc = BitVec.ofNat 64 (4096+4*2432) := by rw [pc]; decide
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
    step_one _ _ (.JAL .x0 1276) 2432 (by decide) pc58 rfl rfl rfl,
    step_one _ (stubEnter state) (.ADDI .x21 .x21 16) 2751 (by decide) (enter_pc0 state pc) rfl rfl rfl,
    step_one _ (stubLoad state) (.LD .x31 .x23 24) 2752 (by decide) (enter_pc state pc) rfl stepLoad rfl,
    step_one _ _ (.SLLI .x31 .x31 18) 2753 (by decide) (load_pc state pc) rfl rfl rfl,
    step_one _ (stubMask state) (.SRLI .x31 .x31 18) 2754 (by decide) (slli_pc state pc) rfl rfl rfl,
    step_one _ _ (.SD .x23 .x31 24) 2755 (by decide) (mask_pc state pc) rfl stepStore rfl,
    step_one _ (stubBack state) (.JAL .x0 2095860) 2756 (by decide) (store_pc state pc) rfl rfl rfl,
    step_one _ _ (.ADD .x6 .x6 .x20) 2433 (by decide) (back_pc state pc) rfl rfl rfl,
    step_one _ _ (.ADDI .x11 .x0 64) 2434 (by decide) (add_pc state pc) rfl rfl rfl,
    step_one _ _ (.ADDI .x13 .x0 0) 2435 (by decide) (size_pc state pc) rfl rfl rfl,
    step_one _ (truncLower state) (.ADDI .x29 .x0 16) 2436 (by decide) (kind_pc state pc) rfl rfl rfl]
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
      (state.mem (state.getReg .x23 + signExtend12 24) <<< (18 : Nat)) >>> (18 : Nat) := by
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

private theorem trunc_read_word (state : MachineState) (word : Nat) :
    readBuffer state (8*word) 8=memoryView state word := by
  have slice := read_buffer_slice state (8*word) 32 0 8 (by decide)
  have loaded := read_digest_word state (8*word) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero,memoryView,wordAddress] using slice.symm.trans loaded

private theorem buffer_of_words (state : MachineState) (start : Nat) (expected : BitVec 256)
    (words : ∀ k < 4, memoryView state (start+k)=expected.extractLsb' (64*k) 64) :
    readBuffer state (8*start) 32=expected := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let k := bit/64
  have bound : k<4 := by dsimp [k];omega
  have chunk := read_buffer_slice state (8*start) 32 (8*k) 8 (by omega)
  rw [show 8*start+8*k=8*(start+k) by omega,trunc_read_word,words k bound] at chunk
  have bits := congrArg (fun w : BitVec 64 => w.getLsbD (bit%64)) chunk
  have numeric : 64*k+bit%64=bit := by dsimp [k];omega
  simpa only [←Nat.mul_assoc, Nat.reduceMul, BitVec.getLsbD_extractLsb',show bit%64<64 by omega,
    decide_true,Bool.true_and,numeric] using bits

/-- After the stub the digest buffer holds the leaf digest cut to 238 bits. -/
theorem trunc_lower_digest (state : MachineState) (digest : state.getReg .x23 = 12288) :
    readBuffer (truncLower state) 12288 32 =
      BitVec.ofNat 256 ((readBuffer state 12288 32).toNat % 2^238) := by
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

@[irreducible] def checkerLeafPathState (s : MachineState) : MachineState := truncLower s

theorem checker_leaf_path_eq (s : MachineState) : checkerLeafPathState s=truncLower s := by rw [checkerLeafPathState]

theorem checker_leaf_path_execution (s : MachineState) (pc : s.pc=4096+4*2432)
    (digest : s.getReg .x23=12288) (fuel : Nat) :
    execute (Artifact.submission.image .check) (11+fuel) s false=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLeafPathState s) false
          return result.charge 11 0) := by
  rw [checker_leaf_path_eq]
  exact execute_trunc_lower s pc digest fuel

theorem checker_leaf_path_pc {s : MachineState} {source nonce : Nat} {index : Index}
    (ready : LeafReady s source nonce index) (a b : Block) :
    (checkerLeafPathState (secondReplyState s source a b)).pc=4096+4*2437 := by
  rw [checker_leaf_path_eq]
  exact trunc_lower_pc _ (checker_leaf_finished_pc ready a b)

theorem checker_leaf_path_digest {s : MachineState} {source nonce : Nat} {index : Index}
    (ready : LeafReady s source nonce index) (a b : Block) :
    readBuffer (checkerLeafPathState (secondReplyState s source a b)) 12288 32=
      BitVec.ofNat 256 ((outputDigest b).toNat%2^238) := by
  have destination : (secondReplyState s source a b).getReg .x23=12288 :=
    (checker_leaf_preserved_register s source a b .x23 (by decide) (by decide) (by decide)).trans ready.destination
  rw [checker_leaf_path_eq,trunc_lower_digest _ destination,checker_leaf_digest]

theorem checker_decoded_path_execution (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (fuel : Nat) :
    execute (Artifact.submission.image .check) (2120+fuel) s false=
      (do let after ← leafQueries (checkerRecordNonceState s) 754975239 (checkerFirstInputIndex input nonempty)
          let result ← execute (Artifact.submission.image .check) fuel (checkerLeafPathState after) false
          return result.charge 2134 2) := by
  rw [show 2120+fuel=2109+(11+fuel) by omega,checker_decoded_leaf_execution input nonempty footer s ready]
  simp only [leafQueries,bind_assoc,pure_bind]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  have args := checker_record_leaf_ready input nonempty footer s ready
  have destination : (secondReplyState (checkerRecordNonceState s) 754975239 a b).getReg .x23=12288 :=
    (checker_leaf_preserved_register _ _ _ _ .x23 (by decide) (by decide) (by decide)).trans args.destination
  rw [checker_leaf_path_execution _ (checker_leaf_finished_pc args a b) destination]
  simp [Execution.charge,←Nat.add_assoc]

theorem checker_first_path_register (s : MachineState) (a b : Block) (reg : Reg)
    (kept : reg∉[.x5,.x6,.x10,.x11,.x12,.x13,.x21,.x28,.x29,.x31]) :
    (checkerLeafPathState (secondReplyState (checkerRecordNonceState s) 754975239 a b)).getReg reg=
      (checkerCryptoRecordState s).getReg reg := by
  have different (other : Reg) (member : other∈[.x5,.x6,.x10,.x11,.x12,.x13,.x21,.x28,.x29,.x31]) :
      reg≠other := by
    intro equal
    subst reg
    exact kept member
  rw [checker_leaf_path_eq,trunc_lower_register _ reg (different .x21 (by decide))
    (different .x6 (by decide)) (different .x11 (by decide)) (different .x13 (by decide))
    (different .x29 (by decide)) (different .x31 (by decide)),
    checker_leaf_preserved_register _ _ _ _ reg (different .x10 (by decide))
      (different .x12 (by decide)) (different .x31 (by decide)),checker_record_nonce_eq,
    checker_copy_register .nonce _ reg (different .x31 (by decide))]
  apply checker_leaf_head_register 7 _ (by decide) reg
  intro member
  have subset : ([.x5,.x6,.x28,.x10,.x11,.x13] : List Reg)⊆
      [.x5,.x6,.x10,.x11,.x12,.x13,.x21,.x28,.x29,.x31] := by decide +kernel
  exact kept (subset member)

structure CheckerRecordBase where
  value : Nat
  above : 32768≤value
  even : value%2=0
  room : value+528≤MEMORY_BYTES

def checkerDefaultRecordBase : CheckerRecordBase :=
  ⟨checkingRawBase,by decide +kernel,by decide +kernel,by decide +kernel⟩

def checkerRecordBaseAt (record : Fin LENGTH) : CheckerRecordBase where
  value := checkingRawBase+498*record.val
  above := by
    have low : 32768≤checkingRawBase := checkerDefaultRecordBase.above
    omega
  even := by
    have even : checkingRawBase%2=0 := checkerDefaultRecordBase.even
    simp [Nat.add_mod,Nat.mul_mod,even]
  room := by
    have bound : record.val<16777216 := record.isLt
    have slack : checkingRawBase+498*16777216+528≤MEMORY_BYTES := by decide +kernel
    omega

structure CheckerFirstPathReady (input : CheckInput) (s : MachineState)
    (base : CheckerRecordBase := checkerDefaultRecordBase) (record : Nat := 0) : Prop where
  pc : s.pc=4096+4*2437
  source : s.getReg .x21=BitVec.ofNat 64 (base.value+16)
  node : s.getReg .x6=BitVec.ofNat 64 (LENGTH+((input.positions.sort (·≤·))[record]?.getD (⟨0,by decide⟩ : Index)).val)
  digest : s.getReg .x23=12288
  pair : s.getReg .x24=12544
  counter : s.getReg .x29=16
  size : s.getReg .x11=64
  primitive : s.getReg .x13=0

theorem checker_first_path_ready (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (a b : Block) :
    CheckerFirstPathReady input (checkerLeafPathState (secondReplyState (checkerRecordNonceState s) 754975239 a b)) := by
  have args := checker_record_leaf_ready input nonempty footer s ready
  have post := trunc_lower_post (secondReplyState (checkerRecordNonceState s) 754975239 a b)
  have pointer : (checkerRecordNonceState s).getReg .x21=BitVec.ofNat 64 checkingRawBase := by
    rw [checker_record_nonce_eq,checker_copy_register .nonce _ .x21 (by decide)]
    exact (checker_record_nonce_ready input footer s ready).src
  have size : (checkerRecordNonceState s).getReg .x20=16777216#64 := by
    rw [checker_record_nonce_eq,checker_copy_register .nonce _ .x20 (by decide),
      checker_leaf_head_register 7 _ (by decide) .x20 (by decide),
      checker_crypto_record_assigned s .x20 (by decide +kernel)]
    rfl
  refine ⟨checker_leaf_path_pc args a b,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [checker_leaf_path_eq,post.1,checker_leaf_preserved_register _ _ _ _ .x21 (by decide) (by decide) (by decide),pointer]
    change BitVec.ofNat 64 checkingRawBase+BitVec.ofNat 64 16=BitVec.ofNat 64 (checkingRawBase+16)
    rw [BitVec.ofNat_add]
  · rw [checker_leaf_path_eq,post.2.1,
      checker_leaf_preserved_register _ _ _ _ .x6 (by decide) (by decide) (by decide),
      checker_leaf_preserved_register _ _ _ _ .x20 (by decide) (by decide) (by decide),
      checker_record_nonce_index input nonempty footer s ready,size]
    have present : 0<(input.positions.sort (·≤·)).length := by simpa only [Finset.length_sort] using Nat.pos_of_ne_zero nonempty
    simp only [List.getElem?_eq_getElem present,Option.getD_some]
    change BitVec.ofNat 64 (checkerFirstInputIndex input nonempty).val+BitVec.ofNat 64 16777216=
      BitVec.ofNat 64 (16777216+(checkerFirstInputIndex input nonempty).val)
    rw [←BitVec.ofNat_add,Nat.add_comm]
  · rw [checker_first_path_register s a b .x23 (by decide),checker_crypto_record_assigned s .x23 (by decide +kernel)]
    rfl
  · rw [checker_first_path_register s a b .x24 (by decide),checker_crypto_record_assigned s .x24 (by decide +kernel)]
    rfl
  · rw [checker_leaf_path_eq,post.2.2.2.2]
  · rw [checker_leaf_path_eq,post.2.2.1]
  · rw [checker_leaf_path_eq,post.2.2.2.1]

theorem checker_record_path_ready {input : CheckInput} {base : CheckerRecordBase} {record : Nat}
    {state : MachineState} {src nonce : Nat}
    (ready : LeafReady state src nonce ((input.positions.sort (·≤·))[record]?.getD (⟨0,by decide⟩ : Index)))
    (pointer : state.getReg .x21=BitVec.ofNat 64 base.value)
    (node : state.getReg .x6=BitVec.ofNat 64 (((input.positions.sort (·≤·))[record]?.getD (⟨0,by decide⟩ : Index)).val))
    (length : state.getReg .x20=BitVec.ofNat 64 LENGTH) (pair : state.getReg .x24=12544)
    (a b : Block) :
    CheckerFirstPathReady input (checkerLeafPathState (secondReplyState state src a b)) base record := by
  have post := trunc_lower_post (secondReplyState state src a b)
  refine ⟨checker_leaf_path_pc ready a b,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [checker_leaf_path_eq,post.1,
      checker_leaf_preserved_register _ _ _ _ .x21 (by decide) (by decide) (by decide),pointer,
      BitVec.ofNat_add]
    congr 1 <;> decide +kernel
  · rw [checker_leaf_path_eq,post.2.1,
      checker_leaf_preserved_register _ _ _ _ .x6 (by decide) (by decide) (by decide),
      checker_leaf_preserved_register _ _ _ _ .x20 (by decide) (by decide) (by decide),node,length,
      ←BitVec.ofNat_add,Nat.add_comm]
  · rw [checker_leaf_path_eq,trunc_lower_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      checker_leaf_preserved_register _ _ _ _ .x23 (by decide) (by decide) (by decide)]
    exact ready.destination
  · rw [checker_leaf_path_eq,trunc_lower_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      checker_leaf_preserved_register _ _ _ _ .x24 (by decide) (by decide) (by decide),pair]
  · rw [checker_leaf_path_eq,post.2.2.2.2]
  · rw [checker_leaf_path_eq,post.2.2.1]
  · rw [checker_leaf_path_eq,post.2.2.2.1]

@[irreducible] def checkerRecordHeadPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i before => execInstrBr before (checkerLeafHeadOps.getD (i+1) .EBREAK)) n

theorem checker_record_head_zero (s : MachineState) : checkerRecordHeadPrefix 0 s=s := by
  rw [checkerRecordHeadPrefix]; rfl

theorem checker_record_head_succ (n : Nat) (s : MachineState) : checkerRecordHeadPrefix (n+1) s=
    execInstrBr (checkerRecordHeadPrefix n s) (checkerLeafHeadOps.getD (n+1) .EBREAK) := by
  unfold checkerRecordHeadPrefix; rfl

theorem checker_record_head_pc (n : Nat) (s : MachineState) (small : n≤6) :
    (checkerRecordHeadPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 6) :
      (execInstrBr t (checkerLeafHeadOps.getD (i.val+1) .EBREAK)).pc=t.pc+4 := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_record_head_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_record_head_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    change s.pc+(BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4)=s.pc+BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 2

theorem checker_record_head_register (n : Nat) (s : MachineState) (small : n≤6) (reg : Reg)
    (kept : reg∉[.x6,.x28,.x10,.x11,.x13]) : (checkerRecordHeadPrefix n s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Fin 6) :
      (execInstrBr t (checkerLeafHeadOps.getD (i.val+1) .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases i <;> cases reg <;> simp at kept <;> rfl
  induction n with
  | zero => rw [checker_record_head_zero]
  | succ n ih => rw [checker_record_head_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_record_head_memory (n : Nat) (s : MachineState) (small : n≤6) (query : Word) :
    (checkerRecordHeadPrefix n s).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 6) :
      (execInstrBr t (checkerLeafHeadOps.getD (i.val+1) .EBREAK)).getMem query=t.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_record_head_zero]
  | succ n ih => rw [checker_record_head_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_record_head_values (s : MachineState) :
    let next := checkerRecordHeadPrefix 6 s
    next.getReg .x6=s.getMem (s.getReg .x8) ∧
    next.getReg .x28=s.getReg .x3+(s.getMem (s.getReg .x8) <<< 8) ∧
    next.getReg .x10=s.getReg .x19 ∧ next.getReg .x11=200 ∧ next.getReg .x13=1 := by
  dsimp only
  rw [checker_record_head_succ 5,checker_record_head_succ 4,checker_record_head_succ 3,
    checker_record_head_succ 2,checker_record_head_succ 1,checker_record_head_succ 0,
    checker_record_head_zero]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals simp [checkerLeafHeadOps,execInstrBr,Opening.getReg_setReg,
    Opening.getReg_setMem,MachineState.getReg_setPC,signExtend12]
  all_goals rfl

theorem checker_record_head_execution (s : MachineState) (pc : s.pc=4096+4*2396)
    (valid : accessValid (s.getReg .x8) 8=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (6+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordHeadPrefix 6 s) coins
          return result.charge 6 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_record_head_zero s]
  apply execute_unit_steps (states := fun n => checkerRecordHeadPrefix n s)
  intro i inside
  refine ⟨.base (checkerLeafHeadOps.getD (i+1) .EBREAK),?_,?_,?_⟩
  · apply checker_leaf_head_at (i+1) (by change i+1<7; omega)
    rw [checker_record_head_pc i s (by omega),pc]
    change BitVec.ofNat 64 (4096+4*2396)+BitVec.ofNat 64 (4*i)=
      BitVec.ofNat 64 (4096+4*2395)+BitVec.ofNat 64 (4*(i+1))
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    congr 1
    omega
  · rw [checker_record_head_succ]
    interval_cases i
    · rw [checker_record_head_zero]
      change (if accessValid (s.getReg .x8+0#64) 8 then _ else _)=_
      rw [BitVec.add_zero]
      exact ite_eq_left valid
    all_goals rfl
  · interval_cases i <;> rfl

def checkerRecordInputIndex (input : CheckInput) (record : Nat) : Index :=
  (input.positions.sort (·≤·))[record]?.getD ⟨0,by decide⟩

structure CheckerRecordCoreReady (input : CheckInput) (record : Nat) (base : CheckerRecordBase)
    (src : Nat) (s : MachineState) : Prop where
  pc : s.pc=4096+4*2396
  access : accessValid (s.getReg .x8) 8=true
  loaded : s.getMem (s.getReg .x8)=BitVec.ofNat 64 (checkerRecordInputIndex input record).val
  cursor : s.getReg .x21=BitVec.ofNat 64 base.value
  source : s.getReg .x19=wordAddress src
  nonce : s.getReg .x4=12272
  digest : s.getReg .x23=12288
  pair : s.getReg .x24=12544
  tagBase : s.getReg .x3=4056
  length : s.getReg .x20=BitVec.ofNat 64 LENGTH
  selector : s.getReg .x5=0
  separated : 1536≤src
  endBound : src+37≤2^33

theorem checker_record_core_nonce_ready {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s : MachineState} (ready : CheckerRecordCoreReady input record base src s) :
    TwoPermutationPrototype.Packed.CopyReady (checkerCopyCode .nonce) (checkerRecordHeadPrefix 6 s)
      base.value 12272 0 := by
  refine ⟨?_,?_,?_,?_,by decide,base.even,by decide⟩
  · change (checkerRecordHeadPrefix 6 s).pc=BitVec.ofNat 64 (4096+4*2402)
    rw [checker_record_head_pc 6 s (by decide),ready.pc]
    rfl
  · exact (checker_record_head_register 6 s (by decide) .x21 (by decide)).trans ready.cursor
  · change (checkerRecordHeadPrefix 6 s).getReg .x4+0#64=12272#64
    rw [BitVec.add_zero,checker_record_head_register 6 s (by decide) .x4 (by decide),ready.nonce]
    decide +kernel
  · change base.value+16≤MEMORY_BYTES
    have := base.room
    omega

@[irreducible] def checkerRecordCoreNonceState (s : MachineState) : MachineState :=
  checkerCopyState .nonce (checkerRecordHeadPrefix 6 s)

theorem checker_record_core_nonce_execution {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s : MachineState} (ready : CheckerRecordCoreReady input record base src s)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (22+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordCoreNonceState s) coins
          return result.charge 22 0) := by
  rw [checkerRecordCoreNonceState,
    show 22+fuel=6+(2*CheckerCopySite.nonce.count+fuel) by simp only [CheckerCopySite.count]; omega,
    checker_record_head_execution s ready.pc ready.access,
    checker_copy_execution .nonce _ base.value 12272 (checker_record_core_nonce_ready ready)]
  simp [Execution.charge,CheckerCopySite.count,←Nat.add_assoc]

theorem checker_record_core_leaf_ready {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s : MachineState} (ready : CheckerRecordCoreReady input record base src s) :
    LeafReady (checkerRecordCoreNonceState s) src 1534 (checkerRecordInputIndex input record) := by
  have kept (reg : Reg) (other : reg≠.x31) : (checkerRecordCoreNonceState s).getReg reg=
      (checkerRecordHeadPrefix 6 s).getReg reg := by
    rw [checkerRecordCoreNonceState,checker_copy_register .nonce _ reg other]
  have values := checker_record_head_values s
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,ready.separated,ready.endBound⟩
  · rw [checkerRecordCoreNonceState,
      checker_copy_pc .nonce _ base.value 12272 (checker_record_core_nonce_ready ready)]
    rfl
  · rw [kept .x10 (by decide),values.2.2.1,ready.source]
  · rw [kept .x4 (by decide),checker_record_head_register 6 s (by decide) .x4 (by decide)]
    exact ready.nonce
  · rw [kept .x23 (by decide),checker_record_head_register 6 s (by decide) .x23 (by decide)]
    exact ready.digest
  · rw [kept .x28 (by decide),values.2.1,ready.loaded,ready.tagBase]
    change 4056#64+(BitVec.ofNat 64 (checkerRecordInputIndex input record).val <<< 8)=
      BitVec.ofNat 64 (4056+256*(checkerRecordInputIndex input record).val)
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 4056+BitVec.ofNat 64 (checkerRecordInputIndex input record).val*BitVec.ofNat 64 256=_
    rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
    congr 1
    omega
  · rw [kept .x5 (by decide),checker_record_head_register 6 s (by decide) .x5 (by decide),ready.selector]
  · rw [kept .x11 (by decide),values.2.2.2.1]
  · rw [kept .x13 (by decide),values.2.2.2.2]

theorem checker_record_core_path_ready {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s : MachineState} (ready : CheckerRecordCoreReady input record base src s) (a b : Block) :
    CheckerFirstPathReady input (checkerLeafPathState (secondReplyState (checkerRecordCoreNonceState s) src a b)) base record := by
  have kept (reg : Reg) (other : reg≠.x31) (head : reg∉[.x6,.x28,.x10,.x11,.x13]) :
      (checkerRecordCoreNonceState s).getReg reg=s.getReg reg := by
    rw [checkerRecordCoreNonceState,checker_copy_register .nonce _ reg other,
      checker_record_head_register 6 s (by decide) reg head]
  have node : (checkerRecordCoreNonceState s).getReg .x6=
      BitVec.ofNat 64 (checkerRecordInputIndex input record).val := by
    rw [checkerRecordCoreNonceState,checker_copy_register .nonce _ .x6 (by decide),
      (checker_record_head_values s).1,ready.loaded]
  exact checker_record_path_ready (checker_record_core_leaf_ready ready)
    ((kept .x21 (by decide) (by decide)).trans ready.cursor) node
    ((kept .x20 (by decide) (by decide)).trans ready.length)
    ((kept .x24 (by decide) (by decide)).trans ready.pair) a b

theorem checker_record_core_path_execution {input : CheckInput} {record : Nat} {base : CheckerRecordBase}
    {src : Nat} {s : MachineState} (ready : CheckerRecordCoreReady input record base src s) (fuel : Nat) :
    execute (Artifact.submission.image .check) (47+fuel) s false=
      (do let after ← leafQueries (checkerRecordCoreNonceState s) src (checkerRecordInputIndex input record)
          let result ← execute (Artifact.submission.image .check) fuel (checkerLeafPathState after) false
          return result.charge 61 2) := by
  rw [show 47+fuel=22+(14+(11+fuel)) by omega,checker_record_core_nonce_execution ready]
  have args := checker_record_core_leaf_ready ready
  rw [execute_checker_leaf args]
  simp only [leafQueries,bind_assoc,pure_bind]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  have destination : (secondReplyState (checkerRecordCoreNonceState s) src a b).getReg .x23=12288 :=
    (checker_leaf_preserved_register _ _ _ _ .x23 (by decide) (by decide) (by decide)).trans args.destination
  rw [checker_leaf_path_execution _ (checker_leaf_finished_pc args a b) destination]
  simp [Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Chained.Native.RecordLeaf
