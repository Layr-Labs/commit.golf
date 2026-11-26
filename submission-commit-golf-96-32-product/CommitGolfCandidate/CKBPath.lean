import CommitGolfCandidate.LateNormalCommon
import CommitGolfCandidate.LateCheckCall
import CommitGolfCandidate.CMHalf
import CommitGolfCandidate.CKBHalf
import CommitGolfCandidate.Model
import CommitGolfCandidate.LateCheckModel

/-! A96 batch authentication path `bpath` (check words 458..631), entered from word 218 after the leaf.
Words 458..461 set x9 := 0x1FFFC (bit l of x9 selects the 240-bit store of the level-l parent, i.e. the
cut heights 3..17) and x29 := 3. Loop A (words 462..546, three levels) copies full 32-byte siblings with
sixteen halfword copies; loop B (words 548..630, thirteen levels) copies 30-byte siblings and zeroes the
sibling's top halfword. Both hash through the truncating adapter `tcomp`. Word 631 jumps to word 256. -/
namespace CommitGolfCandidate.Late.Check.Micro.CKBPath
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W wordAt Outside)
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

/-! ### Generic pieces -/

theorem stepOne (n : Nat) (hn : n<814) (op : Instr)
    (enc : decodeInstruction (checkWord n)=some (.base op)) (s : MachineState) (pc : s.pc=pcAt n)
    (plain : ordinaryStep s (.base op) = if memoryArgumentsValid s op then some (execInstrBr s op) else none)
    (valid : memoryArgumentsValid s op = true) (cyc : instructionCycles (.base op) = 1) :
    Runs s (execInstrBr s op) 1 1 := by
  have h := one n hn op enc s (execInstrBr s op) pc (by rw [plain, if_pos valid])
  rw [cyc] at h; exact h

theorem outside_refl (s : MachineState) : Outside s s 256 64 := fun _ _ _ _ => rfl

theorem outside_trans {s m t : MachineState} (a : Outside s m 256 64) (b : Outside m t 256 64) :
    Outside s t 256 64 := fun q hq al o => (b q hq al o).trans (a q hq al o)

theorem outside_pc (s : MachineState) (p : Word) : Outside s (s.setPC p) 256 64 := fun _ _ _ _ => rfl

theorem outside_reg (s : MachineState) (r : Reg) (v : Word) : Outside s (s.setReg r v) 256 64 := by
  intro _ _ _ _; cases r <;> rfl

theorem outside_mem {s t : MachineState} (h : t.mem = s.mem) : Outside s t 256 64 := by
  intro q _ _ _; unfold wordAt; simp only [MachineState.getMem, h]

theorem pcAt_add (n k : Nat) : pcAt n+BitVec.ofNat 64 (4*k)=pcAt (n+k) := by
  unfold pcAt;rw [←BitVec.ofNat_add];congr 1;omega

theorem pc4 (n : Nat) : pcAt n+4=pcAt (n+1) := (pc_succ n).symm

/-! ### Block copies (from the shared path proofs) -/

def ckb_copyBlock (state : MachineState) (source : Reg) (offset : Nat) : MachineState :=
  ([.LD .x6 source 0, .SD .x21 .x6 (BitVec.ofNat 12 offset),
    .LD .x6 source 8, .SD .x21 .x6 (BitVec.ofNat 12 (offset+8)),
    .LD .x6 source 16, .SD .x21 .x6 (BitVec.ofNat 12 (offset+16)),
    .LD .x6 source 24, .SD .x21 .x6 (BitVec.ofNat 12 (offset+24))] : List Instr).foldl execInstrBr state

theorem ckb_register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

theorem ckb_copy_block_word (state : MachineState) (source : Reg) (offset word : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32) (bounded : word < 4)
    (scratch : state.getReg .x21 = 256)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg source + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    (ckb_copyBlock state source offset).getMem (BitVec.ofNat 64 (256+offset+8*word)) =
      state.getMem (state.getReg source + BitVec.ofNat 64 (8*word)) := by
  have disjoint : ∀ i : Fin 4, ∀ j : Fin 4,
      state.getReg source + BitVec.ofNat 64 (8*i.val) ≠ BitVec.ofNat 64 (256+offset+8*j.val) :=
    fun i j => separated i i.isLt j j.isLt
  rcases offsets with rfl | rfl <;>
    simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul,
      BitVec.add_zero] at disjoint <;>
    simp only [ckb_copyBlock, List.foldl, execInstrBr, signExtend12] <;>
    interval_cases word <;>
    simp [ckb_register_set_mem, scratch, disjoint, Ne.symm notTemp,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem ckb_copy_block_outside (state : MachineState) (source : Reg) (offset : Nat)
    (address : Word) (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256+offset+8*i)) :
    (ckb_copyBlock state source offset).getMem address = state.getMem address := by
  have disjoint : ∀ i : Fin 4, address ≠ BitVec.ofNat 64 (256+offset+8*i.val) :=
    fun i => outside i i.isLt
  rcases offsets with rfl | rfl <;>
    simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reduceMul] at disjoint <;>
    simp only [ckb_copyBlock, List.foldl, execInstrBr, signExtend12] <;>
    simp [ckb_register_set_mem, scratch, disjoint, Ne.symm notTemp,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem ckb_copy_block_digest (state : MachineState) (source : Reg) (offset : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256) (aligned : (state.getReg source).toNat % 8 = 0)
    (separated : ∀ i < 4, ∀ j < 4,
      state.getReg source + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    readBuffer (ckb_copyBlock state source offset) (256+offset) 32 =
      readBuffer state (state.getReg source).toNat 32 := by
  rw [read_digest_words _ _ (by rcases offsets with rfl | rfl <;> decide),
    read_digest_words _ _ aligned]
  have w0 := ckb_copy_block_word state source offset 0 notTemp offsets (by decide) scratch separated
  have w1 := ckb_copy_block_word state source offset 1 notTemp offsets (by decide) scratch separated
  have w2 := ckb_copy_block_word state source offset 2 notTemp offsets (by decide) scratch separated
  have w3 := ckb_copy_block_word state source offset 3 notTemp offsets (by decide) scratch separated
  simp only [Nat.reduceMul, Nat.add_zero, BitVec.add_zero] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ckb_copy_block_register (state : MachineState) (source : Reg) (offset : Nat)
    (reg : Reg) (notTemp : reg ≠ .x6) :
    (ckb_copyBlock state source offset).getReg reg = state.getReg reg := by
  simp [ckb_copyBlock, List.foldl, execInstrBr, ckb_register_set_mem, Ne.symm notTemp,
    MachineState.getReg_setReg_ne]

theorem ckb_copy_block_preserves (state : MachineState) (source : Reg) (offset address : Nat)
    (notTemp : source ≠ .x6) (offsets : offset = 0 ∨ offset = 32)
    (scratch : state.getReg .x21 = 256) (aligned : address % 8 = 0)
    (outside : ∀ i < 4, ∀ j < 4,
      BitVec.ofNat 64 (address+8*i) ≠ BitVec.ofNat 64 (256+offset+8*j)) :
    readBuffer (ckb_copyBlock state source offset) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  exact ckb_copy_block_outside state source offset _ notTemp offsets scratch (outside i hi)


/-! ### Executing the pieces -/

def moveInstrs : List Instr :=
  [.LD .x6 .x21 0, .SD .x21 .x6 (BitVec.ofNat 12 32), .LD .x6 .x21 8, .SD .x21 .x6 (BitVec.ofNat 12 (32+8)),
   .LD .x6 .x21 16, .SD .x21 .x6 (BitVec.ofNat 12 (32+16)), .LD .x6 .x21 24, .SD .x21 .x6 (BitVec.ofNat 12 (32+24))]

def movePre (s : MachineState) (k : Nat) : MachineState := (moveInstrs.take k).foldl execInstrBr s

theorem move_full (s : MachineState) : movePre s 8 = ckb_copyBlock s .x21 32 := rfl

theorem move_reg (s : MachineState) (k : Nat) (hk : k ≤ 8) (r : Reg) (ne : r ≠ .x6) :
    (movePre s k).getReg r = s.getReg r := by
  interval_cases k <;>
    simp only [movePre, moveInstrs, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, ckb_register_set_mem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]

theorem move_pc (s : MachineState) (k : Nat) (hk : k ≤ 8) :
    (movePre s k).pc = s.pc + BitVec.ofNat 64 (4*k) := by
  interval_cases k <;>
    simp [movePre, moveInstrs, execInstrBr, MachineState.setPC, MachineState.setMem, MachineState.setReg,
      BitVec.add_assoc] <;> rfl

theorem move_run (base : Nat) (loc : base = 464 ∨ base = 550) (s : MachineState) (pc : s.pc = pcAt base)
    (sc : s.getReg .x21 = 256) : Runs s (ckb_copyBlock s .x21 32) 8 8 := by
  intro fuel
  rw [Nat.add_comm, ← move_full]
  apply execute_unit_steps (states := movePre s)
  intro i hi
  have r21 : (movePre s i).getReg .x21 = 256 := (move_reg s i (by omega) .x21 (by decide)).trans sc
  refine ⟨.base ((moveInstrs[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched (base+i) (by omega) _ (by rcases loc with rfl | rfl <;> interval_cases i <;> rfl)
    rw [move_pc s i (by omega), pc, pcAt_add]
  · have valid : memoryArgumentsValid (movePre s i) ((moveInstrs[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [moveInstrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, r21] <;> decide
    have next : movePre s (i+1) = execInstrBr (movePre s i) ((moveInstrs[i]?).getD .EBREAK) := by
      interval_cases i <;> rfl
    rw [next]
    interval_cases i <;>
      simp only [moveInstrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte]
  · interval_cases i <;> rfl

/-- `k` halfword copies `lhu x6,(a+2j)(x25); sh x6,(b+2j)(x21)` starting at word `start`. -/
theorem copy_run (start a b k : Nat) (s : MachineState) (pc : s.pc = pcAt start) (bound : start+2*k ≤ 814)
    (words : ∀ j < k, decodeInstruction (checkWord (start+2*j))=some (.base (.LHU .x6 .x25 (BitVec.ofNat 12 (a+2*j)))) ∧
      decodeInstruction (checkWord (start+2*j+1))=some (.base (.SH .x21 .x6 (BitVec.ofNat 12 (b+2*j)))))
    (S D : Nat) (source : s.getReg .x25=W S) (target : s.getReg .x21=W D)
    (ab : a+2*k ≤ 2048) (bb : b+2*k ≤ 2048) (se : (S+a)%2=0) (de : (D+b)%2=0)
    (sb : S+a+2*k≤MEMORY_BYTES) (db : D+b+2*k≤MEMORY_BYTES) :
    Runs s (CKBHalf.halfRun .x25 .x21 s a b k) (2*k) (2*k) := by
  intro fuel
  have run := CKBHalf.half_run_execute image .x25 .x21 s a b S D k (by decide) (by decide) source target
    ab bb se de sb db
    (fun j hj t tp => by
      apply fetched (start+2*j) (by omega) _ (words j hj).1 t
      rw [tp,pc,show 8*j=4*(2*j) by omega,pcAt_add])
    (fun j hj t tp => by
      apply fetched (start+2*j+1) (by omega) _ (words j hj).2 t
      rw [tp,pc,show 8*j+4=4*(2*j+1) by omega,pcAt_add,Nat.add_assoc])
    fuel false
  rw [Nat.add_comm,run]

/-- The top-halfword clear `sh x0,off(x21)` (off = 30 or 62). -/
theorem zero_run (n off : Nat) (hn : n<814) (enc : decodeInstruction (checkWord n)=some (.base (.SH .x21 .x0 (BitVec.ofNat 12 off))))
    (small : off < 2048) (even : off % 2 = 0) (fits : 256+off+2 ≤ 448)
    (s : MachineState) (pc : s.pc=pcAt n) (sc : s.getReg .x21 = 256) :
    Runs s ((s.setHalfword (BitVec.ofNat 64 (256+off)) 0).setPC (pcAt (n+1))) 1 1 := by
  have addr : s.getReg .x21 + signExtend12 (BitVec.ofNat 12 off) = BitVec.ofNat 64 (256+off) := by
    rw [sc, CKBHalf.half_offset off small]; exact (BitVec.ofNat_add 256 off).symm
  have valid : memoryArgumentsValid s (.SH .x21 .x0 (BitVec.ofNat 12 off)) = true := by
    simp only [memoryArgumentsValid, memAccess]
    rw [addr]
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Bool.and_eq_true, decide_eq_true_eq, MEMORY_BYTES]
    omega
  have h := stepOne n hn _ enc s pc rfl valid rfl
  have same : execInstrBr s (.SH .x21 .x0 (BitVec.ofNat 12 off)) =
      (s.setHalfword (BitVec.ofNat 64 (256+off)) 0).setPC (pcAt (n+1)) := by
    simp only [execInstrBr]
    rw [addr, pc, pc4]
    rfl
  rw [same] at h; exact h

theorem jump_run (n target : Nat) (off : BitVec 21) (hn : n<814)
    (enc : decodeInstruction (checkWord n)=some (.base (.JAL .x0 off)))
    (tgt : pcAt n + signExtend21 off = pcAt target)
    (s : MachineState) (pc : s.pc=pcAt n) : Runs s (s.setPC (pcAt target)) 1 1 := by
  have h := stepOne n hn _ enc s pc rfl rfl rfl
  have same : execInstrBr s (.JAL .x0 off) = s.setPC (pcAt target) := by
    simp only [execInstrBr]; rw [pc, tgt]; rfl
  rw [same] at h; exact h

theorem parity_word (idx : Nat) : (W idx &&& 1) = W (idx % 2) := by
  change (BitVec.ofNat 64 idx &&& BitVec.ofNat 64 (2^1-1)) = _
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]; rfl

/-- `andi x7,x20,1; beq x7,x0,target`. -/
theorem branch_run (H target : Nat) (off : BitVec 13) (hn : H+1<814)
    (e0 : decodeInstruction (checkWord H)=some (.base (.ANDI .x7 .x20 1)))
    (e1 : decodeInstruction (checkWord (H+1))=some (.base (.BEQ .x7 .x0 off)))
    (tgt : pcAt (H+1) + signExtend13 off = pcAt target)
    (s : MachineState) (pc : s.pc=pcAt H) (idx : Nat) (ix : s.getReg .x20 = W idx) :
    let a := s.setReg .x7 (W (idx%2))
    Runs s (a.setPC (pcAt (if idx%2=0 then target else H+2))) 2 2 := by
  intro a
  have h0 := stepOne H (by omega) _ e0 s pc rfl rfl rfl
  have s0 : execInstrBr s (.ANDI .x7 .x20 1) = a.setPC (pcAt (H+1)) := by
    simp only [execInstrBr]; rw [ix, show signExtend12 (1 : BitVec 12) = 1 from rfl, parity_word, pc, pc4]
  rw [s0] at h0
  have h1 := stepOne (H+1) hn _ e1 (a.setPC (pcAt (H+1))) rfl rfl rfl rfl
  have s1 : execInstrBr (a.setPC (pcAt (H+1))) (.BEQ .x7 .x0 off) = a.setPC (pcAt (if idx%2=0 then target else H+2)) := by
    simp only [execInstrBr, MachineState.getReg_setPC]
    have r7 : a.getReg .x7 = W (idx%2) := MachineState.getReg_setReg_eq (by decide)
    rw [r7]
    by_cases e : idx%2=0
    · rw [if_pos e, e]
      have eq : (W 0 == a.getReg .x0) = true := by simp only [MachineState.getReg]; decide
      rw [eq]; simp only [↓reduceIte]
      change (a.setPC (pcAt (H+1))).setPC (pcAt (H+1) + signExtend13 off) = _
      rw [tgt]; rfl
    · rw [if_neg e]
      have one' : idx%2=1 := by omega
      rw [one']
      have ne : (W 1 == a.getReg .x0) = false := by
        simp only [MachineState.getReg]; decide
      rw [ne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change (a.setPC (pcAt (H+1))).setPC (pcAt (H+1) + 4) = _
      rw [pc4]; rfl
  rw [s1] at h1
  exact h0.trans h1


/-! ### Compression through `tcomp` and the loop counter -/

theorem compress_run (o : Oracle) (s : MachineState) (start : Nat) (loc : start = 537 ∨ start = 621)
    (pc : s.pc = pcAt start) (sc : s.getReg .x21 = 256) :
    Normal.Runs o s (Normal.checkCompressionState s (o.compression (padInput (readBuffer s 256 64))))
      (5 + tcompSteps s) 1 := by
  intro fuel
  simp only [Normal.obs]
  rw [Normal.check_compression s start (Or.inr loc) pc sc fuel false]
  simp only [Normal.check_evaluation_public_bind, bind_pure_comp, Normal.check_evaluation_map]
  rfl

theorem tcomp_steps_le (s : MachineState) : tcompSteps s ≤ 21 := by
  unfold tcompSteps; split <;> omega

theorem w_add (P k : Nat) (hk : k < 2048) : W P + signExtend12 (BitVec.ofNat 12 k) = W (P+k) := by
  rw [CKBHalf.half_offset k hk]; exact (BitVec.ofNat_add P k).symm

theorem w_dec (c : Nat) (pos : 1 ≤ c) (small : c < 2^64) : W c + signExtend12 (4095 : BitVec 12) = W (c-1) := by
  have neg : signExtend12 4095 = -(1 : Word) := by decide
  rw [neg, ← BitVec.sub_eq_add_neg]
  exact BitVec.ofNat_sub_ofNat_of_le (w := 64) c 1 (by decide) pos

theorem w_zero (c : Nat) (small : c < 2^64) : (W c = 0) ↔ c = 0 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp [W] at this; omega
  · intro h; subst h; rfl

/-- `addi x25,x25,stride; srli x20,x20,1; addi x29,x29,-1; bne x29,x0,back`. -/
theorem adv_run (A stride back : Nat) (off : BitVec 13) (hA : A+3<814) (hs : stride < 2048)
    (e0 : decodeInstruction (checkWord A)=some (.base (.ADDI .x25 .x25 (BitVec.ofNat 12 stride))))
    (e1 : decodeInstruction (checkWord (A+1))=some (.base (.SRLI .x20 .x20 1)))
    (e2 : decodeInstruction (checkWord (A+2))=some (.base (.ADDI .x29 .x29 4095)))
    (e3 : decodeInstruction (checkWord (A+3))=some (.base (.BNE .x29 .x0 off)))
    (tgt : pcAt (A+3) + signExtend13 off = pcAt back)
    (s : MachineState) (pc : s.pc = pcAt A) (P idx c : Nat) (pp : s.getReg .x25 = W P)
    (ix : s.getReg .x20 = W idx) (cc : s.getReg .x29 = W c) (pos : 1 ≤ c) (cs : c < 2^64) (is : idx < 2^64) :
    ∃ t, Runs s t 4 4 ∧ t.pc = pcAt (if c = 1 then A+4 else back) ∧ t.getReg .x25 = W (P+stride) ∧
      t.getReg .x20 = W (idx/2) ∧ t.getReg .x29 = W (c-1) ∧ t.mem = s.mem ∧
      ∀ r, r ≠ .x25 → r ≠ .x20 → r ≠ .x29 → t.getReg r = s.getReg r := by
  let t1 := execInstrBr s (.ADDI .x25 .x25 (BitVec.ofNat 12 stride))
  let t2 := execInstrBr t1 (.SRLI .x20 .x20 1)
  let t3 := execInstrBr t2 (.ADDI .x29 .x29 4095)
  let t4 := execInstrBr t3 (.BNE .x29 .x0 off)
  have p1 : t1.pc = pcAt (A+1) := by change s.pc+4 = _; rw [pc, pc4]
  have p2 : t2.pc = pcAt (A+2) := by change t1.pc+4 = _; rw [p1, pc4]
  have p3 : t3.pc = pcAt (A+3) := by change t2.pc+4 = _; rw [p2, pc4]
  have r1 (r : Reg) (ne : r ≠ .x25) : t1.getReg r = s.getReg r := by
    simp only [t1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]
  have r2 (r : Reg) (ne : r ≠ .x20) : t2.getReg r = t1.getReg r := by
    simp only [t2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]
  have r3 (r : Reg) (ne : r ≠ .x29) : t3.getReg r = t2.getReg r := by
    simp only [t3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]
  have v25 : t1.getReg .x25 = W (P+stride) := by
    simp only [t1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0)]
    rw [pp, w_add P stride hs]
  have v20 : t2.getReg .x20 = W (idx/2) := by
    simp only [t2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0)]
    rw [r1 _ (by decide), ix]
    exact Open.shr idx 1 is
  have v29 : t3.getReg .x29 = W (c-1) := by
    simp only [t3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ .x0)]
    rw [r2 _ (by decide), r1 _ (by decide), cc, w_dec c pos cs]
  have h0 := stepOne A (by omega) _ e0 s pc rfl rfl rfl
  have h1 := stepOne (A+1) (by omega) _ e1 t1 p1 rfl rfl rfl
  have h2 := stepOne (A+2) (by omega) _ e2 t2 p2 rfl rfl rfl
  have h3 := stepOne (A+3) hA _ e3 t3 p3 rfl rfl rfl
  have p4 : t4.pc = pcAt (if c = 1 then A+4 else back) := by
    have g : t3.getReg .x0 = 0 := rfl
    have def4 : t4 = if (t3.getReg .x29 != t3.getReg .x0) then t3.setPC (t3.pc + signExtend13 off)
        else t3.setPC (t3.pc + 4) := rfl
    rw [def4, v29, g]
    by_cases e : c = 1
    · subst e
      have f : (W (1-1) != (0:Word)) = false := rfl
      rw [f, if_pos rfl]
      simp only [Bool.false_eq_true, ↓reduceIte]
      show t3.pc + 4 = _
      rw [p3, pc4]
    · have ne : (W (c-1) != (0:Word)) = true := by
        rw [bne_iff_ne]; exact fun h => e (by have := (w_zero (c-1) (lt_of_le_of_lt (Nat.sub_le c 1) cs)).mp h; omega)
      rw [ne, if_neg e]
      simp only [↓reduceIte]
      show t3.pc + signExtend13 off = _
      rw [p3, tgt]
  have m3 : t3.mem = s.mem := rfl
  have def4 : t4 = if (t3.getReg .x29 != t3.getReg .x0) then t3.setPC (t3.pc + signExtend13 off)
      else t3.setPC (t3.pc + 4) := rfl
  have m4 : t4.mem = s.mem := by rw [def4]; split <;> exact m3
  have r4 (r : Reg) : t4.getReg r = t3.getReg r := by rw [def4]; split <;> exact MachineState.getReg_setPC
  refine ⟨t4, ((h0.trans h1).trans h2).trans h3, p4, ?_, ?_, ?_, m4, ?_⟩
  · rw [r4, r3 _ (by decide), r2 _ (by decide), v25]
  · rw [r4, r3 _ (by decide), v20]
  · rw [r4]; exact v29
  · intro r a b c'
    rw [r4, r3 _ c', r2 _ b, r1 _ a]


/-! ### Memory bookkeeping -/

theorem w_ne (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) (ne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro h; have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact ne this

theorem mem_small (q : Nat) (hq : q < MEMORY_BYTES) : q < 18446744073709551616 :=
  lt_trans hq (by decide)

theorem outside_copy (b1 : MachineState) (sc : b1.getReg .x21 = 256) :
    Outside b1 (ckb_copyBlock b1 .x21 32) 256 64 := by
  intro q hq al o
  apply ckb_copy_block_outside b1 .x21 32 _ (by decide) (Or.inr rfl) sc
  intro i hi
  exact w_ne _ _ (mem_small q hq) (by omega) (by omega)

theorem outside_half (m : MachineState) (b k : Nat) (hb : b + 2*k ≤ 64) (sc : m.getReg .x21 = 256) :
    Outside m (CKBHalf.halfRun .x25 .x21 m 0 b k) 256 64 := by
  intro q hq al o
  exact CKBHalf.half_run_mem .x25 .x21 m 0 b 256 k q (by decide) (by rw [sc]; rfl) (by omega) (by omega) al
    (mem_small q hq) (by omega)

theorem outside_zero (m : MachineState) (off : Nat) (ho : off + 2 ≤ 64) (p : Word) :
    Outside m ((m.setHalfword (BitVec.ofNat 64 (256+off)) 0).setPC p) 256 64 := by
  intro q hq al o
  change (m.setHalfword (BitVec.ofNat 64 (256+off)) 0).getMem (BitVec.ofNat 64 q) = m.getMem (BitVec.ofNat 64 q)
  exact CKBHalf.set_halfword_get_mem m (256+off) q 0 al (by omega) (mem_small q hq) (by omega)

theorem outside_compress (m : MachineState) (ans : BitVec 256) :
    Outside m (Normal.checkCompressionState m ans) 256 64 := by
  intro q hq al o
  have b := mem_small q hq
  exact Normal.check_compression_memory_outside m ans _
    ⟨w_ne q 256 b (by decide) (by omega), w_ne q 264 b (by decide) (by omega),
     w_ne q 272 b (by decide) (by omega), w_ne q 280 b (by decide) (by omega)⟩

theorem sep256 : ∀ i < 4, ∀ j < 4, (256 : Word) + BitVec.ofNat 64 (8*i) ≠ BitVec.ofNat 64 (256+32+8*j) := by
  intro i hi j hj; interval_cases i <;> interval_cases j <;> decide

theorem moved_digest (b1 : MachineState) (sc : b1.getReg .x21 = 256) :
    readBuffer (ckb_copyBlock b1 .x21 32) (256+32) 32 = readBuffer b1 256 32 := by
  have d := ckb_copy_block_digest b1 .x21 32 (by decide) (Or.inr rfl) sc (by rw [sc]; decide)
    (by intro i hi j hj; rw [sc]; exact sep256 i hi j hj)
  rw [d, sc]; rfl

theorem moved_keep (b1 : MachineState) (sc : b1.getReg .x21 = 256) :
    readBuffer (ckb_copyBlock b1 .x21 32) 256 32 = readBuffer b1 256 32 :=
  ckb_copy_block_preserves b1 .x21 32 256 (by decide) (Or.inr rfl) sc (by decide)
    (by intro i hi j hj; interval_cases i <;> interval_cases j <;> decide)

theorem big (P : Nat) (pb : P+32 ≤ MEMORY_BYTES) : P+32 ≤ 2^64 := le_trans pb (by decide)

/-! ### One level: the copy phase -/

structure Prep (s m : MachineState) (join : Nat) (input : BitVec 512) (k : Nat) : Prop where
  runs : Runs s m k k
  budget : k ≤ 45
  pc : m.pc = pcAt join
  input : readBuffer m 256 64 = input
  regs : ∀ r, r ≠ .x6 → r ≠ .x7 → m.getReg r = s.getReg r
  outside : Outside s m 256 64

attribute [local irreducible] readBuffer CKBHalf.halfRun ckb_copyBlock

theorem prepA (s : MachineState) (pc : s.pc = pcAt 462) (sc : s.getReg .x21 = 256) (P idx : Nat)
    (pp : s.getReg .x25 = W P) (ix : s.getReg .x20 = W idx)
    (pe : P%2=0) (ph : 448 ≤ P) (pb : P+32 ≤ MEMORY_BYTES) :
    ∃ m k, Prep s m 537 (if idx%2=1 then readBuffer s 256 32 ++ readBuffer s P 32
      else readBuffer s P 32 ++ readBuffer s 256 32) k := by
  have br := branch_run 462 505 168 (by decide) rfl rfl rfl s pc idx ix
  let a := s.setReg .x7 (W (idx%2))
  have ar (r : Reg) (n7 : r ≠ .x7) : a.getReg r = s.getReg r := MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n7)
  have aout : Outside s a 256 64 := outside_reg s .x7 _
  have hb := big P pb
  by_cases odd : idx%2 = 1
  · rw [if_neg (show ¬ idx%2 = 0 by omega)] at br
    let b1 := a.setPC (pcAt (462+2))
    have b21 : b1.getReg .x21 = 256 := (ar _ (by decide)).trans sc
    have b25 : b1.getReg .x25 = W P := (ar _ (by decide)).trans pp
    have mv := move_run 464 (Or.inl rfl) b1 rfl b21
    let m1 := ckb_copyBlock b1 .x21 32
    have m1pc : m1.pc = pcAt 472 := by
      show (ckb_copyBlock b1 .x21 32).pc = _
      rw [← move_full, move_pc b1 8 (by decide)]; exact pcAt_add 464 8
    have m1r (r : Reg) (n6 : r ≠ .x6) : m1.getReg r = b1.getReg r := ckb_copy_block_register _ _ _ r n6
    have m21 : m1.getReg .x21 = W 256 := (m1r _ (by decide)).trans b21
    have m25 : m1.getReg .x25 = W P := (m1r _ (by decide)).trans b25
    have cp := copy_run 472 0 0 16 m1 m1pc (by decide) (fun j hj => by interval_cases j <;> exact ⟨rfl,rfl⟩)
      P 256 m25 m21 (by decide) (by decide) (by omega) (by decide) (by omega) (by decide)
    let m2 := CKBHalf.halfRun .x25 .x21 m1 0 0 16
    have m2pc : m2.pc = pcAt 504 := by
      rw [CKBHalf.half_run_pc, m1pc]; exact pcAt_add 472 32
    have jp := jump_run 504 537 132 (by decide) rfl rfl m2 m2pc
    let m3 := m2.setPC (pcAt 537)
    refine ⟨m3, 2+8+32+1, ⟨((br.trans mv).trans cp).trans jp, by decide, rfl, ?_, ?_, ?_⟩⟩
    · rw [if_pos odd, read_compression_halves _ _ (by decide)]
      have e1 : readBuffer m3 (256+32) 32 = readBuffer s 256 32 := by
        rw [read_congr_mem m3 m2 _ _ rfl,
          CKBHalf.half_run_preserves .x25 .x21 m1 0 0 P 256 16 (256+32) 32 (by decide) (by decide) m25 m21
            (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega)) (by decide)
            (Or.inr (by omega)),
          moved_digest b1 b21]
        exact read_congr_mem b1 s _ _ rfl
      have e2 : readBuffer m3 256 32 = readBuffer s P 32 := by
        have h := CKBHalf.half_run_copy .x25 .x21 m1 0 0 P 256 16 (by decide) (by decide) m25 m21
          (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega))
        rw [read_congr_mem m3 m2 _ _ rfl]
        refine h.trans ?_
        rw [Open.outside_read (outside_copy b1 b21) (by decide) (by decide) (P+0) (2*16) (by omega) (Or.inr (by omega))]
        exact read_congr_mem b1 s _ _ rfl
      rw [e1, e2]
    · intro r n6 n7
      have e : m3.getReg r = m2.getReg r := MachineState.getReg_setPC
      rw [e, CKBHalf.half_run_register _ _ _ _ _ _ _ n6, m1r r n6]
      exact ar r n7
    · exact outside_trans (outside_trans (outside_trans (outside_trans aout (outside_pc a _))
        (outside_copy b1 b21)) (outside_half m1 0 16 (by decide) m21)) (outside_pc m2 _)
  · rw [if_pos (show idx%2 = 0 by omega)] at br
    let b1 := a.setPC (pcAt 505)
    have b21 : b1.getReg .x21 = W 256 := (ar _ (by decide)).trans sc
    have b25 : b1.getReg .x25 = W P := (ar _ (by decide)).trans pp
    have cp := copy_run 505 0 32 16 b1 rfl (by decide) (fun j hj => by interval_cases j <;> exact ⟨rfl,rfl⟩)
      P 256 b25 b21 (by decide) (by decide) (by omega) (by decide) (by omega) (by decide)
    let m2 := CKBHalf.halfRun .x25 .x21 b1 0 32 16
    have m2pc : m2.pc = pcAt 537 := by
      rw [CKBHalf.half_run_pc]; exact pcAt_add 505 32
    refine ⟨m2, 2+32, ⟨br.trans cp, by decide, m2pc, ?_, ?_, ?_⟩⟩
    · rw [if_neg (by omega), read_compression_halves _ _ (by decide)]
      have e1 : readBuffer m2 (256+32) 32 = readBuffer s P 32 := by
        have h := CKBHalf.half_run_copy .x25 .x21 b1 0 32 P 256 16 (by decide) (by decide) b25 b21
          (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega))
        refine h.trans ?_
        exact read_congr_mem b1 s _ _ rfl
      have e2 : readBuffer m2 256 32 = readBuffer s 256 32 := by
        rw [CKBHalf.half_run_preserves .x25 .x21 b1 0 32 P 256 16 256 32 (by decide) (by decide) b25 b21
            (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega)) (by decide)
            (Or.inl (by omega))]
        exact read_congr_mem b1 s _ _ rfl
      rw [e1, e2]
    · intro r n6 n7
      rw [CKBHalf.half_run_register _ _ _ _ _ _ _ n6]
      exact ar r n7
    · exact outside_trans (outside_trans aout (outside_pc a _)) (outside_half b1 32 16 (by decide) b21)


theorem low_read (m : MachineState) (a : Nat) : low240 (readBuffer m a 32) = readBuffer m a 30 := by
  have h := read_buffer_slice m a 32 0 30 (by decide)
  simpa [low240] using h

theorem prepB (s : MachineState) (pc : s.pc = pcAt 548) (sc : s.getReg .x21 = 256) (P idx : Nat)
    (pp : s.getReg .x25 = W P) (ix : s.getReg .x20 = W idx)
    (pe : P%2=0) (ph : 448 ≤ P) (pb : P+32 ≤ MEMORY_BYTES) :
    ∃ m k, Prep s m 621 (if idx%2=1 then readBuffer s 256 32 ++ widen (readBuffer s P 30)
      else widen (readBuffer s P 30) ++ readBuffer s 256 32) k := by
  have br := branch_run 548 590 164 (by decide) rfl rfl rfl s pc idx ix
  let a := s.setReg .x7 (W (idx%2))
  have ar (r : Reg) (n7 : r ≠ .x7) : a.getReg r = s.getReg r := MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n7)
  have aout : Outside s a 256 64 := outside_reg s .x7 _
  have hb := big P pb
  by_cases odd : idx%2 = 1
  · rw [if_neg (show ¬ idx%2 = 0 by omega)] at br
    let b1 := a.setPC (pcAt (548+2))
    have b21 : b1.getReg .x21 = 256 := (ar _ (by decide)).trans sc
    have b25 : b1.getReg .x25 = W P := (ar _ (by decide)).trans pp
    have mv := move_run 550 (Or.inr rfl) b1 rfl b21
    let m1 := ckb_copyBlock b1 .x21 32
    have m1pc : m1.pc = pcAt 558 := by
      show (ckb_copyBlock b1 .x21 32).pc = _
      rw [← move_full, move_pc b1 8 (by decide)]; exact pcAt_add 550 8
    have m1r (r : Reg) (n6 : r ≠ .x6) : m1.getReg r = b1.getReg r := ckb_copy_block_register _ _ _ r n6
    have m21 : m1.getReg .x21 = W 256 := (m1r _ (by decide)).trans b21
    have m25 : m1.getReg .x25 = W P := (m1r _ (by decide)).trans b25
    have cp := copy_run 558 0 0 15 m1 m1pc (by decide) (fun j hj => by interval_cases j <;> exact ⟨rfl,rfl⟩)
      P 256 m25 m21 (by decide) (by decide) (by omega) (by decide) (by omega) (by decide)
    let m2 := CKBHalf.halfRun .x25 .x21 m1 0 0 15
    have m2pc : m2.pc = pcAt 588 := by
      rw [CKBHalf.half_run_pc, m1pc]; exact pcAt_add 558 30
    have m2r (r : Reg) (n6 : r ≠ .x6) : m2.getReg r = m1.getReg r := CKBHalf.half_run_register _ _ _ _ _ _ _ n6
    have z := zero_run 588 30 (by decide) rfl (by decide) (by decide) (by decide) m2 m2pc
      ((m2r _ (by decide)).trans m21)
    let m2' := (m2.setHalfword (BitVec.ofNat 64 (256+30)) 0).setPC (pcAt (588+1))
    have jp := jump_run 589 621 128 (by decide) rfl rfl m2' rfl
    let m3 := m2'.setPC (pcAt 621)
    refine ⟨m3, 2+8+30+1+1, ⟨(((br.trans mv).trans cp).trans z).trans jp, by decide, rfl, ?_, ?_, ?_⟩⟩
    · rw [if_pos odd, read_compression_halves _ _ (by decide)]
      have e1 : readBuffer m3 (256+32) 32 = readBuffer s 256 32 := by
        rw [read_congr_mem m3 (m2.setHalfword (BitVec.ofNat 64 (256+30)) 0) _ _ rfl,
          cm_trunc_store_outside m2 256 (256+32) 32 (by decide) (by decide) (by decide) (Or.inr (by omega)),
          CKBHalf.half_run_preserves .x25 .x21 m1 0 0 P 256 15 (256+32) 32 (by decide) (by decide) m25 m21
            (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega)) (by decide)
            (Or.inr (by omega)),
          moved_digest b1 b21]
        exact read_congr_mem b1 s _ _ rfl
      have e2 : readBuffer m3 256 32 = widen (readBuffer s P 30) := by
        have h := CKBHalf.half_run_copy .x25 .x21 m1 0 0 P 256 15 (by decide) (by decide) m25 m21
          (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega))
        rw [read_congr_mem m3 (m2.setHalfword (BitVec.ofNat 64 (256+30)) 0) _ _ rfl,
          cm_trunc_store_digest m2 256 (by decide) (by decide), low_read]
        congr 1
        refine h.trans ?_
        rw [Open.outside_read (outside_copy b1 b21) (by decide) (by decide) (P+0) (2*15) (by omega) (Or.inr (by omega))]
        exact read_congr_mem b1 s _ _ rfl
      rw [e1, e2]
    · intro r n6 n7
      have e : m3.getReg r = m2.getReg r := by
        show (((m2.setHalfword (BitVec.ofNat 64 (256+30)) 0).setPC (pcAt (588+1))).setPC (pcAt 621)).getReg r = _
        rw [MachineState.getReg_setPC, MachineState.getReg_setPC, cm_set_halfword_reg]
      rw [e, m2r r n6, m1r r n6]
      exact ar r n7
    · exact outside_trans (outside_trans (outside_trans (outside_trans (outside_trans aout (outside_pc a _))
        (outside_copy b1 b21)) (outside_half m1 0 15 (by decide) m21)) (outside_zero m2 30 (by decide) _))
        (outside_pc m2' _)
  · rw [if_pos (show idx%2 = 0 by omega)] at br
    let b1 := a.setPC (pcAt 590)
    have b21 : b1.getReg .x21 = W 256 := (ar _ (by decide)).trans sc
    have b25 : b1.getReg .x25 = W P := (ar _ (by decide)).trans pp
    have cp := copy_run 590 0 32 15 b1 rfl (by decide) (fun j hj => by interval_cases j <;> exact ⟨rfl,rfl⟩)
      P 256 b25 b21 (by decide) (by decide) (by omega) (by decide) (by omega) (by decide)
    let m2 := CKBHalf.halfRun .x25 .x21 b1 0 32 15
    have m2pc : m2.pc = pcAt 620 := by
      rw [CKBHalf.half_run_pc]; exact pcAt_add 590 30
    have m2r (r : Reg) (n6 : r ≠ .x6) : m2.getReg r = b1.getReg r := CKBHalf.half_run_register _ _ _ _ _ _ _ n6
    have z := zero_run 620 62 (by decide) rfl (by decide) (by decide) (by decide) m2 m2pc
      ((m2r _ (by decide)).trans b21)
    let m3 := (m2.setHalfword (BitVec.ofNat 64 (256+62)) 0).setPC (pcAt (620+1))
    have z62 : BitVec.ofNat 64 (256+62) = BitVec.ofNat 64 (288+30) := rfl
    refine ⟨m3, 2+30+1, ⟨(br.trans cp).trans z, by decide, rfl, ?_, ?_, ?_⟩⟩
    · rw [if_neg (by omega), read_compression_halves _ _ (by decide)]
      have e1 : readBuffer m3 (256+32) 32 = widen (readBuffer s P 30) := by
        have h := CKBHalf.half_run_copy .x25 .x21 b1 0 32 P 256 15 (by decide) (by decide) b25 b21
          (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega))
        rw [read_congr_mem m3 (m2.setHalfword (BitVec.ofNat 64 (256+62)) 0) _ _ rfl, z62,
          cm_trunc_store_digest m2 (256+32) (by decide) (by decide), low_read]
        congr 1
        refine h.trans ?_
        exact read_congr_mem b1 s _ _ rfl
      have e2 : readBuffer m3 256 32 = readBuffer s 256 32 := by
        rw [read_congr_mem m3 (m2.setHalfword (BitVec.ofNat 64 (256+62)) 0) _ _ rfl, z62,
          cm_trunc_store_outside m2 (288) 256 32 (by decide) (by decide) (by decide) (Or.inl (by omega)),
          CKBHalf.half_run_preserves .x25 .x21 b1 0 32 P 256 15 256 32 (by decide) (by decide) b25 b21
            (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (Or.inr (by omega)) (by decide)
            (Or.inl (by omega))]
        exact read_congr_mem b1 s _ _ rfl
      rw [e1, e2]
    · intro r n6 n7
      have e : m3.getReg r = m2.getReg r := by
        show ((m2.setHalfword (BitVec.ofNat 64 (256+62)) 0).setPC (pcAt (620+1))).getReg r = _
        rw [MachineState.getReg_setPC, cm_set_halfword_reg]
      rw [e, m2r r n6]
      exact ar r n7
    · exact outside_trans (outside_trans (outside_trans aout (outside_pc a _)) (outside_half b1 32 15 (by decide) b21))
        (outside_zero m2 62 (by decide) _)


/-! ### One level: hash and advance -/

def keepRegs : List Reg := [.x1, .x8, .x19, .x24, .x26, .x27, .x30]

structure LevelOut (o : Oracle) (s t : MachineState) (exitPC head c P' idx mask : Nat) (digest : Digest)
    (n : Nat) : Prop where
  budget : n ≤ 80
  runs : Normal.Runs o s t n 1
  pc : t.pc = pcAt (if c = 1 then exitPC else head)
  scratch : t.getReg .x21 = 256
  proof : t.getReg .x25 = W P'
  index : t.getReg .x20 = W (idx/2)
  counter : t.getReg .x29 = W (c-1)
  mask : t.getReg .x9 = W (mask/2)
  digest : readBuffer t 256 32 = digest
  keep : ∀ r ∈ keepRegs, t.getReg r = s.getReg r
  outside : Outside s t 256 64

def boff (j : Nat) : BitVec 13 := if j = 537 then BitVec.ofInt 13 (-336) else BitVec.ofInt 13 (-328)

theorem finishLevel (o : Oracle) (s m : MachineState) (join stride back exitPC : Nat) (input : BitVec 512) (k : Nat)
    (ph : (join = 537 ∧ stride = 32 ∧ back = 462 ∧ exitPC = 547) ∨ (join = 621 ∧ stride = 30 ∧ back = 548 ∧ exitPC = 631))
    (prep : Prep s m join input k)
    (sc : s.getReg .x21 = 256) (P idx c mask : Nat) (pp : s.getReg .x25 = W P) (ix : s.getReg .x20 = W idx)
    (cc : s.getReg .x29 = W c) (mm : s.getReg .x9 = W mask) (pos : 1 ≤ c) (cs : c < 2^64) (is : idx < 2^64)
    (ms : mask < 2^64) :
    ∃ t n, LevelOut o s t exitPC back c (P+stride) idx mask
      (Normal.tcompDigest (W mask &&& 1) (o.compression (padInput input))) n := by
  have mr (r : Reg) (n6 : r ≠ .x6) (n7 : r ≠ .x7) := prep.regs r n6 n7
  have m21 : m.getReg .x21 = 256 := (mr _ (by decide) (by decide)).trans sc
  have comp := compress_run o m join (by rcases ph with ⟨rfl,-⟩|⟨rfl,-⟩ <;> simp) prep.pc m21
  let t1 := Normal.checkCompressionState m (o.compression (padInput (readBuffer m 256 64)))
  have t1pc : t1.pc = pcAt (join+6) := by
    exact (Normal.check_compression_pc m _).trans (by rw [prep.pc]; exact pcAt_add join 6)
  have t1r (r : Reg) (n5 : r ≠ .x5) (n6 : r ≠ .x6) (n7 : r ≠ .x7) (n9 : r ≠ .x9) (n10 : r ≠ .x10) (n11 : r ≠ .x11)
      (n12 : r ≠ .x12) (n13 : r ≠ .x13) (n14 : r ≠ .x14) (n15 : r ≠ .x15) (n16 : r ≠ .x16) (n17 : r ≠ .x17)
      (n31 : r ≠ .x31) : t1.getReg r = s.getReg r :=
    (Normal.check_compression_register m _ r n5 n10 n11 n12 n13 n14 n15 n16 n17 n31 n7 n9).trans (mr r n6 n7)
  have ad := adv_run (join+6) stride back (boff join) (by rcases ph with ⟨rfl,-⟩|⟨rfl,-⟩ <;> decide)
    (by rcases ph with ⟨-,rfl,-⟩|⟨-,rfl,-⟩ <;> decide)
    (by rcases ph with ⟨rfl,rfl,-⟩|⟨rfl,rfl,-⟩ <;> rfl) (by rcases ph with ⟨rfl,-⟩|⟨rfl,-⟩ <;> rfl)
    (by rcases ph with ⟨rfl,-⟩|⟨rfl,-⟩ <;> rfl) (by rcases ph with ⟨rfl,-⟩|⟨rfl,-⟩ <;> rfl)
    (by rcases ph with ⟨rfl,-,rfl,-⟩|⟨rfl,-,rfl,-⟩ <;> rfl)
    t1 t1pc P idx c ((t1r _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pp)
    ((t1r _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ix)
    ((t1r _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans cc) pos cs is
  obtain ⟨t, run, tpc, t25, t20, t29, tmem, tr⟩ := ad
  have steps : 5 + tcompSteps m ≤ 26 := by have := tcomp_steps_le m; omega
  refine ⟨t, k + (5 + tcompSteps m) + 4, ⟨by have := prep.budget; omega,
    ((Normal.deterministic o prep.runs).trans comp).trans (Normal.deterministic o run), ?_, ?_, t25, t20, t29, ?_, ?_, ?_, ?_⟩⟩
  · rw [tpc]; rcases ph with ⟨rfl,-,rfl,rfl⟩|⟨rfl,-,rfl,rfl⟩ <;> rfl
  · rw [tr _ (by decide) (by decide) (by decide)]
    exact (t1r _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans sc
  · rw [tr _ (by decide) (by decide) (by decide)]
    exact (Normal.check_compression_x9 m _).trans (by rw [mr _ (by decide) (by decide), mm]; exact Open.shr mask 1 ms)
  · rw [read_congr_mem t t1 _ _ tmem]
    refine (Normal.check_compression_digest m _).trans ?_
    have b : tcompBit m = W mask &&& 1 := by unfold tcompBit; rw [mr _ (by decide) (by decide), mm]
    simp only [b, prep.input]
  · intro r hr
    simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [tr r (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide) (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
      (by rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact t1r _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact outside_trans (outside_trans prep.outside (outside_compress m _)) (outside_mem tmem)

/-! ### Cut bookkeeping -/

theorem mask_cut (l : Nat) (hl : l < 16) (a : Digest) :
    Normal.tcompDigest (W (131068 / 2^l) &&& 1) a = cut (l+1) a := by
  have key : (W (131068 / 2^l) &&& 1 = 0) ↔ ¬ CutHeight (l+1) := by
    rw [parity_word, w_zero _ (by omega)]
    interval_cases l <;> simp [CutHeight]
  unfold Normal.tcompDigest cut
  by_cases h : CutHeight (l+1)
  · rw [if_neg (fun e => (key.mp e) h), if_pos h]
  · rw [if_pos (key.mpr h), if_neg h]

theorem mask_half (l : Nat) : 131068 / 2^l / 2 = 131068 / 2^(l+1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem level_digest (o : Oracle) (l idx : Nat) (hl : l < 16) (cur sib : Digest) :
    Normal.tcompDigest (W (131068 / 2^l) &&& 1)
        (o.compression (padInput (if idx%2=1 then cur ++ sib else sib ++ cur))) =
      climbStep o.compression l cur (idx.testBit 0, sib) := by
  erw [mask_cut l hl]
  unfold climbStep combine
  rw [Nat.testBit_zero]
  by_cases odd : idx%2=1
  · simp [odd]
  · simp [odd]


/-! ### Loops -/

def phaseHead (b : Bool) : Nat := if b then 548 else 462
def phaseExit (b : Bool) : Nat := if b then 631 else 547
def phaseStride (b : Bool) : Nat := if b then 30 else 32
def phaseSib (b : Bool) (s : MachineState) (P : Nat) : Digest :=
  if b then widen (readBuffer s P 30) else readBuffer s P 32

theorem level (o : Oracle) (b : Bool) (s : MachineState) (pc : s.pc = pcAt (phaseHead b))
    (sc : s.getReg .x21 = 256) (P idx c l : Nat)
    (pp : s.getReg .x25 = W P) (ix : s.getReg .x20 = W idx) (cc : s.getReg .x29 = W c)
    (mm : s.getReg .x9 = W (131068 / 2^l)) (pos : 1 ≤ c) (cs : c < 2^64) (is : idx < 2^64) (hl : l < 16)
    (pe : P%2=0) (ph : 448 ≤ P) (pb : P+32 ≤ MEMORY_BYTES) :
    ∃ t n, LevelOut o s t (phaseExit b) (phaseHead b) c (P+phaseStride b) idx (131068 / 2^l)
      (climbStep o.compression l (readBuffer s 256 32) (idx.testBit 0, phaseSib b s P)) n := by
  have ms : 131068 / 2^l < 2^64 := lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
  cases b with
  | false =>
    obtain ⟨m,k,pr⟩ := prepA s pc sc P idx pp ix pe ph pb
    obtain ⟨t,n,lo⟩ := finishLevel o s m 537 32 462 547 _ k (Or.inl ⟨rfl,rfl,rfl,rfl⟩) pr sc P idx c _ pp ix cc mm
      pos cs is ms
    exact ⟨t,n,⟨lo.budget,lo.runs,lo.pc,lo.scratch,lo.proof,lo.index,lo.counter,lo.mask,
      lo.digest.trans (level_digest o l idx hl _ _),lo.keep,lo.outside⟩⟩
  | true =>
    obtain ⟨m,k,pr⟩ := prepB s pc sc P idx pp ix pe ph pb
    obtain ⟨t,n,lo⟩ := finishLevel o s m 621 30 548 631 _ k (Or.inr ⟨rfl,rfl,rfl,rfl⟩) pr sc P idx c _ pp ix cc mm
      pos cs is ms
    exact ⟨t,n,⟨lo.budget,lo.runs,lo.pc,lo.scratch,lo.proof,lo.index,lo.counter,lo.mask,
      lo.digest.trans (level_digest o l idx hl _ _),lo.keep,lo.outside⟩⟩

theorem sib_outside (b : Bool) {s t : MachineState} (out : Outside s t 256 64) (P : Nat) (ph : 448 ≤ P)
    (pb : P+32 ≤ MEMORY_BYTES) : phaseSib b t P = phaseSib b s P := by
  cases b
  · exact Open.outside_read out (by decide) (by decide) P 32 pb (Or.inr (by omega))
  · simp only [phaseSib, if_true]
    rw [Open.outside_read out (by decide) (by decide) P 30 (by omega) (Or.inr (by omega))]

structure LoopOut (o : Oracle) (b : Bool) (s t : MachineState) (c P idx l : Nat) (start : Digest)
    (sibs : Nat → Digest) (n : Nat) : Prop where
  budget : n ≤ 80*c
  runs : Normal.Runs o s t n c
  pc : t.pc = pcAt (phaseExit b)
  scratch : t.getReg .x21 = 256
  proof : t.getReg .x25 = W (P+phaseStride b*c)
  index : t.getReg .x20 = W (idx/2^c)
  mask : t.getReg .x9 = W (131068 / 2^(l+c))
  digest : readBuffer t 256 32 = climbAt o.compression l start ((List.range c).map fun j => (idx.testBit j, sibs j))
  keep : ∀ r ∈ keepRegs, t.getReg r = s.getReg r
  outside : Outside s t 256 64

theorem stride_le (b : Bool) : phaseStride b ≤ 32 := by cases b <;> decide

theorem loop (o : Oracle) (b : Bool) (c : Nat) : ∀ (s : MachineState) (P idx l : Nat) (sibs : Nat → Digest),
    s.pc = pcAt (phaseHead b) → s.getReg .x21 = 256 → s.getReg .x25 = W P → s.getReg .x20 = W idx →
    s.getReg .x29 = W c → s.getReg .x9 = W (131068 / 2^l) → 1 ≤ c → c < 2^64 → idx < 2^64 → l + c ≤ 16 →
    P%2=0 → phaseStride b % 2 = 0 → 448 ≤ P → P + 32*c ≤ MEMORY_BYTES →
    (∀ j < c, phaseSib b s (P+phaseStride b*j) = sibs j) →
    ∃ t n, LoopOut o b s t c P idx l (readBuffer s 256 32) sibs n := by
  induction c with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ pos; omega
  | succ c ih =>
    intro s P idx l sibs pc sc pp ix cc mm pos cs is hl pe se ph pb sib
    obtain ⟨t1,n1,lo⟩ := level o b s pc sc P idx (c+1) l pp ix cc mm pos cs is (by omega) pe ph (by omega)
    have s0 : phaseSib b s P = sibs 0 := by simpa using sib 0 (by omega)
    by_cases last : c = 0
    · subst last
      refine ⟨t1, n1, ⟨by have := lo.budget; omega, lo.runs, ?_, lo.scratch, ?_, ?_, ?_, ?_, lo.keep, lo.outside⟩⟩
      · rw [lo.pc]; rfl
      · rw [lo.proof]; simp
      · rw [lo.index]; simp
      · rw [lo.mask, mask_half]
      · rw [lo.digest, s0]; simp [climbAt_cons, climbAt_nil]
    · have t1pc : t1.pc = pcAt (phaseHead b) := by rw [lo.pc, if_neg (by omega)]
      have sib' : ∀ j < c, phaseSib b t1 (P+phaseStride b+phaseStride b*j) = sibs (j+1) := by
        intro j hj
        have h := stride_le b
        rw [sib_outside b lo.outside _ (by omega) (by have := Nat.mul_le_mul_left (j+1) h; nlinarith),
          show P+phaseStride b+phaseStride b*j = P+phaseStride b*(j+1) by ring]
        exact sib (j+1) (by omega)
      obtain ⟨t,n2,lp⟩ := ih t1 (P+phaseStride b) (idx/2) (l+1) (fun j => sibs (j+1)) t1pc lo.scratch lo.proof
        lo.index (by rw [lo.counter]; rfl) (by rw [lo.mask, mask_half]) (by omega) (by omega)
        (lt_of_le_of_lt (Nat.div_le_self _ _) is) (by omega)
        (by have := pe; cases b <;> simp [phaseStride] at * <;> omega) se (by omega)
        (by have h := stride_le b; nlinarith) sib'
      have runs := lo.runs.trans lp.runs
      rw [Nat.add_comm 1 c] at runs
      refine ⟨t, n1+n2, ⟨by have := lo.budget; have := lp.budget; nlinarith, runs, lp.pc, lp.scratch, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [lp.proof]; congr 1; ring
      · rw [lp.index, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      · rw [lp.mask]; congr 3; omega
      · rw [lp.digest, lo.digest, s0, List.range_succ_eq_map, List.map_cons, List.map_map, climbAt_cons]
        congr 1
        apply List.map_congr_left
        intro j _
        simp [Nat.testBit_div_two]
      · intro r hr; rw [lp.keep r hr, lo.keep r hr]
      · exact outside_trans lo.outside lp.outside


/-! ### The whole path: word 218 to word 256 -/

structure PathEnd (o : Oracle) (s t : MachineState) (i : Index) (p : Nat) (d : Digest) (n : Nat) : Prop where
  pc : t.pc = pcAt 256
  index : t.getReg .x20 = W (i.val/65536)
  proof : t.getReg .x25 = W (p+486)
  scratch : t.getReg .x21 = 256
  keep : ∀ reg ∈ keepRegs, t.getReg reg = s.getReg reg
  digest : readBuffer t 256 32 = d
  high : High s t
  runs : Normal.Runs o s t n 16
  budget : n ≤ 1300

theorem setup_run (s : MachineState) (pc : s.pc = pcAt 458) :
    ∃ t, Runs s t 4 4 ∧ t.pc = pcAt 462 ∧ t.getReg .x9 = W 131068 ∧ t.getReg .x29 = W 3 ∧ t.mem = s.mem ∧
      ∀ r, r ≠ .x9 → r ≠ .x29 → t.getReg r = s.getReg r := by
  let t1 := execInstrBr s (.ADDI .x9 .x0 63)
  let t2 := execInstrBr t1 (.SLLI .x9 .x9 11)
  let t3 := execInstrBr t2 (.ADDI .x9 .x9 2044)
  let t4 := execInstrBr t3 (.ADDI .x29 .x0 3)
  have p1 : t1.pc = pcAt 459 := by change s.pc+4 = _; rw [pc, pc4]
  have p2 : t2.pc = pcAt 460 := by change t1.pc+4 = _; rw [p1, pc4]
  have p3 : t3.pc = pcAt 461 := by change t2.pc+4 = _; rw [p2, pc4]
  have h0 := stepOne 458 (by decide) _ rfl s pc rfl rfl rfl
  have h1 := stepOne 459 (by decide) _ rfl t1 p1 rfl rfl rfl
  have h2 := stepOne 460 (by decide) _ rfl t2 p2 rfl rfl rfl
  have h3 := stepOne 461 (by decide) _ rfl t3 p3 rfl rfl rfl
  refine ⟨t4, ((h0.trans h1).trans h2).trans h3, ?_, ?_, ?_, rfl, ?_⟩
  · change t3.pc+4 = _; rw [p3, pc4]
  · have v1 : t1.getReg .x9 = 63 := by
      simp only [t1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x9 ≠ .x0)]; rfl
    have v2 : t2.getReg .x9 = 129024 := by
      simp only [t2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x9 ≠ .x0)]
      rw [v1]; rfl
    have v3 : t3.getReg .x9 = W 131068 := by
      simp only [t3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x9 ≠ .x0)]
      rw [v2]; rfl
    simp only [t4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x9)]
    exact v3
  · simp only [t4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ .x0)]
    rfl
  · intro r a b
    simp only [t4, t3, t2, t1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]

theorem fullPath (o : Oracle) (s : MachineState) (p : Nat) (i : Index) (siblings : Nat → Digest)
    (pc : s.pc = pcAt 218) (scratch : s.getReg .x21 = 256)
    (pf : s.getReg .x25 = W p) (idx : s.getReg .x20 = W i.val)
    (pe : p%2=0) (high : 448 ≤ p) (pb : p+512 ≤ MEMORY_BYTES)
    (dataA : ∀ j<3, readBuffer s (p+32*j) 32 = siblings j)
    (dataB : ∀ j<13, widen (readBuffer s (p+96+30*j) 30) = siblings (3+j)) :
    ∃ t n, PathEnd o s t i p (climbAt o.compression 0 (readBuffer s 256 32) (Late.Check.path i 16 siblings)) n := by
  have j0 := jump_run 218 458 960 (by decide) rfl rfl s pc
  let s1 := s.setPC (pcAt 458)
  obtain ⟨s2, r2, p2, m2, c2, mem2, k2⟩ := setup_run s1 rfl
  have iv : i.val < 2^24 := i.isLt
  have k12 (r : Reg) (a : r ≠ .x9) (b : r ≠ .x29) : s2.getReg r = s.getReg r := (k2 r a b).trans MachineState.getReg_setPC
  obtain ⟨t1, nA, lA⟩ := loop o false 3 s2 p i.val 0 (fun j => siblings j) p2 ((k12 _ (by decide) (by decide)).trans scratch)
    ((k12 _ (by decide) (by decide)).trans pf) ((k12 _ (by decide) (by decide)).trans idx) c2 (by rw [m2]; rfl)
    (by decide) (by decide) (by omega) (by decide) pe (by decide) high (by omega)
    (by intro j hj; simp only [phaseSib, Bool.false_eq_true, ↓reduceIte, phaseStride]
        rw [read_congr_mem s2 s _ _ mem2]; exact dataA j hj)
  -- word 547: addi x29,x0,13
  let t2 := execInstrBr t1 (.ADDI .x29 .x0 13)
  have h2 := stepOne 547 (by decide) _ rfl t1 lA.pc rfl rfl rfl
  have t2pc : t2.pc = pcAt 548 := by change t1.pc+4 = _; rw [lA.pc, pc4]; rfl
  have t2r (r : Reg) (ne : r ≠ .x29) : t2.getReg r = t1.getReg r := by
    simp only [t2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm ne)]
  have t229 : t2.getReg .x29 = W 13 := by
    simp only [t2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ .x0)]
    rfl
  have t2mem : t2.mem = t1.mem := rfl
  obtain ⟨t3, nB, lB⟩ := loop o true 13 t2 (p+96) (i.val/8) 3 (fun j => siblings (3+j)) t2pc
    ((t2r _ (by decide)).trans lA.scratch) ((t2r _ (by decide)).trans (by rw [lA.proof]; rfl))
    ((t2r _ (by decide)).trans (by rw [lA.index]; rfl)) t229 ((t2r _ (by decide)).trans (by rw [lA.mask]))
    (by decide) (by decide) (by omega) (by decide) (by omega) (by decide) (by omega) (by omega)
    (by
      intro j hj
      simp only [phaseSib, ↓reduceIte, phaseStride]
      rw [read_congr_mem t2 t1 _ _ t2mem,
        Open.outside_read lA.outside (by decide) (by decide) _ 30 (by omega) (Or.inr (by omega)),
        read_congr_mem s2 s _ _ mem2]
      exact dataB j hj)
  have j3 := jump_run 631 256 (BitVec.ofInt 21 (-1500)) (by decide) rfl rfl t3 lB.pc
  let t := t3.setPC (pcAt 256)
  have tr (r : Reg) : t.getReg r = t3.getReg r := MachineState.getReg_setPC
  refine ⟨t, 1+4+nA+1+nB+1, ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [tr, lB.index, Nat.div_div_eq_div_mul]; rfl
  · rw [tr, lB.proof]; congr 1
  · rw [tr]; exact lB.scratch
  · intro r hr
    have n9 : r ≠ .x9 := by simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have n29 : r ≠ .x29 := by simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rw [tr, lB.keep r hr, t2r r n29, lA.keep r hr, k12 r n9 n29]
  · rw [read_congr_mem t t3 _ _ rfl, lB.digest, read_congr_mem t2 t1 _ _ t2mem, lA.digest, read_congr_mem s2 s _ _ mem2]
    unfold Late.Check.path
    rw [show (16 : Nat) = 3 + 13 from rfl, List.range_add, List.map_append, climbAt_append]
    simp only [List.length_map, List.length_range, Nat.zero_add, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    rw [show (8 : Nat) = 2^3 from rfl, Nat.testBit_div_two_pow, Nat.add_comm]
  · have out : Outside s t 256 64 :=
      outside_trans (outside_trans (outside_trans (outside_trans (outside_pc s _) (outside_mem mem2)) lA.outside)
        (outside_mem t2mem)) (outside_trans lB.outside (outside_pc t3 _))
    exact high_write out (by decide) (by decide) (by decide)
  · exact (((((Normal.deterministic o j0).trans (Normal.deterministic o r2)).trans lA.runs).trans
      (Normal.deterministic o h2)).trans lB.runs).trans (Normal.deterministic o j3)
  · have := lA.budget; have := lB.budget; omega

end CommitGolfCandidate.Late.Check.Micro.CKBPath
