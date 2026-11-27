import CommitGolfCandidate.TwoPermutationPackedDecode
import CommitGolfCandidate.TwoPermutationPackedCapBytes
import CommitGolfCandidate.TwoPermutationPackedRecordGeometry
import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.C3CommitMemory
import CommitGolfCandidate.TwoPermutationCheckerRecordSetup
import CommitGolfCandidate.TwoPermutationPackedCheckRecordData
import CommitGolfCandidate.TwoPermutationPackedInputFrame
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.R1bMachine

/-! # The checker's paired-leaf block (check image word 22, words 10542..453, lower setup 58..62)

With `src = checkSourceWord ordinal`, the claimed value `v` is at words `src+5 .. src+37`
(`V = 8 (src+5)`, `s3 = x19 = V - 40`). Word 22 is `jal zero,<10542>`; then
`ld t1,0(s0) ; andi t2,t1,1 ; bne t2,zero,<10589>`.

Even path (words 10545..418, 48 steps, 4 calls):
`addi a1,zero,64 ; addi a3,zero,0 ; addi a0,s3,232 ; addi a2,a0,32 ; ecall` (r at src+33),
`addi a0,a0,-192 ; addi a2,a0,192 ; ecall` (q at src+29), `addi a0,a0,192 ; ecall` (z at src+29),
`slli t3,t1,8 ; add t3,gp,t3 ; addi t6,t3,96 ; sd t6,32(a0)` (tag at src+33),
8 halfword copies of the salt to src+35..src+37, `addi a1,zero,200 ; addi a3,zero,1 ;
addi a0,a0,-136 ; addi a2,s7,0 ; ecall` (the reply at 1536), 4 word copies of reply words 21..24 to
1536..1539, `jal zero,<58>`.

Odd path (words 10589..453, 39 steps, 4 calls):
`addi a1,zero,64 ; addi a3,zero,0 ; addi a0,s3,40 ; addi a2,a0,0 ; ecall` (q at src+5),
`addi a0,a0,192 ; addi a2,a0,-160 ; ecall` (r at src+9), `addi a0,a0,-192 ; ecall` (z at src+9),
`slli t3,t1,8 ; add t3,gp,t3 ; addi t6,t3,40 ; sd t6,16(a0)` (tag at src+7), 8 halfword copies of
the salt to src+5..src+7, `addi a1,zero,200 ; addi a3,zero,1 ; addi a2,s7,0 ; ecall` (the reply at
1536), `jal zero,<58>`. -/
namespace TwoPermutationPrototype.Packed.C3PRecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.C3Leaves TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (checkIndexWord checkSourceWord checker_positions_bound honestIndex beginLower beginLowerCode lower_setup_post lower_setup_register lower_setup_mem check_recorded_bind check_recorded_map checker_value_data buffer_window)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
-- Sequential elaboration, as in C3PAdmission (the verifier builds with parallel elaboration on two CPUs).
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option autoImplicit false

attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem set_pc_pc (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem mem_set_reg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl
@[local simp] private theorem mem_set_pc (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl

/-- The address of check word `k`. -/
abbrev ckPC (k : Nat) : Word := BitVec.ofNat 64 (4096 + 4 * k)

theorem ck_pc_next (k : Nat) : ckPC k + 4 = ckPC (k + 1) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 by rfl, ← BitVec.ofNat_add]; congr 1

theorem ck_fetch (st : MachineState) (k : Nat) (instr : Instr) (bounded : k < 10624) (pc : st.pc = ckPC k)
    (decoded : decodeInstruction (R1b.Machine.Code.word .check k) = some (.base instr)) :
    fetch packedImage st = some (.base instr) := by
  rw [← delivered_check_image]
  exact (R1b.Machine.fetched .check k bounded st pc).trans decoded

/-! ### The two salt copies -/

def evenSaltCode : CopyCode where
  image := packedImage
  start := 10559
  count := 8
  source := .x21
  dest := .x10
  destOffset := 48
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by decide
  load := fun j bounded s pc => ck_fetch s _ _ (by omega) pc (by interval_cases j <;> rfl)
  store := fun j bounded s pc => ck_fetch s _ _ (by omega) pc (by interval_cases j <;> rfl)

def oddSaltCode : CopyCode where
  image := packedImage
  start := 10603
  count := 8
  source := .x21
  dest := .x10
  destOffset := 0
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by decide
  load := fun j bounded s pc => ck_fetch s _ _ (by omega) pc (by interval_cases j <;> rfl)
  store := fun j bounded s pc => ck_fetch s _ _ (by omega) pc (by interval_cases j <;> rfl)

theorem code_bytes (c : CopyCode) (s : MachineState) (source target : Nat)
    (ready : CopyReady c s source target 0) (order : target ≤ source) :
    let t := copyField c s
    (∀ i<2*c.count, t.getByte (BitVec.ofNat 64 (target+i))=s.getByte (BitVec.ofNat 64 (source+i))) ∧
    (∀ q : Word, (∀ i<2*c.count, q≠BitVec.ofNat 64 (target+i)) → t.getByte q=s.getByte q) := by
  have sb : source+2*c.count≤MEMORY_BYTES := ready.srcBound
  have tb : target+2*c.count≤MEMORY_BYTES := ready.dstBound
  have lim : MEMORY_BYTES<2^64 := by decide
  have mem := copy_field_memory _ _ _ _ ready
  have bytes := ProjectedHalfword.forward_memory c.count s source target order (by omega) (by omega)
        ready.srcAligned ready.dstAligned
  simpa only [MachineState.getByte, MachineState.getMem, mem] using bytes

theorem code_read (c : CopyCode) (s : MachineState) (source target : Nat)
    (ready : CopyReady c s source target 0) (order : target ≤ source) :
    readBuffer (copyField c s) target (2*c.count)=readBuffer s source (2*c.count) := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro i hi
  rw [(code_bytes _ _ _ _ ready order).1 _ (Finset.mem_range.mp hi)]

/-! ### The precondition and the head -/

/-- The record cursor's registers, named by their word indices. -/
structure CkReady (s : MachineState) (src proof : Nat) (index : Index) : Prop where
  pc : s.pc = 0x1058
  indexAccess : accessValid (s.getReg .x8) 8 = true
  indexValue : s.getMem (s.getReg .x8) = BitVec.ofNat 64 index.val
  source : s.getReg .x19 = wordAddress src
  proofPointer : s.getReg .x21 = BitVec.ofNat 64 proof
  tagBase : s.getReg .x3 = 4056
  digest : s.getReg .x23 = wordAddress 1536
  selector : s.getReg .x5 = 0
  sourceBound : src + 37 ≤ 2 ^ 33
  sourceLow : 1576 ≤ src
  proofAligned : proof % 2 = 0
  proofBound : proof + 16 ≤ MEMORY_BYTES
  apart : 8 * (src + 37) ≤ proof

/-- After `jal zero,<10542> ; ld t1,0(s0) ; andi t2,t1,1`. -/
def ckHead (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (s.setPC (ckPC 10542)) (.LD .x6 .x8 0)) (.ANDI .x7 .x6 1)

theorem ck_head_facts (s : MachineState) :
    (ckHead s).mem = s.mem ∧ (ckHead s).getReg .x6 = s.getMem (s.getReg .x8) ∧
    (ckHead s).getReg .x7 = s.getMem (s.getReg .x8) &&& 1 ∧ (ckHead s).pc = ckPC 10544 ∧
    ∀ r, r ≠ .x6 → r ≠ .x7 → (ckHead s).getReg r = s.getReg r := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [ckHead, execInstrBr]
  · simp [ckHead, execInstrBr, signExtend12]
  · simp [ckHead, execInstrBr, signExtend12] <;> rfl
  · simp [ckHead, execInstrBr] <;> rfl
  · intro r a b
    simp [ckHead, execInstrBr, Ne.symm a, Ne.symm b]

theorem parity_word (i : Nat) (small : i < 2 ^ 64) :
    BitVec.ofNat 64 i &&& 1 = BitVec.ofNat 64 (i % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    show (1 : BitVec 64).toNat = 1 by rfl, Nat.and_one_is_mod]
  omega

/-! ### Even path: states -/

def evOps1 : List Instr := [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x10 .x19 232, .ADDI .x12 .x10 32]

/-- Entry of the even path (word 10545). -/
def ev0 (s : MachineState) : MachineState := (ckHead s).setPC (ckPC 10545)

def ev1 (s : MachineState) : MachineState := evOps1.foldl execInstrBr (ev0 s)

def ev2 (s : MachineState) (src : Nat) (r : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (writeBits (ev1 s) (wordAddress (src + 33)) r) (.ADDI .x10 .x10 3904))
    (.ADDI .x12 .x10 192)

def ev3 (s : MachineState) (src : Nat) (r q : BitVec 256) : MachineState :=
  execInstrBr (writeBits (ev2 s src r) (wordAddress (src + 29)) q) (.ADDI .x10 .x10 192)

def evOps4 : List Instr := [.SLLI .x28 .x6 8, .ADD .x28 .x3 .x28, .ADDI .x31 .x28 96, .SD .x10 .x31 32]

def ev4 (s : MachineState) (src : Nat) (r q z : BitVec 256) : MachineState :=
  evOps4.foldl execInstrBr (writeBits (ev3 s src r q) (wordAddress (src + 29)) z)

def ev5 (s : MachineState) (src : Nat) (r q z : BitVec 256) : MachineState :=
  copyField evenSaltCode (ev4 s src r q z)

def evOps6 : List Instr := [.ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x10 .x10 3960, .ADDI .x12 .x23 0]

def ev6 (s : MachineState) (src : Nat) (r q z : BitVec 256) : MachineState :=
  evOps6.foldl execInstrBr (ev5 s src r q z)

def evOps7 : List Instr :=
  [.LD .x31 .x23 168, .SD .x23 .x31 0, .LD .x31 .x23 176, .SD .x23 .x31 8,
   .LD .x31 .x23 184, .SD .x23 .x31 16, .LD .x31 .x23 192, .SD .x23 .x31 24]

def ev7 (s : MachineState) (src : Nat) (r q z : BitVec 256) (y : Block) : MachineState :=
  evOps7.foldl execInstrBr (writeBits (ev6 s src r q z) (wordAddress 1536) y)

/-- After `jal zero,<58>`. -/
def ev8 (s : MachineState) (src : Nat) (r q z : BitVec 256) (y : Block) : MachineState :=
  (ev7 s src r q z y).setPC (ckPC 58)

/-! ### Even path: registers and memory -/

private theorem imm_down (n : Nat) (imm : BitVec 12) (value : signExtend12 imm = BitVec.ofNat 64 (2 ^ 64 - 8 * n))
    (a : Nat) (room : n ≤ a) (bounded : n ≤ 256 := by decide) : wordAddress a + signExtend12 imm = wordAddress (a - n) :=
  address_down a n imm value room (by omega)

theorem ck_written_pc {bits : Nat} (s : MachineState) (dst : Word) (coins : BitVec bits) :
    (writeBits s dst coins).pc = s.pc + 4 := by simp only [writeBits, MachineState.setPC]

private theorem imm_up (a n : Nat) (imm : BitVec 12) (value : signExtend12 imm = BitVec.ofNat 64 (8 * n)) :
    wordAddress a + signExtend12 imm = wordAddress (a + n) := by
  rw [value, address_up]

theorem ev0_facts (s : MachineState) :
    (ev0 s).mem = s.mem ∧ (ev0 s).getReg .x6 = s.getMem (s.getReg .x8) ∧ (ev0 s).pc = ckPC 10545 ∧
    ∀ r, r ≠ .x6 → r ≠ .x7 → (ev0 s).getReg r = s.getReg r := by
  obtain ⟨m, h6, _, _, keep⟩ := ck_head_facts s
  refine ⟨?_, ?_, rfl, fun r a b => ?_⟩
  · simpa [ev0] using m
  · simpa [ev0] using h6
  · simpa [ev0] using keep r a b

theorem ev1_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index) :
    (ev1 s).getReg .x10 = wordAddress (src + 29) ∧ (ev1 s).getReg .x12 = wordAddress (src + 33) ∧
    (ev1 s).getReg .x11 = 64 ∧ (ev1 s).getReg .x13 = 0 ∧ (ev1 s).pc = ckPC 10549 ∧ (ev1 s).mem = s.mem ∧
    (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → (ev1 s).getReg r = (ev0 s).getReg r) := by
  obtain ⟨m0, _, p0, k0⟩ := ev0_facts s
  have x19 : (ev0 s).getReg .x19 = wordAddress src := (k0 .x19 (by decide) (by decide)).trans ready.source
  have a10 : (ev1 s).getReg .x10 = wordAddress (src + 29) := by
    simp only [ev1, evOps1, List.foldl]
    rw [addi_other _ .x12 .x10 .x10 32 (by decide), addi_from _ .x10 .x19 232 (by decide),
      addi_other _ .x13 .x0 .x19 0 (by decide), addi_other _ .x11 .x0 .x19 64 (by decide), x19,
      imm_up src 29 232 (by decide)]
  refine ⟨a10, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have prev : (execInstrBr (execInstrBr (execInstrBr (ev0 s) (.ADDI .x11 .x0 64)) (.ADDI .x13 .x0 0))
        (.ADDI .x10 .x19 232)).getReg .x10 = wordAddress (src + 29) := by
      rw [addi_from _ .x10 .x19 232 (by decide), addi_other _ .x13 .x0 .x19 0 (by decide),
        addi_other _ .x11 .x0 .x19 64 (by decide), x19, imm_up src 29 232 (by decide)]
    simp only [ev1, evOps1, List.foldl]
    rw [addi_from _ .x12 .x10 32 (by decide), prev, imm_up (src + 29) 4 32 (by decide)]
  · simp only [ev1, evOps1, List.foldl]
    rw [addi_other _ .x12 .x10 .x11 32 (by decide), addi_other _ .x10 .x19 .x11 232 (by decide),
      addi_other _ .x13 .x0 .x11 0 (by decide), addi_from _ .x11 .x0 64 (by decide)]
    rfl
  · simp only [ev1, evOps1, List.foldl]
    rw [addi_other _ .x12 .x10 .x13 32 (by decide), addi_other _ .x10 .x19 .x13 232 (by decide),
      addi_from _ .x13 .x0 0 (by decide)]
    rfl
  · simp only [ev1, evOps1, List.foldl]
    rw [addi_pc, addi_pc, addi_pc, addi_pc, p0]
    rfl
  · simp only [ev1, evOps1, List.foldl]
    rw [addi_mem, addi_mem, addi_mem, addi_mem, m0]
  · intro r a b c d
    simp only [ev1, evOps1, List.foldl]
    rw [addi_other _ _ _ _ _ c, addi_other _ _ _ _ _ a, addi_other _ _ _ _ _ d, addi_other _ _ _ _ _ b]

theorem ev2_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (r : BitVec 256) :
    (ev2 s src r).getReg .x10 = wordAddress (src + 5) ∧ (ev2 s src r).getReg .x12 = wordAddress (src + 29) ∧
    (ev2 s src r).pc = ckPC 10552 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → (ev2 s src r).getReg g = (ev1 s).getReg g) := by
  obtain ⟨a10, _, _, _, p1, _, _⟩ := ev1_facts s src proof index ready
  let w := writeBits (ev1 s) (wordAddress (src + 33)) r
  have wx : w.getReg .x10 = wordAddress (src + 29) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans a10
  have down : (execInstrBr w (.ADDI .x10 .x10 3904)).getReg .x10 = wordAddress (src + 5) := by
    rw [addi_self w .x10 3904 (by decide), wx, imm_down 24 3904 (by decide) (src + 29) (by omega),
      show src + 29 - 24 = src + 5 by omega]
  refine ⟨(addi_other _ .x12 .x10 .x10 192 (by decide)).trans down, ?_, ?_, ?_⟩
  · rw [ev2, addi_from _ _ _ _ (by decide), down, imm_up (src + 5) 24 192 (by decide)]
  · rw [ev2, addi_pc, addi_pc, ck_written_pc, p1]
    rfl
  · intro g a b
    rw [ev2, addi_other _ _ _ _ _ b, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register]

theorem ev3_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (r q : BitVec 256) :
    (ev3 s src r q).getReg .x10 = wordAddress (src + 29) ∧ (ev3 s src r q).getReg .x12 = wordAddress (src + 29) ∧
    (ev3 s src r q).pc = ckPC 10554 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → (ev3 s src r q).getReg g = (ev1 s).getReg g) := by
  obtain ⟨b10, b12, bpc, bkeep⟩ := ev2_facts s src proof index ready r
  let w := writeBits (ev2 s src r) (wordAddress (src + 29)) q
  have wx : w.getReg .x10 = wordAddress (src + 5) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans b10
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ev3, addi_self w .x10 192 (by decide), wx, imm_up (src + 5) 24 192 (by decide)]
  · rw [ev3, addi_other _ _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, b12]
  · rw [ev3, addi_pc, ck_written_pc, bpc]
    rfl
  · intro g a b
    rw [ev3, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register, bkeep g a b]

private theorem addr_shift (i : Nat) : (BitVec.ofNat 64 i <<< 8) = BitVec.ofNat 64 (256 * i) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 i * BitVec.ofNat 64 256 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm i]

/-- `slli t3,t1,8 ; add t3,gp,t3` with `t1 = i`, `gp = 4056`. -/
theorem tag_base (t : MachineState) (i : Nat) (t6 : t.getReg .x6 = BitVec.ofNat 64 i)
    (t3 : t.getReg .x3 = 4056) :
    (execInstrBr (execInstrBr t (.SLLI .x28 .x6 8)) (.ADD .x28 .x3 .x28)).getReg .x28 =
      BitVec.ofNat 64 (4056 + 256 * i) := by
  have h : (execInstrBr (execInstrBr t (.SLLI .x28 .x6 8)) (.ADD .x28 .x3 .x28)).getReg .x28 =
      t.getReg .x3 + (t.getReg .x6 <<< 8) := by
    simp [execInstrBr]
  rw [h, t6, t3, addr_shift, show (4056 : Word) = BitVec.ofNat 64 4056 by rfl, ← BitVec.ofNat_add]

theorem tag_mem (t : MachineState) :
    (execInstrBr (execInstrBr t (.SLLI .x28 .x6 8)) (.ADD .x28 .x3 .x28)).mem = t.mem := by
  simp [execInstrBr]

theorem tag_keep (t : MachineState) (g : Reg) (h : g ≠ .x28) :
    (execInstrBr (execInstrBr t (.SLLI .x28 .x6 8)) (.ADD .x28 .x3 .x28)).getReg g = t.getReg g := by
  simp [execInstrBr, Ne.symm h]

theorem tag_pc (t : MachineState) :
    (execInstrBr (execInstrBr t (.SLLI .x28 .x6 8)) (.ADD .x28 .x3 .x28)).pc = t.pc + 4 + 4 := by
  simp [execInstrBr]

/-- The even tag: the address of an even leaf's permutation window. -/
theorem even_tag_value (index : Index) (even : c3pEven index) :
    BitVec.ofNat 64 (4056 + 256 * index.val) + signExtend12 (96 : BitVec 12) = c3pTag index := by
  rw [show signExtend12 (96 : BitVec 12) = BitVec.ofNat 64 96 by decide, ← BitVec.ofNat_add]
  unfold c3pTag
  rw [if_pos even]
  congr 1
  omega

theorem odd_tag_value (index : Index) (odd : ¬ c3pEven index) :
    BitVec.ofNat 64 (4056 + 256 * index.val) + signExtend12 (40 : BitVec 12) = c3pTag index := by
  rw [show signExtend12 (40 : BitVec 12) = BitVec.ofNat 64 40 by decide, ← BitVec.ofNat_add]
  unfold c3pTag
  rw [if_neg odd]
  congr 1
  omega

/-- The register state just before the even tag store (`sd t6,32(a0)` at word 10558). -/
def ev4pre (s : MachineState) (src : Nat) (r q z : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (writeBits (ev3 s src r q) (wordAddress (src + 29)) z)
    (.SLLI .x28 .x6 8)) (.ADD .x28 .x3 .x28)) (.ADDI .x31 .x28 96)

theorem ev4_unfold (s : MachineState) (src : Nat) (r q z : BitVec 256) :
    ev4 s src r q z = execInstrBr (ev4pre s src r q z) (.SD .x10 .x31 32) := rfl

theorem ev4pre_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) :
    (ev4pre s src r q z).getReg .x10 = wordAddress (src + 29) ∧
    (ev4pre s src r q z).getReg .x31 = c3pTag index ∧
    (ev4pre s src r q z).pc = ckPC 10558 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → g ≠ .x28 → g ≠ .x31 → (ev4pre s src r q z).getReg g = (ev1 s).getReg g) := by
  obtain ⟨c10, _, cpc, ckeep⟩ := ev3_facts s src proof index ready r q
  obtain ⟨_, h6, _, k0⟩ := ev0_facts s
  obtain ⟨_, _, _, _, _, _, k1⟩ := ev1_facts s src proof index ready
  let w := writeBits (ev3 s src r q) (wordAddress (src + 29)) z
  have w6 : w.getReg .x6 = BitVec.ofNat 64 index.val := by
    rw [CommitGolfCandidate.writeBits_register, ckeep _ (by decide) (by decide),
      k1 _ (by decide) (by decide) (by decide) (by decide), h6, ready.indexValue]
  have w3 : w.getReg .x3 = 4056 := by
    rw [CommitGolfCandidate.writeBits_register, ckeep _ (by decide) (by decide),
      k1 _ (by decide) (by decide) (by decide) (by decide), k0 _ (by decide) (by decide), ready.tagBase]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ev4pre, addi_other _ _ _ _ _ (by decide), tag_keep _ _ (by decide),
      CommitGolfCandidate.writeBits_register, c10]
  · rw [ev4pre, addi_from _ _ _ _ (by decide), tag_base w index.val w6 w3, even_tag_value index even]
  · rw [ev4pre, addi_pc, tag_pc, ck_written_pc, cpc]
    rfl
  · intro g a b c d
    rw [ev4pre, addi_other _ _ _ _ _ d, tag_keep _ _ c, CommitGolfCandidate.writeBits_register,
      ckeep g a b]

theorem write_window_point {n : Nat} (X Y : Memory) (a : Nat) (d : Words n) (w : Nat) (h : X w = Y w) :
    writeWindow X a d w = writeWindow Y a d w := by
  simp only [writeWindow]
  split
  · rfl
  · exact h

theorem write_word_point (X Y : Memory) (a : Nat) (d : Word) (w : Nat) (h : X w = Y w) :
    writeWord X a d w = writeWord Y a d w := by
  simp only [writeWord]
  split
  · rfl
  · exact h

theorem ev2_view (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (r : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (ev2 s src r) w = writeWindow (memoryView s) (src + 33) (digestWords r) w := by
  have room := ready.sourceBound
  obtain ⟨_, _, _, _, _, m1, _⟩ := ev1_facts s src proof index ready
  have same : (ev2 s src r).mem = (writeBits (ev1 s) (wordAddress (src + 33)) r).mem := by
    rw [ev2, addi_mem, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw]
  exact write_window_point _ _ _ _ _ (congrFun (memoryView_congr m1) w)

theorem ev3_view (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (r q : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (ev3 s src r q) w =
      writeWindow (writeWindow (memoryView s) (src + 33) (digestWords r)) (src + 29) (digestWords q) w := by
  have room := ready.sourceBound
  have same : (ev3 s src r q).mem = (writeBits (ev2 s src r) (wordAddress (src + 29)) q).mem := by
    rw [ev3, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw]
  exact write_window_point _ _ _ _ _ (ev2_view s src proof index ready r w hw)

theorem ev4pre_view (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (r q z : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (ev4pre s src r q z) w =
      writeWindow (writeWindow (writeWindow (memoryView s) (src + 33) (digestWords r)) (src + 29) (digestWords q))
        (src + 29) (digestWords z) w := by
  have room := ready.sourceBound
  have same : (ev4pre s src r q z).mem = (writeBits (ev3 s src r q) (wordAddress (src + 29)) z).mem := by
    rw [ev4pre, addi_mem, tag_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw]
  exact write_window_point _ _ _ _ _ (ev3_view s src proof index ready r q w hw)

/-- Memory of the even path after the three compressions and the tag store. -/
def evenMem (M : Memory) (src : Nat) (dr dq dz : Words 4) (tag : Word) : Memory :=
  writeWord (writeWindow (writeWindow (writeWindow M (src + 33) dr) (src + 29) dq) (src + 29) dz) (src + 33) tag

theorem ev4_memory (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (ev4 s src r q z) w =
      evenMem (memoryView s) src (digestWords r) (digestWords q) (digestWords z) (c3pTag index) w := by
  have room := ready.sourceBound
  obtain ⟨p10, p31, _, _⟩ := ev4pre_facts s src proof index ready even r q z
  have same : (ev4 s src r q z).mem =
      ((ev4pre s src r q z).setMem ((ev4pre s src r q z).getReg .x10 + signExtend12 32)
        ((ev4pre s src r q z).getReg .x31)).mem := by
    rw [ev4_unfold, sd_mem]
  rw [memoryView_congr same, p10, p31, imm_up (src + 29) 4 32 (by decide),
    view_store _ (src + 29 + 4) w _ (by omega) (by omega), show src + 29 + 4 = src + 33 by omega]
  exact write_word_point _ _ _ _ _ (ev4pre_view s src proof index ready r q z w hw)

theorem even_mem_outside (M : Memory) (src : Nat) (dr dq dz : Words 4) (tag : Word) (w : Nat)
    (outside : w < src + 29 ∨ src + 37 ≤ w) : evenMem M src dr dq dz tag w = M w := by
  simp only [evenMem, writeWord, writeWindow]
  split_ifs <;> first | omega | rfl

theorem ev4_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) :
    (ev4 s src r q z).getReg .x10 = wordAddress (src + 29) ∧ (ev4 s src r q z).pc = ckPC 10559 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → g ≠ .x28 → g ≠ .x31 → (ev4 s src r q z).getReg g = (ev1 s).getReg g) := by
  obtain ⟨p10, _, ppc, pkeep⟩ := ev4pre_facts s src proof index ready even r q z
  refine ⟨by rw [ev4_unfold, sd_reg, p10], ?_, fun g a b c d => by rw [ev4_unfold, sd_reg, pkeep g a b c d]⟩
  rw [ev4_unfold, sd_pc, ppc]
  rfl

theorem ev1_keeps (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (g : Reg) (a : g ≠ .x6) (b : g ≠ .x7) (c : g ≠ .x10) (d : g ≠ .x11) (e : g ≠ .x12) (f : g ≠ .x13) :
    (ev1 s).getReg g = s.getReg g :=
  ((ev1_facts s src proof index ready).2.2.2.2.2.2 g c d e f).trans ((ev0_facts s).2.2.2 g a b)

theorem ev4_copy_ready (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) :
    CopyReady evenSaltCode (ev4 s src r q z) proof (8 * (src + 35)) 0 := by
  obtain ⟨d10, dpc, dkeep⟩ := ev4_facts s src proof index ready even r q z
  have pb := ready.proofBound
  have sb := ready.sourceBound
  refine ⟨?_, ?_, ?_, ?_, ?_, ready.proofAligned, ?_⟩
  · change (ev4 s src r q z).pc = ckPC (10559 + 2 * 0)
    exact dpc
  · change (ev4 s src r q z).getReg .x21 = _
    rw [dkeep .x21 (by decide) (by decide) (by decide) (by decide),
      ev1_keeps s src proof index ready .x21 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), ready.proofPointer]
  · change (ev4 s src r q z).getReg .x10 + BitVec.ofNat 64 (8 * 6) = _
    rw [d10, address_up]
    try rfl
  · change proof + 2 * 8 ≤ MEMORY_BYTES; omega
  · change 8 * (src + 35) + 2 * 8 ≤ MEMORY_BYTES; unfold MEMORY_BYTES; omega
  · change 8 * (src + 35) % 2 = 0; omega

theorem ev5_pc (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) : (ev5 s src r q z).pc = ckPC 10575 :=
  copy_field_pc _ _ _ _ (ev4_copy_ready s src proof index ready even r q z)

theorem ev5_reg (s : MachineState) (src : Nat) (r q z : BitVec 256) (g : Reg) (h : g ≠ .x31) :
    (ev5 s src r q z).getReg g = (ev4 s src r q z).getReg g :=
  copy_field_register _ _ g h

theorem ev6_mem (s : MachineState) (src : Nat) (r q z : BitVec 256) :
    (ev6 s src r q z).mem = (ev5 s src r q z).mem := by
  simp only [ev6, evOps6, List.foldl]
  rw [addi_mem, addi_mem, addi_mem, addi_mem]

theorem ev6_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) :
    (ev6 s src r q z).getReg .x10 = wordAddress (src + 12) ∧
    (ev6 s src r q z).getReg .x12 = wordAddress 1536 ∧
    (ev6 s src r q z).getReg .x5 = 0 ∧
    (ev6 s src r q z).getReg .x11 = 200 ∧
    (ev6 s src r q z).getReg .x13 = 1 ∧
    (ev6 s src r q z).pc = ckPC 10579 := by
  have sb := ready.sourceBound
  obtain ⟨d10, _, dkeep⟩ := ev4_facts s src proof index ready even r q z
  have p5 := ev5_pc s src proof index ready even r q z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ev6, evOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x10 0 (by decide), addi_self _ .x10 3960 (by decide),
      addi_other _ .x13 .x0 .x10 1 (by decide), addi_other _ .x11 .x0 .x10 200 (by decide),
      ev5_reg _ _ _ _ _ .x10 (by decide), d10, imm_down 17 3960 (by decide) (src + 29) (by omega),
      show src + 29 - 17 = src + 12 by omega]
  · simp only [ev6, evOps6, List.foldl]
    rw [addi_from _ .x12 .x23 0 (by decide), addi_other _ .x10 .x10 .x23 3960 (by decide),
      addi_other _ .x13 .x0 .x23 1 (by decide), addi_other _ .x11 .x0 .x23 200 (by decide),
      ev5_reg _ _ _ _ _ .x23 (by decide), dkeep .x23 (by decide) (by decide) (by decide) (by decide),
      ev1_keeps s src proof index ready .x23 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), ready.digest, imm_up 1536 0 0 (by decide)]
  · simp only [ev6, evOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x5 0 (by decide), addi_other _ .x10 .x10 .x5 3960 (by decide),
      addi_other _ .x13 .x0 .x5 1 (by decide), addi_other _ .x11 .x0 .x5 200 (by decide),
      ev5_reg _ _ _ _ _ .x5 (by decide), dkeep .x5 (by decide) (by decide) (by decide) (by decide),
      ev1_keeps s src proof index ready .x5 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), ready.selector]
  · simp only [ev6, evOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x11 0 (by decide), addi_other _ .x10 .x10 .x11 3960 (by decide),
      addi_other _ .x13 .x0 .x11 1 (by decide), addi_from _ .x11 .x0 200 (by decide)]
    rfl
  · simp only [ev6, evOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x13 0 (by decide), addi_other _ .x10 .x10 .x13 3960 (by decide),
      addi_from _ .x13 .x0 1 (by decide)]
    rfl
  · simp only [ev6, evOps6, List.foldl]
    rw [addi_pc, addi_pc, addi_pc, addi_pc, p5]
    rfl

/-! ### Even path: the permutation window and the digest -/

/-- The salt words copied from the proof. -/
def ckNonce (s : MachineState) (proof : Nat) : Words 2 := fun i => (readBuffer s proof 16).extractLsb' (64 * i.val) 64

theorem copy_frame (c : CopyCode) (t : MachineState) (proof target : Nat) (ready : CopyReady c t proof target 0)
    (order : target ≤ proof) (count : c.count = 8) (w : Nat) (bound : w < 2 ^ 33)
    (outside : 8 * w + 8 ≤ target ∨ target + 16 ≤ 8 * w) :
    memoryView (copyField c t) w = memoryView t w := by
  have frame := (code_bytes c t _ _ ready order).2
  apply word_eq_of_byte_frame
  intro i hi
  apply frame
  intro j hj eq
  rw [count] at hj
  have same := congrArg BitVec.toNat eq
  have one : 8 * w + i < 2 ^ 64 := by omega
  have tb : target + 2 * c.count ≤ MEMORY_BYTES := ready.dstBound
  rw [count] at tb
  have two : target + j < 2 ^ 64 := by unfold MEMORY_BYTES at tb; omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt two] at same
  omega

theorem copied_words (c : CopyCode) (t : MachineState) (proof dst : Nat) (ready : CopyReady c t proof (8 * dst) 0)
    (order : 8 * dst ≤ proof) (count : c.count = 8) (i : Nat) (hi : i < 2) :
    memoryView (copyField c t) (dst + i) = (readBuffer t proof 16).extractLsb' (64 * i) 64 := by
  have fr : readBuffer (copyField c t) (8 * dst) 16 = readBuffer t proof 16 := by
    have := code_read c t proof (8 * dst) ready order
    rwa [count] at this
  have win := congrFun (buffer_window (copyField c t) dst 2) ⟨i, hi⟩
  change memoryView (copyField c t) (dst + i) =
    (readBuffer (copyField c t) (8 * dst) (8 * 2)).extractLsb' (64 * i) 64 at win
  rw [win, show 8 * 2 = 16 by rfl, fr]

theorem ev4_proof_read (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) :
    readBuffer (ev4 s src r q z) proof 16 = readBuffer s proof 16 := by
  have ap := ready.apart
  have pb := ready.proofBound
  apply buffer_byte_frame
  intro j hj
  rw [ev4_memory s src proof index ready even r q z _ (by unfold MEMORY_BYTES at pb; omega),
    even_mem_outside _ _ _ _ _ _ _ (by omega)]

theorem ev_perm_input (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) :
    (window (memoryView (ev6 s src r q z)) (src + 12) : Words 25) =
      c3pEvenWords index (ckNonce s proof) (window (memoryView s) (src + 5)) (digestWords z) (digestWords r) := by
  have sb := ready.sourceBound
  have ap := ready.apart
  have cr := ev4_copy_ready s src proof index ready even r q z
  funext k
  have kt := k.isLt
  change memoryView (ev6 s src r q z) (src + 12 + k.val) = _
  rw [memoryView_congr (ev6_mem s src r q z)]
  by_cases salt : 23 ≤ k.val
  · have word : memoryView (ev5 s src r q z) (src + 35 + (k.val - 23)) =
        (readBuffer (ev4 s src r q z) proof 16).extractLsb' (64 * (k.val - 23)) 64 :=
      copied_words evenSaltCode (ev4 s src r q z) proof (src + 35) cr (by omega) rfl (k.val - 23) (by omega)
    rw [show src + 12 + k.val = src + 35 + (k.val - 23) by omega, word, ev4_proof_read s src proof index ready even r q z]
    simp only [c3pEvenWords]
    rw [dite_eq_right (show ¬ k.val < 17 by omega), dite_eq_right (show ¬ k.val < 21 by omega),
      ite_eq_right (show k.val ≠ 21 by omega), ite_eq_right (show k.val ≠ 22 by omega)]
    rfl
  · change memoryView (copyField evenSaltCode (ev4 s src r q z)) _ = _
    rw [copy_frame evenSaltCode _ proof _ cr (by omega) rfl _ (by omega) (by omega),
      ev4_memory s src proof index ready even r q z _ (by omega)]
    simp only [c3pEvenWords]
    by_cases low : k.val < 17
    · rw [even_mem_outside _ _ _ _ _ _ _ (by omega), dite_eq_left low]
      change memoryView s (src + 12 + k.val) = memoryView s (src + 5 + (7 + k.val))
      congr 1
      omega
    · rw [dite_eq_right low]
      by_cases mid : k.val < 21
      · rw [dite_eq_left mid]
        simp only [evenMem, writeWord, writeWindow]
        rw [ite_eq_right (show src + 12 + k.val ≠ src + 33 by omega),
          dite_eq_left (show src + 29 ≤ src + 12 + k.val ∧ src + 12 + k.val < src + 29 + 4 by omega)]
        congr 1
        ext
        simp only [Fin.val_mk]
        omega
      · rw [dite_eq_right mid]
        by_cases tag : k.val = 21
        · rw [ite_eq_left tag]
          simp only [evenMem, writeWord]
          rw [ite_eq_left (show src + 12 + k.val = src + 33 by omega)]
        · rw [ite_eq_right tag, ite_eq_left (show k.val = 22 by omega)]
          simp only [evenMem, writeWord, writeWindow]
          rw [ite_eq_right (show src + 12 + k.val ≠ src + 33 by omega),
            dite_eq_right (show ¬ (src + 29 ≤ src + 12 + k.val ∧ src + 12 + k.val < src + 29 + 4) by omega),
            dite_eq_right (show ¬ (src + 29 ≤ src + 12 + k.val ∧ src + 12 + k.val < src + 29 + 4) by omega),
            dite_eq_left (show src + 33 ≤ src + 12 + k.val ∧ src + 12 + k.val < src + 33 + 4 by omega)]
          congr 1
          ext
          simp only [Fin.val_mk]
          omega

/-- One `ld t6,168+8k(s7) ; sd t6,8k(s7)` pair with `s7 = 12288`. -/
theorem copy_pair (t : MachineState) (h23 : t.getReg .x23 = wordAddress 1536) (k : Nat) (hk : k < 4)
    (load store : BitVec 12) (lv : signExtend12 load = BitVec.ofNat 64 (8 * (21 + k)))
    (sv : signExtend12 store = BitVec.ofNat 64 (8 * k)) :
    let u := execInstrBr (execInstrBr t (.LD .x31 .x23 load)) (.SD .x23 .x31 store)
    (∀ w < 2 ^ 33, memoryView u w = writeWord (memoryView t) (1536 + k) (memoryView t (1557 + k)) w) ∧
      u.getReg .x23 = wordAddress 1536 ∧ u.pc = t.pc + 4 + 4 ∧
      (∀ g, g ≠ .x31 → u.getReg g = t.getReg g) := by
  intro u
  let a := execInstrBr t (.LD .x31 .x23 load)
  have a23 : a.getReg .x23 = wordAddress 1536 := (ld_other _ _ _ _ _ (by decide)).trans h23
  have a31 : a.getReg .x31 = memoryView t (1557 + k) := by
    rw [ld_same _ _ _ _ (by decide), h23, lv, address_up, show 1536 + (21 + k) = 1557 + k by omega]
    rfl
  refine ⟨fun w hw => ?_, (sd_reg _ _ _ _ _).trans a23, ?_, fun g h => (sd_reg _ _ _ _ _).trans (ld_other _ _ _ _ _ h)⟩
  · have same : u.mem = (a.setMem (a.getReg .x23 + signExtend12 store) (a.getReg .x31)).mem := sd_mem _ _ _ _
    rw [memoryView_congr same, a23, a31, sv, address_up, view_store _ (1536 + k) w _ (by omega) (by omega)]
    exact write_word_point _ _ _ _ _ (congrFun (memoryView_congr (ld_mem _ _ _ _)) w)
  · change (a.pc + 4) = _
    rw [ld_pc]

theorem reply_top (y : Block) :
    packDigestWords (fun k : Fin 4 => y.extractLsb' (64 * (21 + k.val)) 64) = c3pEvenDigest y := by
  apply digest_words_injective
  rw [digest_words_pack]
  funext k
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [digestWords, c3pEvenDigest, BitVec.getLsbD_extractLsb', true_and_of inside,
    true_and_of (show 64 * k.val + bit < 256 by omega)]
  exact getLsbD_index _ (by omega)

theorem ev6_x23 (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) : (ev6 s src r q z).getReg .x23 = wordAddress 1536 := by
  obtain ⟨_, _, dkeep⟩ := ev4_facts s src proof index ready even r q z
  simp only [ev6, evOps6, List.foldl]
  rw [addi_other _ .x12 .x23 .x23 0 (by decide), addi_other _ .x10 .x10 .x23 3960 (by decide),
    addi_other _ .x13 .x0 .x23 1 (by decide), addi_other _ .x11 .x0 .x23 200 (by decide),
    ev5_reg _ _ _ _ _ .x23 (by decide), dkeep .x23 (by decide) (by decide) (by decide) (by decide),
    ev1_keeps s src proof index ready .x23 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ready.digest]

theorem ev7_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) (y : Block) :
    let Y := writeBits (ev6 s src r q z) (wordAddress 1536) y
    (∀ w < 2 ^ 33, memoryView (ev7 s src r q z y) w =
      if 1536 ≤ w ∧ w < 1540 then memoryView Y (w + 21) else memoryView Y w) ∧
    (ev7 s src r q z y).pc = ckPC 10588 ∧
    (∀ g, g ≠ .x31 → (ev7 s src r q z y).getReg g = (ev6 s src r q z).getReg g) := by
  intro Y
  have y23 : Y.getReg .x23 = wordAddress 1536 :=
    (CommitGolfCandidate.writeBits_register _ _ _ _).trans (ev6_x23 s src proof index ready even r q z)
  obtain ⟨m0, a0, p0, k0⟩ := copy_pair Y y23 0 (by decide) 168 0 (by decide) (by decide)
  obtain ⟨m1, a1, p1, k1⟩ := copy_pair _ a0 1 (by decide) 176 8 (by decide) (by decide)
  obtain ⟨m2, a2, p2, k2⟩ := copy_pair _ a1 2 (by decide) 184 16 (by decide) (by decide)
  obtain ⟨m3, _, p3, k3⟩ := copy_pair _ a2 3 (by decide) 192 24 (by decide) (by decide)
  have unfold7 : ev7 s src r q z y = execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr
      (execInstrBr (execInstrBr (execInstrBr Y (.LD .x31 .x23 168)) (.SD .x23 .x31 0)) (.LD .x31 .x23 176))
      (.SD .x23 .x31 8)) (.LD .x31 .x23 184)) (.SD .x23 .x31 16)) (.LD .x31 .x23 192)) (.SD .x23 .x31 24) := rfl
  have e1 : ∀ w < 2 ^ 33, memoryView (execInstrBr (execInstrBr Y (.LD .x31 .x23 168)) (.SD .x23 .x31 0)) w =
      if w = 1536 then memoryView Y 1557 else memoryView Y w := fun w hw => by
    rw [m0 w hw]; simp only [writeWord, Nat.add_zero]
  have e2 : ∀ w < 2 ^ 33, memoryView (execInstrBr (execInstrBr (execInstrBr (execInstrBr Y (.LD .x31 .x23 168))
      (.SD .x23 .x31 0)) (.LD .x31 .x23 176)) (.SD .x23 .x31 8)) w =
      if w = 1537 then memoryView Y 1558 else if w = 1536 then memoryView Y 1557 else memoryView Y w := fun w hw => by
    rw [m1 w hw, e1 _ (by norm_num)]; simp only [writeWord]; rw [e1 w hw]; split_ifs <;> first | omega | rfl
  have e3 : ∀ w < 2 ^ 33, memoryView (execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr
      (execInstrBr Y (.LD .x31 .x23 168)) (.SD .x23 .x31 0)) (.LD .x31 .x23 176)) (.SD .x23 .x31 8))
      (.LD .x31 .x23 184)) (.SD .x23 .x31 16)) w =
      if w = 1538 then memoryView Y 1559 else if w = 1537 then memoryView Y 1558 else
        if w = 1536 then memoryView Y 1557 else memoryView Y w := fun w hw => by
    rw [m2 w hw, e2 _ (by norm_num)]; simp only [writeWord]; rw [e2 w hw]; split_ifs <;> first | omega | rfl
  refine ⟨fun w hw => ?_, ?_, fun g h => ?_⟩
  · rw [unfold7, m3 w hw, e3 _ (by norm_num)]
    simp only [writeWord]
    rw [e3 w hw]
    split_ifs <;> first | omega | (congr 1; omega) | rfl
  · rw [unfold7, p3, p2, p1, p0, ck_written_pc, (ev6_facts s src proof index ready even r q z).2.2.2.2.2]
    rfl
  · rw [unfold7, k3 g h, k2 g h, k1 g h, k0 g h, CommitGolfCandidate.writeBits_register]

theorem ev8_digest (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) (y : Block) :
    readBuffer (ev8 s src r q z y) 12288 32 = c3pEvenDigest y := by
  obtain ⟨view, _, _⟩ := ev7_facts s src proof index ready even r q z y
  rw [show (12288 : Nat) = 8 * 1536 by rfl, c3_read_digest, ← reply_top y]
  congr 1
  funext k
  have kt := k.isLt
  change memoryView ((ev7 s src r q z y).setPC (ckPC 58)) (1536 + k.val) = _
  rw [memoryView_congr (mem_set_pc _ _), view _ (by omega), if_pos (by omega)]
  refine (permutation_write_memory _ 1536 _ y (by decide) (by omega)).trans ?_
  rw [writeWindow, dite_eq_left (show 1536 ≤ 1536 + k.val + 21 ∧ 1536 + k.val + 21 < 1536 + 25 by omega)]
  change y.extractLsb' (64 * (1536 + k.val + 21 - 1536)) 64 = _
  congr 1
  omega

/-! ### Execution helpers -/

theorem ordinary_one (st next : MachineState) (instr : Instr) (fuel : Nat)
    (fetched : fetch packedImage st = some (.base instr)) (stepped : ordinaryStep st (.base instr) = some next)
    (unit : instructionCycles (.base instr) = 1) :
    execute packedImage (1 + fuel) st false =
      (do let result ← execute packedImage fuel next false; return result.charge 1 0) := by
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped, unit]

theorem charge_charge (r : Execution) (a b c d : Nat) : (r.charge a b).charge c d = r.charge (c + a) (d + b) := by
  simp only [Execution.charge, Nat.add_assoc]

theorem sd_step (t : MachineState) (b src : Reg) (imm : BitVec 12)
    (valid : accessValid (t.getReg b + signExtend12 imm) 8 = true) :
    ordinaryStep t (.base (.SD b src imm)) = some (execInstrBr t (.SD b src imm)) := by
  change (if memoryArgumentsValid t (.SD b src imm) = true then some (execInstrBr t (.SD b src imm)) else none) = _
  rw [show memoryArgumentsValid t (.SD b src imm) = accessValid (t.getReg b + signExtend12 imm) 8 from rfl, valid]
  rfl

theorem ld_step (t : MachineState) (rd b : Reg) (imm : BitVec 12)
    (valid : accessValid (t.getReg b + signExtend12 imm) 8 = true) :
    ordinaryStep t (.base (.LD rd b imm)) = some (execInstrBr t (.LD rd b imm)) := by
  change (if memoryArgumentsValid t (.LD rd b imm) = true then some (execInstrBr t (.LD rd b imm)) else none) = _
  rw [show memoryArgumentsValid t (.LD rd b imm) = accessValid (t.getReg b + signExtend12 imm) 8 from rfl, valid]
  rfl

theorem word_valid (a k : Nat) (imm : BitVec 12) (value : signExtend12 imm = BitVec.ofNat 64 (8 * k))
    (bound : a + k < 2 ^ 33) : accessValid (wordAddress a + signExtend12 imm) 8 = true := by
  rw [value]
  exact word_access a k bound

/-! ### Even path: execution -/

def evQueries (s : MachineState) (src : Nat) : OracleComp World MachineState := do
  let r ← World.query (.inr (.inl (readBuffer (ev1 s) (8 * (src + 29)) 64)))
  let q ← World.query (.inr (.inl (readBuffer (ev2 s src r) (8 * (src + 5)) 64)))
  let z ← World.query (.inr (.inl (readBuffer (ev3 s src r q) (8 * (src + 29)) 64)))
  let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (ev6 s src r q z)) (src + 12))))))
  return ev8 s src r q z y

theorem execute_ev1 (s : MachineState) (fuel : Nat) :
    execute packedImage (4 + fuel) (ev0 s) false =
      (do let result ← execute packedImage fuel (ev1 s) false; return result.charge 4 0) := by
  apply execute_unit_steps (states := fun i => (evOps1.take i).foldl execInstrBr (ev0 s))
  intro i bounded
  refine ⟨.base (evOps1[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply ck_fetch _ (10545 + i) _ (by omega)
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_ev6 (s : MachineState) (src : Nat) (r q z : BitVec 256) (pc : (ev5 s src r q z).pc = ckPC 10575)
    (fuel : Nat) :
    execute packedImage (4 + fuel) (ev5 s src r q z) false =
      (do let result ← execute packedImage fuel (ev6 s src r q z) false; return result.charge 4 0) := by
  apply execute_unit_steps (states := fun i => (evOps6.take i).foldl execInstrBr (ev5 s src r q z))
  intro i bounded
  refine ⟨.base (evOps6[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply ck_fetch _ (10575 + i) _ (by omega)
    · interval_cases i <;> simp only [List.take, List.foldl, evOps6, addi_pc, pc] <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_even (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (fuel : Nat) :
    execute packedImage (44 + fuel) (ev0 s) false =
      (do let d ← evQueries s src
          let res ← execute packedImage fuel d false
          return res.charge 94 4) := by
  have sb := ready.sourceBound
  obtain ⟨a10, a12, a11, a13, p1, _, k1⟩ := ev1_facts s src proof index ready
  have sel1 : (ev1 s).getReg .x5 = 0 :=
    (k1 .x5 (by decide) (by decide) (by decide) (by decide)).trans
      (((ev0_facts s).2.2.2 .x5 (by decide) (by decide)).trans ready.selector)
  rw [show 44 + fuel = 4 + ((39 + fuel) + 1) by omega, execute_ev1 s,
    execute_compression_on packedImage (39 + fuel) (ev1 s) false (src + 29) (src + 33) (by omega) (by omega)
      a10 a12 sel1 a11 a13 (ck_fetch _ 10549 .ECALL (by decide) p1 rfl)]
  simp only [evQueries, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro r _
  -- two ordinary steps and the second compression (q)
  have w1pc : (writeBits (ev1 s) (wordAddress (src + 33)) r).pc = ckPC 10550 := by
    rw [ck_written_pc, p1]; rfl
  have m1pc : (execInstrBr (writeBits (ev1 s) (wordAddress (src + 33)) r) (.ADDI .x10 .x10 3904)).pc = ckPC 10551 := by
    rw [addi_pc, w1pc]; rfl
  obtain ⟨b10, b12, bpc, bkeep⟩ := ev2_facts s src proof index ready r
  rw [show 39 + fuel = 1 + (1 + ((36 + fuel) + 1)) by omega,
    ordinary_one _ _ (.ADDI .x10 .x10 3904) _ (ck_fetch _ 10550 _ (by decide) w1pc rfl) rfl rfl,
    ordinary_one _ (ev2 s src r) (.ADDI .x12 .x10 192) _ (ck_fetch _ 10551 _ (by decide) m1pc rfl) rfl rfl,
    execute_compression_on packedImage (36 + fuel) (ev2 s src r) false (src + 5) (src + 29) (by omega) (by omega)
      b10 b12 ((bkeep .x5 (by decide) (by decide)).trans sel1) ((bkeep .x11 (by decide) (by decide)).trans a11)
      ((bkeep .x13 (by decide) (by decide)).trans a13) (ck_fetch _ 10552 .ECALL (by decide) bpc rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro q _
  -- one ordinary step and the third compression (z)
  obtain ⟨c10, c12, cpc, ckeep⟩ := ev3_facts s src proof index ready r q
  have w2pc : (writeBits (ev2 s src r) (wordAddress (src + 29)) q).pc = ckPC 10553 := by
    rw [ck_written_pc, bpc]; rfl
  rw [show 36 + fuel = 1 + ((34 + fuel) + 1) by omega,
    ordinary_one _ (ev3 s src r q) (.ADDI .x10 .x10 192) _ (ck_fetch _ 10553 _ (by decide) w2pc rfl) rfl rfl,
    execute_compression_on packedImage (34 + fuel) (ev3 s src r q) false (src + 29) (src + 29) (by omega) (by omega)
      c10 c12 ((ckeep .x5 (by decide) (by decide)).trans sel1) ((ckeep .x11 (by decide) (by decide)).trans a11)
      ((ckeep .x13 (by decide) (by decide)).trans a13) (ck_fetch _ 10554 .ECALL (by decide) cpc rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro z _
  -- tag (4 steps), salt copy (16), permutation setup (4), permutation call
  let w3 := writeBits (ev3 s src r q) (wordAddress (src + 29)) z
  have w3pc : w3.pc = ckPC 10555 := by rw [ck_written_pc, cpc]; rfl
  have w3x10 : w3.getReg .x10 = wordAddress (src + 29) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans c10
  let t1 := execInstrBr w3 (.SLLI .x28 .x6 8)
  let t2 := execInstrBr t1 (.ADD .x28 .x3 .x28)
  have t1pc : t1.pc = ckPC 10556 := by change w3.pc + 4 = _; rw [w3pc]; rfl
  have t2pc : t2.pc = ckPC 10557 := by change t1.pc + 4 = _; rw [t1pc]; rfl
  obtain ⟨p10, _, ppc, _⟩ := ev4pre_facts s src proof index ready even r q z
  have sdValid : accessValid ((ev4pre s src r q z).getReg .x10 + signExtend12 32) 8 = true := by
    rw [p10]; exact word_valid (src + 29) 4 32 (by decide) (by omega)
  have copyRun : ∀ X, execute packedImage (16 + X) (ev4 s src r q z) false =
      (do let res ← execute packedImage X (ev5 s src r q z) false; return res.charge 16 0) := fun X =>
    copy_field_execute evenSaltCode _ _ _ (ev4_copy_ready s src proof index ready even r q z) X false
  have p4 : (ev4 s src r q z).pc = ckPC 10559 := (ev4_facts s src proof index ready even r q z).2.1
  have p5 := ev5_pc s src proof index ready even r q z
  obtain ⟨e10, e12, e5, e11, e13, e6pc⟩ := ev6_facts s src proof index ready even r q z
  rw [show 34 + fuel = 1 + (1 + (1 + (1 + (16 + (4 + ((8 + (1 + fuel)) + 1)))))) by omega,
    ordinary_one _ t1 (.SLLI .x28 .x6 8) _ (ck_fetch _ 10555 _ (by decide) w3pc rfl) rfl rfl,
    ordinary_one _ t2 (.ADD .x28 .x3 .x28) _ (ck_fetch _ 10556 _ (by decide) t1pc rfl) rfl rfl,
    ordinary_one _ (ev4pre s src r q z) (.ADDI .x31 .x28 96) _ (ck_fetch _ 10557 _ (by decide) t2pc rfl) rfl rfl,
    ordinary_one _ (ev4 s src r q z) (.SD .x10 .x31 32) _ (ck_fetch _ 10558 _ (by decide) ppc rfl)
      (sd_step _ _ _ _ sdValid) rfl,
    copyRun, execute_ev6 s src r q z p5,
    execute_permutation_call packedImage ((8 + (1 + fuel))) (ev6 s src r q z) false (src + 12) 1536 (by omega)
      (by decide) e10 e12 e5 e11 e13 (ck_fetch _ 10579 .ECALL (by decide) e6pc rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro y _
  -- the digest copy (8 steps) and the jump back
  let Y := writeBits (ev6 s src r q z) (wordAddress 1536) y
  have y23 : Y.getReg .x23 = wordAddress 1536 :=
    (CommitGolfCandidate.writeBits_register _ _ _ _).trans (ev6_x23 s src proof index ready even r q z)
  have ypc : Y.pc = ckPC 10580 := by rw [ck_written_pc, e6pc]; rfl
  obtain ⟨_, a0, p0, _⟩ := copy_pair Y y23 0 (by decide) 168 0 (by decide) (by decide)
  obtain ⟨_, a1, p1', _⟩ := copy_pair _ a0 1 (by decide) 176 8 (by decide) (by decide)
  obtain ⟨_, a2, p2, _⟩ := copy_pair _ a1 2 (by decide) 184 16 (by decide) (by decide)
  obtain ⟨_, _, p3, _⟩ := copy_pair _ a2 3 (by decide) 192 24 (by decide) (by decide)
  have run8 : ∀ X, execute packedImage (8 + X) Y false =
      (do let res ← execute packedImage X (ev7 s src r q z y) false; return res.charge 8 0) := by
    intro X
    let L0 := execInstrBr Y (.LD .x31 .x23 168)
    let S0 := execInstrBr L0 (.SD .x23 .x31 0)
    let L1 := execInstrBr S0 (.LD .x31 .x23 176)
    let S1 := execInstrBr L1 (.SD .x23 .x31 8)
    let L2 := execInstrBr S1 (.LD .x31 .x23 184)
    let S2 := execInstrBr L2 (.SD .x23 .x31 16)
    let L3 := execInstrBr S2 (.LD .x31 .x23 192)
    have l0 : L0.getReg .x23 = wordAddress 1536 := (ld_other _ _ _ _ _ (by decide)).trans y23
    have l1 : L1.getReg .x23 = wordAddress 1536 := (ld_other _ _ _ _ _ (by decide)).trans a0
    have l2 : L2.getReg .x23 = wordAddress 1536 := (ld_other _ _ _ _ _ (by decide)).trans a1
    have l3 : L3.getReg .x23 = wordAddress 1536 := (ld_other _ _ _ _ _ (by decide)).trans a2
    have q0 : L0.pc = ckPC 10581 := by change Y.pc + 4 = _; rw [ypc]; rfl
    have q1 : S0.pc = ckPC 10582 := by rw [p0, ypc]; rfl
    have q2 : L1.pc = ckPC 10583 := by change S0.pc + 4 = _; rw [q1]; rfl
    have q3 : S1.pc = ckPC 10584 := by rw [p1', q1]; rfl
    have q4 : L2.pc = ckPC 10585 := by change S1.pc + 4 = _; rw [q3]; rfl
    have q5 : S2.pc = ckPC 10586 := by rw [p2, q3]; rfl
    have q6 : L3.pc = ckPC 10587 := by change S2.pc + 4 = _; rw [q5]; rfl
    rw [show 8 + X = 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + X))))))) by omega,
      ordinary_one _ L0 (.LD .x31 .x23 168) _ (ck_fetch _ 10580 _ (by decide) ypc rfl)
        (ld_step _ _ _ _ (by rw [y23]; exact word_valid 1536 21 168 (by decide) (by decide))) rfl,
      ordinary_one _ S0 (.SD .x23 .x31 0) _ (ck_fetch _ 10581 _ (by decide) q0 rfl)
        (sd_step _ _ _ _ (by rw [l0]; exact word_valid 1536 0 0 (by decide) (by decide))) rfl,
      ordinary_one _ L1 (.LD .x31 .x23 176) _ (ck_fetch _ 10582 _ (by decide) q1 rfl)
        (ld_step _ _ _ _ (by rw [a0]; exact word_valid 1536 22 176 (by decide) (by decide))) rfl,
      ordinary_one _ S1 (.SD .x23 .x31 8) _ (ck_fetch _ 10583 _ (by decide) q2 rfl)
        (sd_step _ _ _ _ (by rw [l1]; exact word_valid 1536 1 8 (by decide) (by decide))) rfl,
      ordinary_one _ L2 (.LD .x31 .x23 184) _ (ck_fetch _ 10584 _ (by decide) q3 rfl)
        (ld_step _ _ _ _ (by rw [a1]; exact word_valid 1536 23 184 (by decide) (by decide))) rfl,
      ordinary_one _ S2 (.SD .x23 .x31 16) _ (ck_fetch _ 10585 _ (by decide) q4 rfl)
        (sd_step _ _ _ _ (by rw [l2]; exact word_valid 1536 2 16 (by decide) (by decide))) rfl,
      ordinary_one _ L3 (.LD .x31 .x23 192) _ (ck_fetch _ 10586 _ (by decide) q5 rfl)
        (ld_step _ _ _ _ (by rw [a2]; exact word_valid 1536 24 192 (by decide) (by decide))) rfl,
      ordinary_one _ (ev7 s src r q z y) (.SD .x23 .x31 24) _ (ck_fetch _ 10587 _ (by decide) q6 rfl)
        (sd_step _ _ _ _ (by rw [l3]; exact word_valid 1536 3 24 (by decide) (by decide))) rfl]
    simp only [bind_assoc, pure_bind, charge_charge]
  have p7 := (ev7_facts s src proof index ready even r q z y).2.1
  have jump : ordinaryStep (ev7 s src r q z y) (.base (.JAL .x0 2055032)) = some (ev8 s src r q z y) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, ev8, MachineState.setReg,
      MachineState.setPC, p7]
    rfl
  rw [run8, ordinary_one _ (ev8 s src r q z y) _ _ (ck_fetch _ 10588 _ (by decide) p7 rfl) jump rfl]
  simp only [bind_assoc, pure_bind, charge_charge]

/-! ### Odd path: states -/

def odOps1 : List Instr := [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x10 .x19 40, .ADDI .x12 .x10 0]

/-- Entry of the odd path (word 10589). -/
def od0 (s : MachineState) : MachineState := (ckHead s).setPC (ckPC 10589)

def od1 (s : MachineState) : MachineState := odOps1.foldl execInstrBr (od0 s)

def od2 (s : MachineState) (src : Nat) (q : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (writeBits (od1 s) (wordAddress (src + 5)) q) (.ADDI .x10 .x10 192))
    (.ADDI .x12 .x10 3936)

def od3 (s : MachineState) (src : Nat) (q r : BitVec 256) : MachineState :=
  execInstrBr (writeBits (od2 s src q) (wordAddress (src + 9)) r) (.ADDI .x10 .x10 3904)

def od4pre (s : MachineState) (src : Nat) (q r z : BitVec 256) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (writeBits (od3 s src q r) (wordAddress (src + 9)) z)
    (.SLLI .x28 .x6 8)) (.ADD .x28 .x3 .x28)) (.ADDI .x31 .x28 40)

def od4 (s : MachineState) (src : Nat) (q r z : BitVec 256) : MachineState :=
  execInstrBr (od4pre s src q r z) (.SD .x10 .x31 16)

def od5 (s : MachineState) (src : Nat) (q r z : BitVec 256) : MachineState :=
  copyField oddSaltCode (od4 s src q r z)

def odOps6 : List Instr := [.ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x12 .x23 0]

def od6 (s : MachineState) (src : Nat) (q r z : BitVec 256) : MachineState :=
  odOps6.foldl execInstrBr (od5 s src q r z)

/-- After the permutation reply at 1536 and `jal zero,<58>`. -/
def od7 (s : MachineState) (src : Nat) (q r z : BitVec 256) (y : Block) : MachineState :=
  (writeBits (od6 s src q r z) (wordAddress 1536) y).setPC (ckPC 58)

/-! ### Odd path: registers and memory -/

theorem od0_facts (s : MachineState) :
    (od0 s).mem = s.mem ∧ (od0 s).getReg .x6 = s.getMem (s.getReg .x8) ∧ (od0 s).pc = ckPC 10589 ∧
    ∀ r, r ≠ .x6 → r ≠ .x7 → (od0 s).getReg r = s.getReg r := by
  obtain ⟨m, h6, _, _, keep⟩ := ck_head_facts s
  refine ⟨?_, ?_, rfl, fun r a b => ?_⟩
  · simpa [od0] using m
  · simpa [od0] using h6
  · simpa [od0] using keep r a b

theorem od1_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index) :
    (od1 s).getReg .x10 = wordAddress (src + 5) ∧ (od1 s).getReg .x12 = wordAddress (src + 5) ∧
    (od1 s).getReg .x11 = 64 ∧ (od1 s).getReg .x13 = 0 ∧ (od1 s).pc = ckPC 10593 ∧ (od1 s).mem = s.mem ∧
    (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → (od1 s).getReg r = (od0 s).getReg r) := by
  obtain ⟨m0, _, p0, k0⟩ := od0_facts s
  have x19 : (od0 s).getReg .x19 = wordAddress src := (k0 .x19 (by decide) (by decide)).trans ready.source
  have prev : (execInstrBr (execInstrBr (execInstrBr (od0 s) (.ADDI .x11 .x0 64)) (.ADDI .x13 .x0 0))
      (.ADDI .x10 .x19 40)).getReg .x10 = wordAddress (src + 5) := by
    rw [addi_from _ .x10 .x19 40 (by decide), addi_other _ .x13 .x0 .x19 0 (by decide),
      addi_other _ .x11 .x0 .x19 64 (by decide), x19, imm_up src 5 40 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [od1, odOps1, List.foldl]
    rw [addi_other _ .x12 .x10 .x10 0 (by decide), prev]
  · simp only [od1, odOps1, List.foldl]
    rw [addi_from _ .x12 .x10 0 (by decide), prev, imm_up (src + 5) 0 0 (by decide)]
  · simp only [od1, odOps1, List.foldl]
    rw [addi_other _ .x12 .x10 .x11 0 (by decide), addi_other _ .x10 .x19 .x11 40 (by decide),
      addi_other _ .x13 .x0 .x11 0 (by decide), addi_from _ .x11 .x0 64 (by decide)]
    rfl
  · simp only [od1, odOps1, List.foldl]
    rw [addi_other _ .x12 .x10 .x13 0 (by decide), addi_other _ .x10 .x19 .x13 40 (by decide),
      addi_from _ .x13 .x0 0 (by decide)]
    rfl
  · simp only [od1, odOps1, List.foldl]
    rw [addi_pc, addi_pc, addi_pc, addi_pc, p0]
    rfl
  · simp only [od1, odOps1, List.foldl]
    rw [addi_mem, addi_mem, addi_mem, addi_mem, m0]
  · intro r a b c d
    simp only [od1, odOps1, List.foldl]
    rw [addi_other _ _ _ _ _ c, addi_other _ _ _ _ _ a, addi_other _ _ _ _ _ d, addi_other _ _ _ _ _ b]

theorem od1_keeps (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (g : Reg) (a : g ≠ .x6) (b : g ≠ .x7) (c : g ≠ .x10) (d : g ≠ .x11) (e : g ≠ .x12) (f : g ≠ .x13) :
    (od1 s).getReg g = s.getReg g :=
  ((od1_facts s src proof index ready).2.2.2.2.2.2 g c d e f).trans ((od0_facts s).2.2.2 g a b)

theorem od2_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (q : BitVec 256) :
    (od2 s src q).getReg .x10 = wordAddress (src + 29) ∧ (od2 s src q).getReg .x12 = wordAddress (src + 9) ∧
    (od2 s src q).pc = ckPC 10596 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → (od2 s src q).getReg g = (od1 s).getReg g) := by
  obtain ⟨a10, _, _, _, p1, _, _⟩ := od1_facts s src proof index ready
  let w := writeBits (od1 s) (wordAddress (src + 5)) q
  have wx : w.getReg .x10 = wordAddress (src + 5) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans a10
  have up : (execInstrBr w (.ADDI .x10 .x10 192)).getReg .x10 = wordAddress (src + 29) := by
    rw [addi_self w .x10 192 (by decide), wx, imm_up (src + 5) 24 192 (by decide)]
  refine ⟨(addi_other _ .x12 .x10 .x10 3936 (by decide)).trans up, ?_, ?_, ?_⟩
  · rw [od2, addi_from _ _ _ _ (by decide), up, imm_down 20 3936 (by decide) (src + 29) (by omega),
      show src + 29 - 20 = src + 9 by omega]
  · rw [od2, addi_pc, addi_pc, ck_written_pc, p1]
    rfl
  · intro g a b
    rw [od2, addi_other _ _ _ _ _ b, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register]

theorem od3_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (q r : BitVec 256) :
    (od3 s src q r).getReg .x10 = wordAddress (src + 5) ∧ (od3 s src q r).getReg .x12 = wordAddress (src + 9) ∧
    (od3 s src q r).pc = ckPC 10598 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → (od3 s src q r).getReg g = (od1 s).getReg g) := by
  obtain ⟨b10, b12, bpc, bkeep⟩ := od2_facts s src proof index ready q
  let w := writeBits (od2 s src q) (wordAddress (src + 9)) r
  have wx : w.getReg .x10 = wordAddress (src + 29) := (CommitGolfCandidate.writeBits_register _ _ _ _).trans b10
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [od3, addi_self w .x10 3904 (by decide), wx, imm_down 24 3904 (by decide) (src + 29) (by omega),
      show src + 29 - 24 = src + 5 by omega]
  · rw [od3, addi_other _ _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, b12]
  · rw [od3, addi_pc, ck_written_pc, bpc]
    rfl
  · intro g a b
    rw [od3, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register, bkeep g a b]

theorem od4pre_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) :
    (od4pre s src q r z).getReg .x10 = wordAddress (src + 5) ∧
    (od4pre s src q r z).getReg .x31 = c3pTag index ∧
    (od4pre s src q r z).pc = ckPC 10602 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → g ≠ .x28 → g ≠ .x31 → (od4pre s src q r z).getReg g = (od1 s).getReg g) := by
  obtain ⟨c10, _, cpc, ckeep⟩ := od3_facts s src proof index ready q r
  obtain ⟨_, h6, _, k0⟩ := od0_facts s
  obtain ⟨_, _, _, _, _, _, k1⟩ := od1_facts s src proof index ready
  let w := writeBits (od3 s src q r) (wordAddress (src + 9)) z
  have w6 : w.getReg .x6 = BitVec.ofNat 64 index.val := by
    rw [CommitGolfCandidate.writeBits_register, ckeep _ (by decide) (by decide),
      k1 _ (by decide) (by decide) (by decide) (by decide), h6, ready.indexValue]
  have w3 : w.getReg .x3 = 4056 := by
    rw [CommitGolfCandidate.writeBits_register, ckeep _ (by decide) (by decide),
      k1 _ (by decide) (by decide) (by decide) (by decide), k0 _ (by decide) (by decide), ready.tagBase]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [od4pre, addi_other _ _ _ _ _ (by decide), tag_keep _ _ (by decide),
      CommitGolfCandidate.writeBits_register, c10]
  · rw [od4pre, addi_from _ _ _ _ (by decide), tag_base w index.val w6 w3, odd_tag_value index odd]
  · rw [od4pre, addi_pc, tag_pc, ck_written_pc, cpc]
    rfl
  · intro g a b c d
    rw [od4pre, addi_other _ _ _ _ _ d, tag_keep _ _ c, CommitGolfCandidate.writeBits_register,
      ckeep g a b]

theorem od2_view (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (q : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (od2 s src q) w = writeWindow (memoryView s) (src + 5) (digestWords q) w := by
  have room := ready.sourceBound
  obtain ⟨_, _, _, _, _, m1, _⟩ := od1_facts s src proof index ready
  have same : (od2 s src q).mem = (writeBits (od1 s) (wordAddress (src + 5)) q).mem := by
    rw [od2, addi_mem, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw]
  exact write_window_point _ _ _ _ _ (congrFun (memoryView_congr m1) w)

theorem od3_view (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (q r : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (od3 s src q r) w =
      writeWindow (writeWindow (memoryView s) (src + 5) (digestWords q)) (src + 9) (digestWords r) w := by
  have room := ready.sourceBound
  have same : (od3 s src q r).mem = (writeBits (od2 s src q) (wordAddress (src + 9)) r).mem := by
    rw [od3, addi_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw]
  exact write_window_point _ _ _ _ _ (od2_view s src proof index ready q w hw)

theorem od4pre_view (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (q r z : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (od4pre s src q r z) w =
      writeWindow (writeWindow (writeWindow (memoryView s) (src + 5) (digestWords q)) (src + 9) (digestWords r))
        (src + 9) (digestWords z) w := by
  have room := ready.sourceBound
  have same : (od4pre s src q r z).mem = (writeBits (od3 s src q r) (wordAddress (src + 9)) z).mem := by
    rw [od4pre, addi_mem, tag_mem]
  rw [memoryView_congr same, compression_write_memory _ _ _ _ (by omega) hw]
  exact write_window_point _ _ _ _ _ (od3_view s src proof index ready q r w hw)

/-- Memory of the odd path after the three compressions and the tag store. -/
def oddMem (M : Memory) (src : Nat) (dq dr dz : Words 4) (tag : Word) : Memory :=
  writeWord (writeWindow (writeWindow (writeWindow M (src + 5) dq) (src + 9) dr) (src + 9) dz) (src + 7) tag

theorem od4_memory (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) (w : Nat) (hw : w < 2 ^ 33) :
    memoryView (od4 s src q r z) w =
      oddMem (memoryView s) src (digestWords q) (digestWords r) (digestWords z) (c3pTag index) w := by
  have room := ready.sourceBound
  obtain ⟨p10, p31, _, _⟩ := od4pre_facts s src proof index ready odd q r z
  have same : (od4 s src q r z).mem =
      ((od4pre s src q r z).setMem ((od4pre s src q r z).getReg .x10 + signExtend12 16)
        ((od4pre s src q r z).getReg .x31)).mem := by
    rw [od4, sd_mem]
  rw [memoryView_congr same, p10, p31, imm_up (src + 5) 2 16 (by decide),
    view_store _ (src + 5 + 2) w _ (by omega) (by omega), show src + 5 + 2 = src + 7 by omega]
  exact write_word_point _ _ _ _ _ (od4pre_view s src proof index ready q r z w hw)

theorem odd_mem_outside (M : Memory) (src : Nat) (dq dr dz : Words 4) (tag : Word) (w : Nat)
    (outside : w < src + 5 ∨ src + 13 ≤ w) : oddMem M src dq dr dz tag w = M w := by
  simp only [oddMem, writeWord, writeWindow]
  split_ifs <;> first | omega | rfl

theorem od4_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) :
    (od4 s src q r z).getReg .x10 = wordAddress (src + 5) ∧ (od4 s src q r z).pc = ckPC 10603 ∧
    (∀ g, g ≠ .x10 → g ≠ .x12 → g ≠ .x28 → g ≠ .x31 → (od4 s src q r z).getReg g = (od1 s).getReg g) := by
  obtain ⟨p10, _, ppc, pkeep⟩ := od4pre_facts s src proof index ready odd q r z
  refine ⟨by rw [od4, sd_reg, p10], ?_, fun g a b c d => by rw [od4, sd_reg, pkeep g a b c d]⟩
  rw [od4, sd_pc, ppc]
  rfl

theorem od4_copy_ready (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) :
    CopyReady oddSaltCode (od4 s src q r z) proof (8 * (src + 5)) 0 := by
  obtain ⟨d10, dpc, dkeep⟩ := od4_facts s src proof index ready odd q r z
  have pb := ready.proofBound
  have sb := ready.sourceBound
  refine ⟨?_, ?_, ?_, ?_, ?_, ready.proofAligned, ?_⟩
  · change (od4 s src q r z).pc = ckPC (10603 + 2 * 0)
    exact dpc
  · change (od4 s src q r z).getReg .x21 = _
    rw [dkeep .x21 (by decide) (by decide) (by decide) (by decide),
      od1_keeps s src proof index ready .x21 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), ready.proofPointer]
  · change (od4 s src q r z).getReg .x10 + BitVec.ofNat 64 (8 * 0) = _
    rw [d10, address_up]
    try rfl
  · change proof + 2 * 8 ≤ MEMORY_BYTES; omega
  · change 8 * (src + 5) + 2 * 8 ≤ MEMORY_BYTES; unfold MEMORY_BYTES; omega
  · change 8 * (src + 5) % 2 = 0; omega

theorem od5_pc (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) : (od5 s src q r z).pc = ckPC 10619 :=
  copy_field_pc _ _ _ _ (od4_copy_ready s src proof index ready odd q r z)

theorem od5_reg (s : MachineState) (src : Nat) (q r z : BitVec 256) (g : Reg) (h : g ≠ .x31) :
    (od5 s src q r z).getReg g = (od4 s src q r z).getReg g :=
  copy_field_register _ _ g h

theorem od6_mem (s : MachineState) (src : Nat) (q r z : BitVec 256) :
    (od6 s src q r z).mem = (od5 s src q r z).mem := by
  simp only [od6, odOps6, List.foldl]
  rw [addi_mem, addi_mem, addi_mem]

theorem od6_facts (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) :
    (od6 s src q r z).getReg .x10 = wordAddress (src + 5) ∧
    (od6 s src q r z).getReg .x12 = wordAddress 1536 ∧
    (od6 s src q r z).getReg .x5 = 0 ∧
    (od6 s src q r z).getReg .x11 = 200 ∧
    (od6 s src q r z).getReg .x13 = 1 ∧
    (od6 s src q r z).pc = ckPC 10622 ∧
    (∀ g, g ≠ .x10 → g ≠ .x11 → g ≠ .x12 → g ≠ .x13 → g ≠ .x28 → g ≠ .x31 →
      (od6 s src q r z).getReg g = (od1 s).getReg g) := by
  obtain ⟨d10, _, dkeep⟩ := od4_facts s src proof index ready odd q r z
  have p5 := od5_pc s src proof index ready odd q r z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [od6, odOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x10 0 (by decide), addi_other _ .x13 .x0 .x10 1 (by decide),
      addi_other _ .x11 .x0 .x10 200 (by decide), od5_reg _ _ _ _ _ .x10 (by decide), d10]
  · simp only [od6, odOps6, List.foldl]
    rw [addi_from _ .x12 .x23 0 (by decide), addi_other _ .x13 .x0 .x23 1 (by decide),
      addi_other _ .x11 .x0 .x23 200 (by decide), od5_reg _ _ _ _ _ .x23 (by decide),
      dkeep .x23 (by decide) (by decide) (by decide) (by decide),
      od1_keeps s src proof index ready .x23 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), ready.digest, imm_up 1536 0 0 (by decide)]
  · simp only [od6, odOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x5 0 (by decide), addi_other _ .x13 .x0 .x5 1 (by decide),
      addi_other _ .x11 .x0 .x5 200 (by decide), od5_reg _ _ _ _ _ .x5 (by decide),
      dkeep .x5 (by decide) (by decide) (by decide) (by decide),
      od1_keeps s src proof index ready .x5 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), ready.selector]
  · simp only [od6, odOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x11 0 (by decide), addi_other _ .x13 .x0 .x11 1 (by decide),
      addi_from _ .x11 .x0 200 (by decide)]
    rfl
  · simp only [od6, odOps6, List.foldl]
    rw [addi_other _ .x12 .x23 .x13 0 (by decide), addi_from _ .x13 .x0 1 (by decide)]
    rfl
  · simp only [od6, odOps6, List.foldl]
    rw [addi_pc, addi_pc, addi_pc, p5]
    rfl
  · intro g a b c d e f
    simp only [od6, odOps6, List.foldl]
    rw [addi_other _ _ _ _ _ c, addi_other _ _ _ _ _ d, addi_other _ _ _ _ _ b, od5_reg _ _ _ _ _ _ f,
      dkeep g a c e f]

theorem od4_proof_read (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) :
    readBuffer (od4 s src q r z) proof 16 = readBuffer s proof 16 := by
  have ap := ready.apart
  have pb := ready.proofBound
  apply buffer_byte_frame
  intro j hj
  rw [od4_memory s src proof index ready odd q r z _ (by unfold MEMORY_BYTES at pb; omega),
    odd_mem_outside _ _ _ _ _ _ _ (by omega)]

theorem od_perm_input (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) :
    (window (memoryView (od6 s src q r z)) (src + 5) : Words 25) =
      c3pOddWords index (ckNonce s proof) (window (memoryView s) (src + 5)) (digestWords z) (digestWords q) := by
  have sb := ready.sourceBound
  have ap := ready.apart
  have cr := od4_copy_ready s src proof index ready odd q r z
  funext k
  have kt := k.isLt
  change memoryView (od6 s src q r z) (src + 5 + k.val) = _
  rw [memoryView_congr (od6_mem s src q r z)]
  by_cases salt : k.val < 2
  · have word : memoryView (od5 s src q r z) (src + 5 + k.val) =
        (readBuffer (od4 s src q r z) proof 16).extractLsb' (64 * k.val) 64 :=
      copied_words oddSaltCode (od4 s src q r z) proof (src + 5) cr (by omega) rfl k.val salt
    rw [word, od4_proof_read s src proof index ready odd q r z]
    simp only [c3pOddWords]
    rw [dite_eq_left salt]
    rfl
  · change memoryView (copyField oddSaltCode (od4 s src q r z)) _ = _
    rw [copy_frame oddSaltCode _ proof _ cr (by omega) rfl _ (by omega) (by omega),
      od4_memory s src proof index ready odd q r z _ (by omega)]
    simp only [c3pOddWords]
    rw [dite_eq_right salt]
    by_cases tag : k.val = 2
    · rw [ite_eq_left tag]
      simp only [oddMem, writeWord]
      rw [ite_eq_left (show src + 5 + k.val = src + 7 by omega)]
    · rw [ite_eq_right tag]
      by_cases three : k.val = 3
      · rw [ite_eq_left three]
        simp only [oddMem, writeWord, writeWindow]
        rw [ite_eq_right (show src + 5 + k.val ≠ src + 7 by omega),
          dite_eq_right (show ¬ (src + 9 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 9 + 4) by omega),
          dite_eq_right (show ¬ (src + 9 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 9 + 4) by omega),
          dite_eq_left (show src + 5 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 5 + 4 by omega)]
        congr 1
        ext
        simp only [Fin.val_mk]
        omega
      · rw [ite_eq_right three]
        by_cases mid : k.val < 8
        · rw [dite_eq_left mid]
          simp only [oddMem, writeWord, writeWindow]
          rw [ite_eq_right (show src + 5 + k.val ≠ src + 7 by omega),
            dite_eq_left (show src + 9 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 9 + 4 by omega)]
          congr 1
          ext
          simp only [Fin.val_mk]
          omega
        · rw [dite_eq_right mid, odd_mem_outside _ _ _ _ _ _ _ (by omega)]
          rfl

/-! ### Odd path: execution -/

def odQueries (s : MachineState) (src : Nat) : OracleComp World MachineState := do
  let q ← World.query (.inr (.inl (readBuffer (od1 s) (8 * (src + 5)) 64)))
  let r ← World.query (.inr (.inl (readBuffer (od2 s src q) (8 * (src + 29)) 64)))
  let z ← World.query (.inr (.inl (readBuffer (od3 s src q r) (8 * (src + 5)) 64)))
  let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (od6 s src q r z)) (src + 5))))))
  return od7 s src q r z y

theorem execute_od1 (s : MachineState) (fuel : Nat) :
    execute packedImage (4 + fuel) (od0 s) false =
      (do let result ← execute packedImage fuel (od1 s) false; return result.charge 4 0) := by
  apply execute_unit_steps (states := fun i => (odOps1.take i).foldl execInstrBr (od0 s))
  intro i bounded
  refine ⟨.base (odOps1[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply ck_fetch _ (10589 + i) _ (by omega)
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_od6 (s : MachineState) (src : Nat) (q r z : BitVec 256) (pc : (od5 s src q r z).pc = ckPC 10619)
    (fuel : Nat) :
    execute packedImage (3 + fuel) (od5 s src q r z) false =
      (do let result ← execute packedImage fuel (od6 s src q r z) false; return result.charge 3 0) := by
  apply execute_unit_steps (states := fun i => (odOps6.take i).foldl execInstrBr (od5 s src q r z))
  intro i bounded
  refine ⟨.base (odOps6[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply ck_fetch _ (10619 + i) _ (by omega)
    · interval_cases i <;> simp only [List.take, List.foldl, odOps6, addi_pc, pc] <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem execute_odd (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (fuel : Nat) :
    execute packedImage (35 + fuel) (od0 s) false =
      (do let d ← odQueries s src
          let res ← execute packedImage fuel d false
          return res.charge 85 4) := by
  have sb := ready.sourceBound
  obtain ⟨a10, a12, a11, a13, p1, _, k1⟩ := od1_facts s src proof index ready
  have sel1 : (od1 s).getReg .x5 = 0 :=
    (k1 .x5 (by decide) (by decide) (by decide) (by decide)).trans
      (((od0_facts s).2.2.2 .x5 (by decide) (by decide)).trans ready.selector)
  rw [show 35 + fuel = 4 + ((30 + fuel) + 1) by omega, execute_od1 s,
    execute_compression_on packedImage (30 + fuel) (od1 s) false (src + 5) (src + 5) (by omega) (by omega)
      a10 a12 sel1 a11 a13 (ck_fetch _ 10593 .ECALL (by decide) p1 rfl)]
  simp only [odQueries, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro q _
  have w1pc : (writeBits (od1 s) (wordAddress (src + 5)) q).pc = ckPC 10594 := by
    rw [ck_written_pc, p1]; rfl
  have m1pc : (execInstrBr (writeBits (od1 s) (wordAddress (src + 5)) q) (.ADDI .x10 .x10 192)).pc = ckPC 10595 := by
    rw [addi_pc, w1pc]; rfl
  obtain ⟨b10, b12, bpc, bkeep⟩ := od2_facts s src proof index ready q
  rw [show 30 + fuel = 1 + (1 + ((27 + fuel) + 1)) by omega,
    ordinary_one _ _ (.ADDI .x10 .x10 192) _ (ck_fetch _ 10594 _ (by decide) w1pc rfl) rfl rfl,
    ordinary_one _ (od2 s src q) (.ADDI .x12 .x10 3936) _ (ck_fetch _ 10595 _ (by decide) m1pc rfl) rfl rfl,
    execute_compression_on packedImage (27 + fuel) (od2 s src q) false (src + 29) (src + 9) (by omega) (by omega)
      b10 b12 ((bkeep .x5 (by decide) (by decide)).trans sel1) ((bkeep .x11 (by decide) (by decide)).trans a11)
      ((bkeep .x13 (by decide) (by decide)).trans a13) (ck_fetch _ 10596 .ECALL (by decide) bpc rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro r _
  obtain ⟨c10, c12, cpc, ckeep⟩ := od3_facts s src proof index ready q r
  have w2pc : (writeBits (od2 s src q) (wordAddress (src + 9)) r).pc = ckPC 10597 := by
    rw [ck_written_pc, bpc]; rfl
  rw [show 27 + fuel = 1 + ((25 + fuel) + 1) by omega,
    ordinary_one _ (od3 s src q r) (.ADDI .x10 .x10 3904) _ (ck_fetch _ 10597 _ (by decide) w2pc rfl) rfl rfl,
    execute_compression_on packedImage (25 + fuel) (od3 s src q r) false (src + 5) (src + 9) (by omega) (by omega)
      c10 c12 ((ckeep .x5 (by decide) (by decide)).trans sel1) ((ckeep .x11 (by decide) (by decide)).trans a11)
      ((ckeep .x13 (by decide) (by decide)).trans a13) (ck_fetch _ 10598 .ECALL (by decide) cpc rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro z _
  let w3 := writeBits (od3 s src q r) (wordAddress (src + 9)) z
  have w3pc : w3.pc = ckPC 10599 := by rw [ck_written_pc, cpc]; rfl
  let t1 := execInstrBr w3 (.SLLI .x28 .x6 8)
  let t2 := execInstrBr t1 (.ADD .x28 .x3 .x28)
  have t1pc : t1.pc = ckPC 10600 := by change w3.pc + 4 = _; rw [w3pc]; rfl
  have t2pc : t2.pc = ckPC 10601 := by change t1.pc + 4 = _; rw [t1pc]; rfl
  obtain ⟨p10, _, ppc, _⟩ := od4pre_facts s src proof index ready odd q r z
  have sdValid : accessValid ((od4pre s src q r z).getReg .x10 + signExtend12 16) 8 = true := by
    rw [p10]; exact word_valid (src + 5) 2 16 (by decide) (by omega)
  have copyRun : ∀ X, execute packedImage (16 + X) (od4 s src q r z) false =
      (do let res ← execute packedImage X (od5 s src q r z) false; return res.charge 16 0) := fun X =>
    copy_field_execute oddSaltCode _ _ _ (od4_copy_ready s src proof index ready odd q r z) X false
  have p5 := od5_pc s src proof index ready odd q r z
  obtain ⟨e10, e12, e5, e11, e13, e6pc, _⟩ := od6_facts s src proof index ready odd q r z
  rw [show 25 + fuel = 1 + (1 + (1 + (1 + (16 + (3 + ((1 + fuel) + 1)))))) by omega,
    ordinary_one _ t1 (.SLLI .x28 .x6 8) _ (ck_fetch _ 10599 _ (by decide) w3pc rfl) rfl rfl,
    ordinary_one _ t2 (.ADD .x28 .x3 .x28) _ (ck_fetch _ 10600 _ (by decide) t1pc rfl) rfl rfl,
    ordinary_one _ (od4pre s src q r z) (.ADDI .x31 .x28 40) _ (ck_fetch _ 10601 _ (by decide) t2pc rfl) rfl rfl,
    ordinary_one _ (od4 s src q r z) (.SD .x10 .x31 16) _ (ck_fetch _ 10602 _ (by decide) ppc rfl)
      (sd_step _ _ _ _ sdValid) rfl,
    copyRun, execute_od6 s src q r z p5,
    execute_permutation_call packedImage (1 + fuel) (od6 s src q r z) false (src + 5) 1536 (by omega)
      (by decide) e10 e12 e5 e11 e13 (ck_fetch _ 10622 .ECALL (by decide) e6pc rfl)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro y _
  have ypc : (writeBits (od6 s src q r z) (wordAddress 1536) y).pc = ckPC 10623 := by
    rw [ck_written_pc, e6pc]; rfl
  have jump : ordinaryStep (writeBits (od6 s src q r z) (wordAddress 1536) y) (.base (.JAL .x0 2054892)) =
      some (od7 s src q r z y) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, od7, MachineState.setReg,
      MachineState.setPC, ypc]
    rfl
  rw [ordinary_one _ (od7 s src q r z y) _ _ (ck_fetch _ 10623 _ (by decide) ypc rfl) jump rfl]
  simp only [bind_assoc, pure_bind, charge_charge]

/-! ### The head and the whole leaf block -/

def c3pSteps (index : Index) : Nat := if c3pEven index then 48 else 39
def c3pCycles (index : Index) : Nat := if c3pEven index then 98 else 89

def c3pCheckQueries (s : MachineState) (src : Nat) (index : Index) : OracleComp World MachineState :=
  if c3pEven index then evQueries s src else odQueries s src

theorem execute_head (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (fuel : Nat) :
    execute packedImage (4 + fuel) s false =
      (do let res ← execute packedImage fuel (if c3pEven index then ev0 s else od0 s) false
          return res.charge 4 0) := by
  let j := s.setPC (ckPC 10542)
  let l := execInstrBr j (.LD .x6 .x8 0)
  have jstep : ordinaryStep s (.base (.JAL .x0 42080)) = some j := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, j, MachineState.setReg,
      MachineState.setPC, ready.pc]
    rfl
  have lvalid : accessValid (j.getReg .x8 + signExtend12 0) 8 = true := by
    rw [show j.getReg .x8 = s.getReg .x8 from rfl, show signExtend12 (0 : BitVec 12) = 0#64 by decide,
      BitVec.add_zero]
    exact ready.indexAccess
  have lpc : l.pc = ckPC 10543 := rfl
  have hpc : (ckHead s).pc = ckPC 10544 := (ck_head_facts s).2.2.2.1
  have parity : (ckHead s).getReg .x7 = BitVec.ofNat 64 (index.val % 2) := by
    rw [(ck_head_facts s).2.2.1, ready.indexValue, parity_word _ (by have := index.isLt; change index.val < 16777216 at this; omega)]
  have branch : ordinaryStep (ckHead s) (.base (.BNE .x7 .x0 180)) =
      some (if c3pEven index then ev0 s else od0 s) := by
    by_cases even : c3pEven index
    · have zero : index.val % 2 = 0 := even
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, parity, zero, even, ev0, hpc]
      rfl
    · have one : index.val % 2 = 1 := by unfold c3pEven at even; omega
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, parity, one, even, od0, hpc,
        signExtend13]
      rfl
  rw [show 4 + fuel = 1 + (1 + (1 + (1 + fuel))) by omega,
    ordinary_one s j _ _ (fetch_at _ 22 _ (by decide) (by rw [ready.pc]; rfl) rfl) jstep rfl,
    ordinary_one j l _ _ (ck_fetch _ 10542 _ (by decide) rfl rfl) (ld_step _ _ _ _ lvalid) rfl,
    ordinary_one l (ckHead s) (.ANDI .x7 .x6 1) _ (ck_fetch _ 10543 _ (by decide) lpc rfl) rfl rfl,
    ordinary_one _ _ _ _ (ck_fetch _ 10544 _ (by decide) hpc rfl) branch rfl]
  simp only [bind_assoc, pure_bind, charge_charge]

theorem execute_c3p_leaf (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (fuel : Nat) :
    execute packedImage (c3pSteps index + fuel) s false =
      (do let d ← c3pCheckQueries s src index
          let res ← execute packedImage fuel d false
          return res.charge (c3pCycles index) 4) := by
  by_cases even : c3pEven index
  · simp only [c3pSteps, c3pCycles, c3pCheckQueries, if_pos even]
    rw [show 48 + fuel = 4 + (44 + fuel) by omega, execute_head s src proof index ready, if_pos even,
      execute_even s src proof index ready even]
    simp only [bind_assoc, pure_bind, charge_charge]
  · simp only [c3pSteps, c3pCycles, c3pCheckQueries, if_neg even]
    rw [show 39 + fuel = 4 + (35 + fuel) by omega, execute_head s src proof index ready, if_neg even,
      execute_odd s src proof index ready even]
    simp only [bind_assoc, pure_bind, charge_charge]

/-! ### Query inputs -/

theorem ev_q1 (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index) :
    readBuffer (ev1 s) (8 * (src + 29)) 64 = c3pRInput (window (memoryView s) (src + 5)) := by
  rw [c3_read_compression, memoryView_congr (ev1_facts s src proof index ready).2.2.2.2.2.1]
  unfold c3pRInput
  congr 1
  funext k
  simp only [window, c3pRWords]
  congr 1
  omega

theorem ev_q2 (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (r : BitVec 256) :
    readBuffer (ev2 s src r) (8 * (src + 5)) 64 = c3pQInput (window (memoryView s) (src + 5)) := by
  have sb := ready.sourceBound
  rw [c3_read_compression]
  unfold c3pQInput
  congr 1
  funext k
  have kt := k.isLt
  change memoryView (ev2 s src r) (src + 5 + k.val) = memoryView s (src + 5 + k.val)
  rw [ev2_view s src proof index ready r _ (by omega)]
  simp only [writeWindow]
  rw [dite_eq_right (show ¬ (src + 33 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 33 + 4) by omega)]

theorem ev_q3 (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (r q : BitVec 256) :
    readBuffer (ev3 s src r q) (8 * (src + 29)) 64 = packWords8 (c3pZWords (digestWords q) (digestWords r)) := by
  have sb := ready.sourceBound
  rw [c3_read_compression]
  congr 1
  funext k
  have kt := k.isLt
  change memoryView (ev3 s src r q) (src + 29 + k.val) = _
  rw [ev3_view s src proof index ready r q _ (by omega)]
  simp only [writeWindow, c3pZWords]
  by_cases low : k.val < 4
  · rw [dite_eq_left (show src + 29 ≤ src + 29 + k.val ∧ src + 29 + k.val < src + 29 + 4 by omega),
      dite_eq_left low]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega
  · rw [dite_eq_right (show ¬ (src + 29 ≤ src + 29 + k.val ∧ src + 29 + k.val < src + 29 + 4) by omega),
      dite_eq_left (show src + 33 ≤ src + 29 + k.val ∧ src + 29 + k.val < src + 33 + 4 by omega),
      dite_eq_right low]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega

theorem od_q1 (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index) :
    readBuffer (od1 s) (8 * (src + 5)) 64 = c3pQInput (window (memoryView s) (src + 5)) := by
  rw [c3_read_compression, memoryView_congr (od1_facts s src proof index ready).2.2.2.2.2.1]
  rfl

theorem od_q2 (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (q : BitVec 256) :
    readBuffer (od2 s src q) (8 * (src + 29)) 64 = c3pRInput (window (memoryView s) (src + 5)) := by
  have sb := ready.sourceBound
  rw [c3_read_compression]
  unfold c3pRInput
  congr 1
  funext k
  have kt := k.isLt
  change memoryView (od2 s src q) (src + 29 + k.val) = memoryView s (src + 5 + (24 + k.val))
  rw [od2_view s src proof index ready q _ (by omega)]
  simp only [writeWindow]
  rw [dite_eq_right (show ¬ (src + 5 ≤ src + 29 + k.val ∧ src + 29 + k.val < src + 5 + 4) by omega)]
  congr 1
  omega

theorem od_q3 (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (q r : BitVec 256) :
    readBuffer (od3 s src q r) (8 * (src + 5)) 64 = packWords8 (c3pZWords (digestWords q) (digestWords r)) := by
  have sb := ready.sourceBound
  rw [c3_read_compression]
  congr 1
  funext k
  have kt := k.isLt
  change memoryView (od3 s src q r) (src + 5 + k.val) = _
  rw [od3_view s src proof index ready q r _ (by omega)]
  simp only [writeWindow, c3pZWords]
  by_cases low : k.val < 4
  · rw [dite_eq_right (show ¬ (src + 9 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 9 + 4) by omega),
      dite_eq_left (show src + 5 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 5 + 4 by omega),
      dite_eq_left low]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega
  · rw [dite_eq_left (show src + 9 ≤ src + 5 + k.val ∧ src + 5 + k.val < src + 9 + 4 by omega),
      dite_eq_right low]
    congr 1
    ext
    simp only [Fin.val_mk]
    omega

/-! ### Final states -/

/-- What the record loop needs of the state after either path: pc at the lower setup, the index
in `x6`, the record registers kept, writes only to the value and the reply scratch, the digest. -/
structure C3PFinal (s : MachineState) (src : Nat) (index : Index) (t : MachineState) (y : Block) : Prop where
  pc : t.pc = ckPC 58
  position : t.getReg .x6 = BitVec.ofNat 64 index.val
  kept : ∀ g, g ≠ .x6 → g ≠ .x7 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 → g ≠ .x13 → g ≠ .x28 → g ≠ .x31 →
    t.getReg g = s.getReg g
  frame : ∀ w < 2 ^ 33, (w < src ∨ src + 37 ≤ w) → (w < 1534 ∨ 1576 ≤ w) → memoryView t w = memoryView s w
  digest : readBuffer t 12288 32 = c3pDigestWindow index y

theorem ev6_keep (s : MachineState) (src : Nat) (r q z : BitVec 256) (g : Reg) (a : g ≠ .x10) (b : g ≠ .x11)
    (c : g ≠ .x12) (d : g ≠ .x13) : (ev6 s src r q z).getReg g = (ev5 s src r q z).getReg g := by
  simp only [ev6, evOps6, List.foldl]
  rw [addi_other _ _ _ _ _ c, addi_other _ _ _ _ _ a, addi_other _ _ _ _ _ d, addi_other _ _ _ _ _ b]

theorem ev8_final (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (even : c3pEven index) (r q z : BitVec 256) (y : Block) :
    C3PFinal s src index (ev8 s src r q z y) y := by
  have sb := ready.sourceBound
  have sl := ready.sourceLow
  obtain ⟨view7, _, keep7⟩ := ev7_facts s src proof index ready even r q z y
  obtain ⟨_, _, keep4⟩ := ev4_facts s src proof index ready even r q z
  obtain ⟨_, _, _, _, _, _, keep1⟩ := ev1_facts s src proof index ready
  have chain (g : Reg) (h6 : g ≠ .x31) (h10 : g ≠ .x10) (h11 : g ≠ .x11) (h12 : g ≠ .x12) (h13 : g ≠ .x13)
      (h28 : g ≠ .x28) : (ev8 s src r q z y).getReg g = (ev1 s).getReg g := by
    change ((ev7 s src r q z y).setPC (ckPC 58)).getReg g = _
    rw [MachineState.getReg_setPC, keep7 g h6, ev6_keep _ _ _ _ _ g h10 h11 h12 h13, ev5_reg _ _ _ _ _ g h6,
      keep4 g h10 h12 h28 h6]
  refine ⟨rfl, ?_, fun g a b c d e f h i => ?_, fun w bound inputOutside scratchOutside => ?_, ?_⟩
  · rw [chain .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep1 .x6 (by decide) (by decide) (by decide) (by decide), (ev0_facts s).2.1, ready.indexValue]
  · rw [chain g i c d e f h, ev1_keeps s src proof index ready g a b c d e f]
  · change memoryView ((ev7 s src r q z y).setPC (ckPC 58)) w = _
    rw [memoryView_congr (mem_set_pc _ _), view7 w bound, if_neg (by omega)]
    refine (permutation_write_memory _ 1536 w y (by decide) bound).trans ?_
    rw [writeWindow, dite_eq_right (show ¬ (1536 ≤ w ∧ w < 1536 + 25) by omega),
      memoryView_congr (ev6_mem s src r q z)]
    change memoryView (copyField evenSaltCode (ev4 s src r q z)) w = _
    rw [copy_frame evenSaltCode _ proof _ (ev4_copy_ready s src proof index ready even r q z) (by
        have := ready.apart; omega) rfl w bound (by omega),
      ev4_memory s src proof index ready even r q z w bound, even_mem_outside _ _ _ _ _ _ _ (by omega)]
  · rw [ev8_digest s src proof index ready even r q z y, c3pDigestWindow, if_pos even]

theorem od6_keep (s : MachineState) (src : Nat) (q r z : BitVec 256) (g : Reg) (b : g ≠ .x11)
    (c : g ≠ .x12) (d : g ≠ .x13) : (od6 s src q r z).getReg g = (od5 s src q r z).getReg g := by
  simp only [od6, odOps6, List.foldl]
  rw [addi_other _ _ _ _ _ c, addi_other _ _ _ _ _ d, addi_other _ _ _ _ _ b]

theorem od7_final (s : MachineState) (src proof : Nat) (index : Index) (ready : CkReady s src proof index)
    (odd : ¬ c3pEven index) (q r z : BitVec 256) (y : Block) :
    C3PFinal s src index (od7 s src q r z y) y := by
  have sb := ready.sourceBound
  have sl := ready.sourceLow
  obtain ⟨_, _, keep4⟩ := od4_facts s src proof index ready odd q r z
  obtain ⟨_, _, _, _, _, _, keep1⟩ := od1_facts s src proof index ready
  have chain (g : Reg) (h6 : g ≠ .x31) (h10 : g ≠ .x10) (h11 : g ≠ .x11) (h12 : g ≠ .x12) (h13 : g ≠ .x13)
      (h28 : g ≠ .x28) : (od7 s src q r z y).getReg g = (od1 s).getReg g := by
    change ((writeBits (od6 s src q r z) (wordAddress 1536) y).setPC (ckPC 58)).getReg g = _
    rw [MachineState.getReg_setPC, CommitGolfCandidate.writeBits_register, od6_keep _ _ _ _ _ g h11 h12 h13,
      od5_reg _ _ _ _ _ g h6, keep4 g h10 h12 h28 h6]
  refine ⟨rfl, ?_, fun g a b c d e f h i => ?_, fun w bound inputOutside scratchOutside => ?_, ?_⟩
  · rw [chain .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep1 .x6 (by decide) (by decide) (by decide) (by decide), (od0_facts s).2.1, ready.indexValue]
  · rw [chain g i c d e f h, od1_keeps s src proof index ready g a b c d e f]
  · change memoryView ((writeBits (od6 s src q r z) (wordAddress 1536) y).setPC (ckPC 58)) w = _
    rw [memoryView_congr (mem_set_pc _ _)]
    refine (permutation_write_memory _ 1536 w y (by decide) bound).trans ?_
    rw [writeWindow, dite_eq_right (show ¬ (1536 ≤ w ∧ w < 1536 + 25) by omega),
      memoryView_congr (od6_mem s src q r z)]
    change memoryView (copyField oddSaltCode (od4 s src q r z)) w = _
    rw [copy_frame oddSaltCode _ proof _ (od4_copy_ready s src proof index ready odd q r z) (by
        have := ready.apart; omega) rfl w bound (by omega),
      od4_memory s src proof index ready odd q r z w bound, odd_mem_outside _ _ _ _ _ _ _ (by omega)]
  · rw [c3pDigestWindow, if_neg odd]
    change readBuffer ((writeBits (od6 s src q r z) (wordAddress 1536) y).setPC (ckPC 58)) 12288 32 = _
    rw [read_buffer_memory_congr _ _ (mem_set_pc _ _)]
    exact write_bits_digest (bits := 1600) (od6 s src q r z) 12288 0 y (by decide) (by decide)

/-! ### Rows under a fixed oracle -/

section rows
attribute [local irreducible] execute readBuffer writeBits packBuffer

theorem ev_rows (oracle : Oracle) (s : MachineState) (src : Nat) :
    let q1 := readBuffer (ev1 s) (8 * (src + 29)) 64
    let r := oracle.compression q1
    let q2 := readBuffer (ev2 s src r) (8 * (src + 5)) 64
    let q := oracle.compression q2
    let q3 := readBuffer (ev3 s src r q) (8 * (src + 29)) 64
    let z := oracle.compression q3
    let q4 := packBuffer (window (memoryView (ev6 s src r q z)) (src + 12))
    let y := oracle.permutation q4
    checkEvaluation oracle (recordRows (evQueries s src)) =
      ((ev8 s src r q z y, [.compression q1 r, .compression q2 q, .compression q3 z, .permutation q4 y]), 4) := by
  simp only [evQueries, record_rows_query, check_evaluation_public_bind, check_evaluation_map,
    record_rows_pure, check_evaluation_pure]
  rfl

theorem od_rows (oracle : Oracle) (s : MachineState) (src : Nat) :
    let q1 := readBuffer (od1 s) (8 * (src + 5)) 64
    let q := oracle.compression q1
    let q2 := readBuffer (od2 s src q) (8 * (src + 29)) 64
    let r := oracle.compression q2
    let q3 := readBuffer (od3 s src q r) (8 * (src + 5)) 64
    let z := oracle.compression q3
    let q4 := packBuffer (window (memoryView (od6 s src q r z)) (src + 5))
    let y := oracle.permutation q4
    checkEvaluation oracle (recordRows (odQueries s src)) =
      ((od7 s src q r z y, [.compression q1 q, .compression q2 r, .compression q3 z, .permutation q4 y]), 4) := by
  simp only [odQueries, record_rows_query, check_evaluation_public_bind, check_evaluation_map,
    record_rows_pure, check_evaluation_pure]
  rfl

end rows

/-- The leaf calls under a fixed oracle: the final state and the recorded rows. -/
def c3pRaw (oracle : Oracle) (s : MachineState) (src : Nat) (index : Index) : MachineState × List PublicRow :=
  (checkEvaluation oracle (recordRows (c3pCheckQueries s src index))).1

theorem c3p_calls (oracle : Oracle) (s : MachineState) (src : Nat) (index : Index) :
    (checkEvaluation oracle (recordRows (c3pCheckQueries s src index))).2 = 4 := by
  unfold c3pCheckQueries
  split
  · rw [ev_rows]
  · rw [od_rows]

theorem c3p_raw_spec (oracle : Oracle) (s : MachineState) (src proof : Nat) (index : Index)
    (ready : CkReady s src proof index) (v : Words 32) (hv : window (memoryView s) (src + 5) = v) :
    C3PFinal s src index (c3pRaw oracle s src index).1
        (oracle.permutation (c3pPermInput oracle.compression index (ckNonce s proof) v)) ∧
      C3PLeafRows (c3pRaw oracle s src index).2 oracle.compression oracle.permutation index (ckNonce s proof) v := by
  subst hv
  unfold c3pRaw c3pCheckQueries
  by_cases even : c3pEven index
  · rw [if_pos even]
    have rows := ev_rows oracle s src
    dsimp only at rows
    rw [ev_q1 s src proof index ready] at rows
    generalize hr : oracle.compression (c3pRInput (window (memoryView s) (src + 5))) = r at rows
    rw [ev_q2 s src proof index ready r] at rows
    generalize hq : oracle.compression (c3pQInput (window (memoryView s) (src + 5))) = q at rows
    rw [ev_q3 s src proof index ready r q] at rows
    generalize hz : oracle.compression (packWords8 (c3pZWords (digestWords q) (digestWords r))) = z at rows
    rw [ev_perm_input s src proof index ready even r q z] at rows
    rw [rows]
    subst hr hq hz
    have input : packBuffer (c3pEvenWords index (ckNonce s proof) (window (memoryView s) (src + 5))
        (digestWords (oracle.compression (packWords8 (c3pZWords
          (digestWords (oracle.compression (c3pQInput (window (memoryView s) (src + 5)))))
          (digestWords (oracle.compression (c3pRInput (window (memoryView s) (src + 5)))))))))
        (digestWords (oracle.compression (c3pRInput (window (memoryView s) (src + 5)))))) =
        c3pPermInput oracle.compression index (ckNonce s proof) (window (memoryView s) (src + 5)) := by
      unfold c3pPermInput c3pPermWords
      rw [if_pos even]
      rfl
    rw [input]
    refine ⟨ev8_final s src proof index ready even _ _ _ _, ?_, ?_, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [if_neg even]
    have rows := od_rows oracle s src
    dsimp only at rows
    rw [od_q1 s src proof index ready] at rows
    generalize hq : oracle.compression (c3pQInput (window (memoryView s) (src + 5))) = q at rows
    rw [od_q2 s src proof index ready q] at rows
    generalize hr : oracle.compression (c3pRInput (window (memoryView s) (src + 5))) = r at rows
    rw [od_q3 s src proof index ready q r] at rows
    generalize hz : oracle.compression (packWords8 (c3pZWords (digestWords q) (digestWords r))) = z at rows
    rw [od_perm_input s src proof index ready even q r z] at rows
    rw [rows]
    subst hr hq hz
    have input : packBuffer (c3pOddWords index (ckNonce s proof) (window (memoryView s) (src + 5))
        (digestWords (oracle.compression (packWords8 (c3pZWords
          (digestWords (oracle.compression (c3pQInput (window (memoryView s) (src + 5)))))
          (digestWords (oracle.compression (c3pRInput (window (memoryView s) (src + 5)))))))))
        (digestWords (oracle.compression (c3pQInput (window (memoryView s) (src + 5)))))) =
        c3pPermInput oracle.compression index (ckNonce s proof) (window (memoryView s) (src + 5)) := by
      unfold c3pPermInput c3pPermWords
      rw [if_neg even]
      rfl
    rw [input]
    refine ⟨od7_final s src proof index ready even _ _ _ _, ?_, ?_, ?_, ?_⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ### The record block -/

theorem execute_lower_setup_p (state : MachineState) (pc : state.pc = 0x10e8) (fuel : Nat) :
    execute packedImage (5 + fuel) state false =
      (do let result ← execute packedImage fuel (beginLower state 5) false
          return result.charge 5 0) := by
  apply execute_unit_steps (states := beginLower state)
  intro i bounded
  refine ⟨.base (beginLowerCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (58 + i) _ (by omega)
    · interval_cases i <;> simp [beginLower, beginLowerCode, execInstrBr, MachineState.setPC, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def c3pBlock (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) : RecordBlock :=
  let raw := c3pRaw oracle s (checkSourceWord ordinal) index
  ⟨beginLower raw.1 5, c3pSteps index + 5, c3pCycles index + 5, raw.2⟩

theorem ck_ready_p (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (s : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal s)
    (framed : InputFrame input ordinal s) :
    CkReady s (checkSourceWord ordinal) (checkProofByte ordinal) (honestIndex input.positions ordinal present).val := by
  obtain ⟨aligned, _, _, room, _⟩ := packed_record_geometry input ordinal present fits
  have card := checker_positions_bound input
  have acc := word_access (checkIndexWord ordinal) 0 (by unfold checkIndexWord; omega)
  rw [address_up, Nat.add_zero] at acc
  refine ⟨cursor.pc.trans (ite_eq_right (show ¬ ordinal = input.positions.card by omega)), ?_, ?_, cursor.value,
    cursor.proof, cursor.tag, cursor.digest, cursor.selector, ?_, ?_, aligned, ?_, ?_⟩
  · rw [cursor.index]; exact acc
  · rw [cursor.index]; exact frame_index input ordinal present s framed
  · unfold checkSourceWord; omega
  · unfold checkSourceWord; omega
  · omega
  · unfold checkSourceWord checkProofByte; omega

private theorem saved_ordinary_p (r : Reg) (keep : RecordSaved r) :
    r≠.x6 ∧ r≠.x7 ∧ r≠.x28 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x13 ∧ r≠.x12 ∧ r≠.x31 ∧ r≠.x21 ∧ r≠.x29 := by
  rcases keep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem c3p_exact_run (oracle : Oracle) (ordinal : Nat) (index : Index) (s : MachineState) (proof : Nat)
    (ready : CkReady s (checkSourceWord ordinal) proof index) (fuel : Nat) :
    let out := c3pBlock oracle ordinal index s
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel out.state false))
    checkEvaluation oracle (recordRows (execute packedImage (out.steps + fuel) s false)) =
      ((tail.1.1.charge out.cycles 4, out.rows ++ tail.1.2), 4 + tail.2) := by
  let src := checkSourceWord ordinal
  let raw := c3pRaw oracle s src index
  have pc : raw.1.pc = 0x10e8 := by
    rw [(c3p_raw_spec oracle s src proof index ready _ rfl).1.pc]; rfl
  change checkEvaluation oracle (recordRows (execute packedImage (c3pSteps index + 5 + fuel) s false)) = _
  rw [show c3pSteps index + 5 + fuel = c3pSteps index + (5 + fuel) by omega,
    execute_c3p_leaf s src proof index ready, check_recorded_bind]
  simp only [bind_pure_comp, check_recorded_map]
  erw [execute_lower_setup_p raw.1 pc]
  simp only [bind_pure_comp, check_recorded_map]
  change (let tail := checkEvaluation oracle (recordRows (execute packedImage fuel (beginLower raw.1 5) false))
          ((((tail.1.1.charge 5 0).charge (c3pCycles index) 4), raw.2 ++ tail.1.2),
            (checkEvaluation oracle (recordRows (c3pCheckQueries s src index))).2 + tail.2)) = _
  rw [c3p_calls]
  simp only [charge_charge, Nat.add_zero]
  rfl

theorem c3p_leaf_block : LeafBlockRefines c3pBlock := by
  intro oracle input ordinal present s fits cursor framed
  let item := honestIndex input.positions ordinal present
  let src := checkSourceWord ordinal
  let proof := checkProofByte ordinal
  have ready : CkReady s src proof item.val := ck_ready_p input ordinal present s fits cursor framed
  have values : window (memoryView s) (src + 5) = entryWords (input.values item) :=
    checker_value_data (fun _ => input.values item) item.val (frame_value input ordinal present s framed)
  obtain ⟨fin, rowsOk⟩ := c3p_raw_spec oracle s src proof item.val ready _ values
  let raw := (c3pRaw oracle s src item.val).1
  have params := lower_setup_post raw
  have value (r : Reg) (g6 : r≠.x6) (g7 : r≠.x7) (g28 : r≠.x28) (g10 : r≠.x10) (g11 : r≠.x11)
      (g13 : r≠.x13) (g12 : r≠.x12) (g31 : r≠.x31) : raw.getReg r = s.getReg r :=
    fin.kept r g6 g7 g10 g11 g12 g13 g28 g31
  have finalSaved : LowerSaved s (beginLower raw 5) := by
    intro r safe
    obtain ⟨h6, h7, h28, h10, h11, h13, h12, h31, h21, h29⟩ := saved_ordinary_p r safe
    exact (lower_setup_register raw r h21 h6 h11 h13 h29).trans (value r h6 h7 h28 h10 h11 h13 h12 h31)
  have digest : readBuffer (c3pBlock oracle ordinal item.val s).state 12288 32 =
      c3pLeafDigest oracle.compression oracle.permutation item.val (ckNonce s proof)
        (entryWords (input.values item)) := by
    change readBuffer (beginLower raw 5) 12288 32 = _
    rw [read_buffer_memory_congr _ _ (lower_setup_mem raw), fin.digest]
    rfl
  refine ⟨by change c3pSteps _ + 5 ≤ 53; unfold c3pSteps; split <;> decide,
    c3p_exact_run oracle ordinal item.val s proof ready, ?_, finalSaved, ?_, ?_, ?_⟩
  · change LowerCursor ordinal item.val 0 (beginLower raw 5)
    refine ⟨?_, ?_, ?_, params.2.2.2.2.1, (finalSaved .x23 (by decide)).trans cursor.digest,
      (finalSaved .x24 (by decide)).trans cursor.pair, (finalSaved .x5 (by decide)).trans cursor.selector,
      params.2.2.1, params.2.2.2.1, (finalSaved .x20 (by decide)).trans cursor.challengeLength⟩
    · change (beginLower raw 5).pc = 4348
      rw [params.2.2.2.2.2, fin.pc]
      rfl
    · rw [params.2.1, fin.position,
        value .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        cursor.challengeLength, ← BitVec.ofNat_add]
      simp only [Opening.lowerNode, Nat.pow_zero, Nat.div_one, Nat.add_comm]
    · rw [params.1, value .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), cursor.proof]
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 16 = BitVec.ofNat 64 (_ + 16)
      rw [← BitVec.ofNat_add]
  · intro w bound inputOutside scratchOutside
    change memoryView (beginLower raw 5) w = _
    rw [memoryView_congr (lower_setup_mem raw)]
    exact fin.frame w bound inputOutside scratchOutside
  · exact ⟨⟨ckNonce s proof, rowsOk, digest.symm⟩⟩
  · intro message salts canonical
    rw [digest]
    have loaded : InputFrame (honestCheckInput oracle message input.positions salts) ordinal s :=
      Eq.mp (congrArg (fun data => InputFrame data ordinal s) canonical) framed
    have salt := packed_record_nonce oracle message input.positions salts ordinal present s loaded
    have nonce : ckNonce s proof = saltWords (salts item.val) := by
      funext i
      change (readBuffer s (checkProofByte ordinal) 16).extractLsb' (64 * i.val) 64 = _
      rw [salt]
      rfl
    have entry : input.values item = message item.val := by
      let lookup (record : CheckInput) : Entry :=
        if h : item.val ∈ record.positions then record.values ⟨item.val, h⟩ else 0
      have transported := congrArg lookup canonical
      have inside : item.val ∈ (honestCheckInput oracle message input.positions salts).positions := item.property
      dsimp only [lookup] at transported
      rw [dite_eq_left item.property, dite_eq_left inside] at transported
      exact transported
    rw [nonce, entry]
    rfl

end TwoPermutationPrototype.Packed.C3PRecordLeaf
