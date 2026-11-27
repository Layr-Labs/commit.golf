import CommitGolfCandidate.C3CommitPass1

/-! # Pass 3 of the 3c1p commit loop: one permutation call per leaf

With `a0 = B` (the leaf's message address, word `base`):
`sd a0,144(a0)` (the tag `B`), `ld t6,X(s6) ; sd t6,152(a0) ; ld t6,X+8(s6) ; sd t6,160(a0)` (the
salt, from the leader's signed nonce window), then `addi a2,s4,D` with signed offset `D = 32 * ((j + 64) % 128) - 2048`.
The `ecall` permutes the 200 bytes at `B`, writes the reply at the leaf's heap slot, and is followed by `addi a0,a0,256`. 37 cycles, 1 call. -/
namespace TwoPermutationPrototype.RV64.C3Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option autoImplicit false

def p3Prefix (j : Nat) : List Instr := (p3Ops j).take 6

private theorem nonce_offsets_table : ∀ slot : Fin 256,
    signExtend12 (BitVec.ofNat 12 (16 * slot.val + 2048)) = BitVec.ofNat 64 (16 * slot.val) - 2048 ∧
    signExtend12 (BitVec.ofNat 12 (16 * slot.val + 2056)) = BitVec.ofNat 64 (16 * slot.val + 8) - 2048 := by
  decide

theorem c3_nonce_load_addresses (base : Word) (j : Nat) :
    base + signExtend12 (BitVec.ofNat 12 (16 * (j % 256) + 2048)) =
      (base - 2048) + BitVec.ofNat 64 (16 * (j % 256)) ∧
    base + signExtend12 (BitVec.ofNat 12 (16 * (j % 256) + 2056)) =
      (base - 2048) + BitVec.ofNat 64 (16 * (j % 256) + 8) := by
  have offsets := nonce_offsets_table ⟨j % 256, Nat.mod_lt _ (by decide)⟩
  rw [offsets.1, offsets.2]
  constructor <;> simp only [BitVec.sub_eq_add_neg] <;> ac_rfl

private theorem output_offset_table : ∀ slot : Fin 128,
    signExtend12 (BitVec.ofNat 12 (32 * slot.val)) = BitVec.ofNat 64 (32 * ((slot.val + 64) % 128)) - 2048 := by decide

theorem c3_output_offset (j : Nat) :
    signExtend12 (BitVec.ofNat 12 (32 * (j % 128))) =
      BitVec.ofNat 64 (32 * ((j + 64) % 128)) - 2048 := by
  have h := output_offset_table ⟨j % 128, Nat.mod_lt _ (by decide)⟩
  simpa only [show (j % 128 + 64) % 128 = (j + 64) % 128 by omega] using h

theorem c3_nonce_bias (base : Nat) : wordAddress (base + 256) - 2048 = wordAddress base := by
  change BitVec.ofNat 64 (8 * (base + 256)) - BitVec.ofNat 64 2048 = BitVec.ofNat 64 (8 * base)
  rw [show 8 * (base + 256) = 8 * base + 2048 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-- The precondition of one pass-3 leaf. `base` is the leaf's message word, `dst` its heap slot,
`salts` the first salt word of the current 256-salt window. -/
structure P3Ready (s : MachineState) (j base dst salts : Nat) : Prop where
  source : s.getReg .x10 = wordAddress base
  destination : s.getReg .x20 + (BitVec.ofNat 64 (32 * ((j + 64) % 128)) - 2048) = wordAddress dst
  nonces : s.getReg .x22 = wordAddress (salts + 256)
  sourceBound : base + 32 ≤ 2 ^ 33
  heapBound : dst + 25 ≤ 2 ^ 33
  nonceBound : salts + 512 ≤ 2 ^ 33
  separate : base + 32 ≤ salts
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1

def saltWordOf (salts j : Nat) : Nat := salts + 2 * (j % 256)

theorem salt_addresses (s : MachineState) (j base dst salts : Nat) (ready : P3Ready s j base dst salts) :
    s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (16 * (j % 256) + 2048)) = wordAddress (saltWordOf salts j) ∧
    s.getReg .x22 + signExtend12 (BitVec.ofNat 12 (16 * (j % 256) + 2056)) = wordAddress (saltWordOf salts j + 1) := by
  have offsets := c3_nonce_load_addresses (s.getReg .x22) j
  rw [offsets.1, offsets.2, ready.nonces, c3_nonce_bias]
  unfold saltWordOf wordAddress
  constructor <;> rw [← BitVec.ofNat_add] <;> congr 1 <;> omega

def p3s1 (s : MachineState) : MachineState := execInstrBr s (.SD .x10 .x10 144)
def p3s2 (s : MachineState) (j : Nat) : MachineState :=
  execInstrBr (p3s1 s) (.LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2048)))
def p3s3 (s : MachineState) (j : Nat) : MachineState := execInstrBr (p3s2 s j) (.SD .x10 .x31 152)
def p3s4 (s : MachineState) (j : Nat) : MachineState :=
  execInstrBr (p3s3 s j) (.LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2056)))
def p3s5 (s : MachineState) (j : Nat) : MachineState := execInstrBr (p3s4 s j) (.SD .x10 .x31 160)
def p3Prep (s : MachineState) (j : Nat) : MachineState :=
  execInstrBr (p3s5 s j) (.ADDI .x12 .x20 (BitVec.ofNat 12 (32 * (j % 128))))

/-- The leaf words after the tag and salt stores. -/
def p3Stamp (M : Memory) (base : Nat) (tag n0 n1 : Word) : Memory :=
  writeWord (writeWord (writeWord M (base + 18) tag) (base + 19) n0) (base + 20) n1

private theorem imm144 : signExtend12 (144 : BitVec 12) = BitVec.ofNat 64 (8 * 18) := by decide
private theorem imm152 : signExtend12 (152 : BitVec 12) = BitVec.ofNat 64 (8 * 19) := by decide
private theorem imm160 : signExtend12 (160 : BitVec 12) = BitVec.ofNat 64 (8 * 20) := by decide

theorem p3_prep_facts (s : MachineState) (j base dst salts : Nat) (ready : P3Ready s j base dst salts) :
    (∀ w < 2 ^ 33, memoryView (p3Prep s j) w =
      p3Stamp (memoryView s) base (wordAddress base) (memoryView s (saltWordOf salts j))
        (memoryView s (saltWordOf salts j + 1)) w) ∧
    (p3Prep s j).getReg .x10 = wordAddress base ∧ (p3Prep s j).getReg .x12 = wordAddress dst ∧
    (∀ r, r ≠ .x12 → r ≠ .x31 → (p3Prep s j).getReg r = s.getReg r) ∧
    (p3Prep s j).pc = s.pc + 4 + 4 + 4 + 4 + 4 + 4 := by
  have sb := ready.sourceBound
  have nb := ready.nonceBound
  have sep := ready.separate
  have sw : saltWordOf salts j + 1 < salts + 512 := by unfold saltWordOf; omega
  have sw0 : salts ≤ saltWordOf salts j := by unfold saltWordOf; omega
  obtain ⟨load0, load1⟩ := salt_addresses s j base dst salts ready
  -- registers
  have r1 (r : Reg) : (p3s1 s).getReg r = s.getReg r := sd_reg _ _ _ _ _
  have r2 (r : Reg) (h : r ≠ .x31) : (p3s2 s j).getReg r = s.getReg r := (ld_other _ _ _ _ _ h).trans (r1 r)
  have r3 (r : Reg) (h : r ≠ .x31) : (p3s3 s j).getReg r = s.getReg r := (sd_reg _ _ _ _ _).trans (r2 r h)
  have r4 (r : Reg) (h : r ≠ .x31) : (p3s4 s j).getReg r = s.getReg r := (ld_other _ _ _ _ _ h).trans (r3 r h)
  have r5 (r : Reg) (h : r ≠ .x31) : (p3s5 s j).getReg r = s.getReg r := (sd_reg _ _ _ _ _).trans (r4 r h)
  -- memory, step by step
  have m1 (w : Nat) (hw : w < 2 ^ 33) :
      memoryView (p3s1 s) w = writeWord (memoryView s) (base + 18) (wordAddress base) w := by
    change (p3s1 s).mem _ = _
    rw [p3s1, sd_mem, ready.source, imm144, address_up]
    exact view_store s (base + 18) w (wordAddress base) (by omega) (by omega)
  have v0 : (p3s2 s j).getReg .x31 = memoryView s (saltWordOf salts j) := by
    rw [p3s2, ld_same _ _ _ _ (by decide), r1, load0]
    change memoryView (p3s1 s) _ = _
    rw [m1 _ (by omega)]
    simp only [writeWord, show saltWordOf salts j ≠ base + 18 by omega, ite_false]
  have m2 (w : Nat) (hw : w < 2 ^ 33) :
      memoryView (p3s2 s j) w = writeWord (memoryView s) (base + 18) (wordAddress base) w := by
    change (p3s2 s j).mem _ = _
    rw [p3s2, ld_mem]
    exact m1 w hw
  have m3 (w : Nat) (hw : w < 2 ^ 33) :
      memoryView (p3s3 s j) w = writeWord (writeWord (memoryView s) (base + 18) (wordAddress base)) (base + 19)
        (memoryView s (saltWordOf salts j)) w := by
    change (p3s3 s j).mem _ = _
    rw [p3s3, sd_mem, r2 _ (by decide), ready.source, imm152, address_up, v0]
    change memoryView ((p3s2 s j).setMem (wordAddress (base + 19)) _) w = _
    rw [view_store _ (base + 19) w _ (by omega) (by omega)]
    simp only [writeWord]
    split
    · rfl
    · exact (m2 w hw).trans (by simp only [writeWord])
  have v1 : (p3s4 s j).getReg .x31 = memoryView s (saltWordOf salts j + 1) := by
    rw [p3s4, ld_same _ _ _ _ (by decide), r3 .x22 (by decide), load1]
    change memoryView (p3s3 s j) _ = _
    rw [m3 _ (by omega)]
    simp only [writeWord, show saltWordOf salts j + 1 ≠ base + 19 by omega,
      show saltWordOf salts j + 1 ≠ base + 18 by omega, ite_false]
  have m4 (w : Nat) (hw : w < 2 ^ 33) :
      memoryView (p3s4 s j) w = writeWord (writeWord (memoryView s) (base + 18) (wordAddress base)) (base + 19)
        (memoryView s (saltWordOf salts j)) w := by
    change (p3s4 s j).mem _ = _
    rw [p3s4, ld_mem]
    exact m3 w hw
  have m5 (w : Nat) (hw : w < 2 ^ 33) :
      memoryView (p3s5 s j) w = p3Stamp (memoryView s) base (wordAddress base) (memoryView s (saltWordOf salts j))
        (memoryView s (saltWordOf salts j + 1)) w := by
    change (p3s5 s j).mem _ = _
    rw [p3s5, sd_mem, r4 _ (by decide), ready.source, imm160, address_up, v1]
    change memoryView ((p3s4 s j).setMem (wordAddress (base + 20)) _) w = _
    rw [view_store _ (base + 20) w _ (by omega) (by omega)]
    unfold p3Stamp
    simp only [writeWord]
    split
    · rfl
    · exact (m4 w hw).trans (by simp only [writeWord])
  refine ⟨fun w hw => ?_, ?_, ?_, ?_, ?_⟩
  · change (p3Prep s j).mem _ = _
    rw [p3Prep, addi_mem]
    exact m5 w hw
  · rw [p3Prep, addi_other _ _ _ _ _ (by decide), r5 _ (by decide), ready.source]
  · rw [p3Prep, addi_from _ _ _ _ (by decide), r5 _ (by decide), c3_output_offset, ready.destination]
  · intro r a b
    rw [p3Prep, addi_other _ _ _ _ _ a, r5 _ b]
  · rw [p3Prep, addi_pc, p3s5, sd_pc, p3s4, ld_pc, p3s3, sd_pc, p3s2, ld_pc, p3s1, sd_pc]

/-! ### Execution -/

def p3Final (s : MachineState) (j dst : Nat) (y : BitVec 1600) : MachineState :=
  execInstrBr (writeBits (p3Prep s j) (wordAddress dst) y) (.ADDI .x10 .x10 256)

def p3Trace (s : MachineState) (j base dst : Nat) : OracleComp World MachineState := do
  let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (p3Prep s j)) base)))))
  return p3Final s j dst y

attribute [local irreducible] packedWideCommitImage

private def p3States (s : MachineState) (j : Nat) : Nat → MachineState
  | 0 => s
  | 1 => p3s1 s
  | 2 => p3s2 s j
  | 3 => p3s3 s j
  | 4 => p3s4 s j
  | 5 => p3s5 s j
  | _ => p3Prep s j

theorem execute_p3_leaf (s : MachineState) (j : Nat) (hj : j < 2048) (base dst salts : Nat)
    (ready : P3Ready s j base dst salts) (pc : s.pc = wordPC (p3Index j)) (fuel : Nat) :
    execute packedWideCommitImage (8 + fuel) s true =
      (do let d ← p3Trace s j base dst
          let r ← execute packedWideCommitImage fuel d true
          return r.charge 37 1) := by
  have sb := ready.sourceBound
  have nb := ready.nonceBound
  have hb := ready.heapBound
  have sw : saltWordOf salts j + 1 < salts + 512 := by unfold saltWordOf; omega
  obtain ⟨load0, load1⟩ := salt_addresses s j base dst salts ready
  obtain ⟨_, p10, p12, pkeep, ppc⟩ := p3_prep_facts s j base dst salts ready
  have r1 (r : Reg) : (p3s1 s).getReg r = s.getReg r := sd_reg _ _ _ _ _
  have r2 (r : Reg) (h : r ≠ .x31) : (p3s2 s j).getReg r = s.getReg r := (ld_other _ _ _ _ _ h).trans (r1 r)
  have r3 (r : Reg) (h : r ≠ .x31) : (p3s3 s j).getReg r = s.getReg r := (sd_reg _ _ _ _ _).trans (r2 r h)
  have r4 (r : Reg) (h : r ≠ .x31) : (p3s4 s j).getReg r = s.getReg r := (ld_other _ _ _ _ _ h).trans (r3 r h)
  have pcs (i : Nat) (hi : i < 6) : (p3States s j i).pc = wordPC (p3Index j + i) := by
    interval_cases i
    · simpa [p3States] using pc
    all_goals simp only [p3States, p3s1, p3s2, p3s3, p3s4, p3s5, sd_pc, ld_pc, pc, BitVec.add_assoc]
    all_goals first
      | rw [show (4 : Word) = BitVec.ofNat 64 (4 * 1) by rfl, word_pc_add]
      | rw [show (4 : Word) + 4 = BitVec.ofNat 64 (4 * 2) by rfl, word_pc_add]
      | rw [show (4 : Word) + (4 + 4) = BitVec.ofNat 64 (4 * 3) by rfl, word_pc_add]
      | rw [show (4 : Word) + (4 + (4 + 4)) = BitVec.ofNat 64 (4 * 4) by rfl, word_pc_add]
      | rw [show (4 : Word) + (4 + (4 + (4 + 4))) = BitVec.ofNat 64 (4 * 5) by rfl, word_pc_add]
  have stepPrefix : execute packedWideCommitImage (6 + (2 + fuel)) s true =
      (do let r ← execute packedWideCommitImage (2 + fuel) (p3Prep s j) true; return r.charge 6 0) := by
    have final : p3States s j 6 = p3Prep s j := rfl
    rw [← final]
    apply CommitGolfCandidate.execute_unit_steps (states := p3States s j)
    intro i hi
    refine ⟨.base (opAt (p3Ops j) i), fetch_p3 j hj i (by omega) _ (pcs i hi), ?_, ?_⟩
    · interval_cases i
      · have valid : memoryArgumentsValid s (.SD .x10 .x10 144) = true := by
          change accessValid (s.getReg .x10 + signExtend12 144) 8 = true
          rw [ready.source, imm144]; exact word_access _ _ (by omega)
        show ordinaryStep (s) (.base (.SD .x10 .x10 144)) = some (p3s1 s)
        simp only [ordinaryStep, valid, ↓reduceIte]; rfl
      · have valid : memoryArgumentsValid (p3s1 s) (.LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2048))) = true := by
          change accessValid ((p3s1 s).getReg .x22 + signExtend12 (BitVec.ofNat 12 (16 * (j % 256) + 2048))) 8 = true
          rw [r1, load0, show wordAddress (saltWordOf salts j) = wordAddress (saltWordOf salts j) + BitVec.ofNat 64 (8 * 0)
            by simp]
          exact word_access _ _ (by omega)
        show ordinaryStep (p3s1 s) (.base (.LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2048)))) = some (p3s2 s j)
        simp only [ordinaryStep, valid, ↓reduceIte]; rfl
      · have valid : memoryArgumentsValid (p3s2 s j) (.SD .x10 .x31 152) = true := by
          change accessValid ((p3s2 s j).getReg .x10 + signExtend12 152) 8 = true
          rw [r2 _ (by decide), ready.source, imm152]; exact word_access _ _ (by omega)
        show ordinaryStep (p3s2 s j) (.base (.SD .x10 .x31 152)) = some (p3s3 s j)
        simp only [ordinaryStep, valid, ↓reduceIte]; rfl
      · have valid : memoryArgumentsValid (p3s3 s j) (.LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2056))) = true := by
          change accessValid ((p3s3 s j).getReg .x22 + signExtend12 (BitVec.ofNat 12 (16 * (j % 256) + 2056))) 8 = true
          rw [r3 _ (by decide), load1, show wordAddress (saltWordOf salts j + 1) =
            wordAddress (saltWordOf salts j + 1) + BitVec.ofNat 64 (8 * 0) by simp]
          exact word_access _ _ (by omega)
        show ordinaryStep (p3s3 s j) (.base (.LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2056)))) = some (p3s4 s j)
        simp only [ordinaryStep, valid, ↓reduceIte]; rfl
      · have valid : memoryArgumentsValid (p3s4 s j) (.SD .x10 .x31 160) = true := by
          change accessValid ((p3s4 s j).getReg .x10 + signExtend12 160) 8 = true
          rw [r4 _ (by decide), ready.source, imm160]; exact word_access _ _ (by omega)
        show ordinaryStep (p3s4 s j) (.base (.SD .x10 .x31 160)) = some (p3s5 s j)
        simp only [ordinaryStep, valid, ↓reduceIte]; rfl
      · rfl
    · interval_cases i <;> rfl
  rw [show 8 + fuel = 6 + (2 + fuel) by omega, stepPrefix]
  have fetchCall : fetch packedWideCommitImage (p3Prep s j) = some (.base .ECALL) := by
    have := fetch_p3 j hj 6 (by decide) (p3Prep s j) (by
      rw [ppc, pc]
      simp only [BitVec.add_assoc]
      rw [show (4 : Word) + (4 + (4 + (4 + (4 + 4)))) = BitVec.ofNat 64 (4 * 6) by rfl, word_pc_add])
    simpa [opAt, p3Ops] using this
  rw [show 2 + fuel = (1 + fuel) + 1 by omega,
    execute_permutation_call _ _ (p3Prep s j) true base dst (by omega) (by omega) p10 p12
      ((pkeep .x5 (by decide) (by decide)).trans ready.selector)
      ((pkeep .x11 (by decide) (by decide)).trans ready.size)
      ((pkeep .x13 (by decide) (by decide)).trans ready.primitive) fetchCall]
  simp only [p3Trace, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro y _
  have lastPC : (writeBits (p3Prep s j) (wordAddress dst) y).pc = wordPC (p3Index j + 7) := by
    rw [written_pc, ppc, pc]
    simp only [BitVec.add_assoc]
    rw [show (4 : Word) + (4 + (4 + (4 + (4 + (4 + 4))))) = BitVec.ofNat 64 (4 * 7) by rfl, word_pc_add]
  have last : execute packedWideCommitImage (fuel + 1) (writeBits (p3Prep s j) (wordAddress dst) y) true =
      (do let r ← execute packedWideCommitImage fuel (p3Final s j dst y) true; return r.charge 1 0) := by
    have fetched := fetch_p3 j hj 7 (by decide) _ lastPC
    exact CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ fetched rfl
  rw [Nat.add_comm 1 fuel, last]
  simp [Execution.charge]
  congr 1
  funext a
  congr 1 <;> omega

theorem p3_final_regs (s : MachineState) (j base dst salts : Nat) (ready : P3Ready s j base dst salts)
    (y : BitVec 1600) :
    (p3Final s j dst y).getReg .x10 = wordAddress (base + 32) ∧ (p3Final s j dst y).getReg .x12 = wordAddress dst ∧
      (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x31 → (p3Final s j dst y).getReg r = s.getReg r) ∧
      (p3Final s j dst y).pc = s.pc + BitVec.ofNat 64 32 := by
  obtain ⟨_, p10, p12, pkeep, ppc⟩ := p3_prep_facts s j base dst salts ready
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [p3Final, addi_self _ _ _ (by decide), CommitGolfCandidate.writeBits_register, p10,
      show (signExtend12 (256 : BitVec 12)) = BitVec.ofNat 64 (8 * 32) by decide, address_up]
  · rw [p3Final, addi_other _ _ _ _ _ (by decide), CommitGolfCandidate.writeBits_register, p12]
  · intro r a b c
    rw [p3Final, addi_other _ _ _ _ _ a, CommitGolfCandidate.writeBits_register, pkeep r b c]
  · rw [p3Final, addi_pc, written_pc, ppc]
    simp only [BitVec.add_assoc]
    congr 1

theorem p3_final_memory (s : MachineState) (j base dst salts : Nat) (ready : P3Ready s j base dst salts)
    (y : BitVec 1600) (w : Nat) (bounded : w < 2 ^ 33) :
    memoryView (p3Final s j dst y) w =
      writeWindow (p3Stamp (memoryView s) base (wordAddress base) (memoryView s (saltWordOf salts j))
        (memoryView s (saltWordOf salts j + 1))) dst (replyWords y) w := by
  have hb := ready.heapBound
  have same : (p3Final s j dst y).mem = (writeBits (p3Prep s j) (wordAddress dst) y).mem := by
    rw [p3Final, addi_mem]
  rw [memoryView_congr same, permutation_write_memory _ _ _ _ hb bounded]
  by_cases inside : dst ≤ w ∧ w < dst + 25
  · simp only [writeWindow, dite_eq_left inside]
  · simp only [writeWindow, dite_eq_right inside]
    exact (p3_prep_facts s j base dst salts ready).1 w bounded

end TwoPermutationPrototype.RV64.C3Leaves
