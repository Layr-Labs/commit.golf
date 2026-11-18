import CommitGolfCandidate.TwoPermutationPackedLowerRecursion
import CommitGolfCandidate.TwoPermutationCheckerLowerRun
import CommitGolfCandidate.CapCompressionStep
import CommitGolfCandidate.K3T238ArmDecode
import CommitGolfCandidate.K3T238ArmCodec

/-! # T238 lower-loop arm: one step of loop levels 5..13

Loop level `L ∈ 5..13` (`x29 = 14 - L`, node at tree level `21 - L`, 238-bit output) runs the K1x copy path,
then `S` (577..620: the sibling's top bits per K3-DESIGN §9), the call at 621..622 with its output masked to
238 bits at 623..626, the jump 627 back to the latch at 236..239. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_recorded_bind check_recorded_map compressed_digest write_bits_word_outside)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

/-! ### The state at the call -/

def preBody (e : MachineState) (left : Nat) (even : Bool) : MachineState :=
  if left = 9 then e.setPC (pcAt 621) else
    let f := t238Parity (e.setPC (pcAt 582)) even
    if left = 1 then t238Short (f.setPC (pcAt 593)) else t238Mid (f.setPC (pcAt 588))

/-- The state at word 622 (the call), from the loop head at word 63. -/
def t238Pre (s : MachineState) (left : Nat) (even : Bool) : MachineState :=
  execInstrBr (preBody (t238Entry (t238Copy s even)) left even) (.ADDI .x12 .x23 0)

def preSteps (left : Nat) (even : Bool) : Nat :=
  45 + 6 + (if left = 9 then 0 else parityCost even + 1 + (if left = 1 then 28 else 5)) + 1

/-- The last sibling's bits `224..237`, as the gather reads them. -/
def gatherTail (s : MachineState) (P : Nat) : BitVec 14 :=
  (spareHalf s P 6).extractLsb' 14 2 ++ (spareHalf s P 5).extractLsb' 14 2 ++ (spareHalf s P 4).extractLsb' 14 2 ++
    (spareHalf s P 3).extractLsb' 14 2 ++ (spareHalf s P 2).extractLsb' 14 2 ++
    (spareHalf s P 1).extractLsb' 14 2 ++ (spareHalf s P 0).extractLsb' 14 2

/-- The sibling the call reads, by loop counter. -/
def preSibling (s : MachineState) (proof left : Nat) : Digest :=
  if left = 9 then 0#16 ++ readBuffer s proof 30
  else if left = 1 then 0#18 ++ (gatherTail s proof ++ (readBuffer s proof 30).extractLsb' 0 224)
  else 0#18 ++ (readBuffer s proof 30).extractLsb' 0 238

/-- The registers the arm writes before the latch. -/
def Scratch (r : Reg) : Prop := r = .x7 ∨ r = .x10 ∨ r = .x12 ∨ r = .x28 ∨ r = .x30 ∨ r = .x31

instance (r : Reg) : Decidable (Scratch r) := by unfold Scratch; infer_instance

theorem jal_x0 (t : MachineState) (off : BitVec 21) :
    execInstrBr t (.JAL .x0 off) = t.setPC (t.pc + signExtend21 off) := rfl

structure PreFacts (s h : MachineState) (node proof left : Nat) (even : Bool) : Prop where
  run : GroupHop s h (preSteps left even)
  pc : h.pc = pcAt 622
  src : h.getReg .x10 = BitVec.ofNat 64 12544
  dst : h.getReg .x12 = BitVec.ofNat 64 12288
  width : h.getReg .x30 = BitVec.ofNat 64 (if left = 1 then 28 else 30)
  regs : ∀ r, ¬ Scratch r → h.getReg r = s.getReg r
  input : readBuffer h 12576 32 ++ readBuffer h 12544 32 = pathPair node (readBuffer s 12288 32) (preSibling s proof left)
  frame : ∀ w < 2^61, (w < 1568 ∨ 1576 ≤ w) → memoryView h w = memoryView s w

/-! ### Pair contents -/

theorem ne_word {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) (ne : a ≠ b) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro eq
  have n := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at n
  exact ne n

theorem pair_of_slots (h : MachineState) (node : Nat) (even : Bool) (parity : even = decide (node % 2 = 0))
    (child sib : Digest) (hc : readBuffer h (8*slotWord (!even)) 32 = child)
    (hs : readBuffer h (sibByte even) 32 = sib) :
    readBuffer h 12576 32 ++ readBuffer h 12544 32 = pathPair node child sib := by
  cases even with
  | true =>
    have e : node % 2 = 0 := of_decide_eq_true parity.symm
    rw [pathPair, if_pos e]
    exact congrArg₂ BitVec.append hs hc
  | false =>
    have o : ¬ node % 2 = 0 := of_decide_eq_false parity.symm
    rw [pathPair, if_neg o]
    exact congrArg₂ BitVec.append hc hs

/-- The child slot is untouched by a change of the sibling's top doubleword. -/
theorem child_kept (c h : MachineState) (even : Bool)
    (other : ∀ a, a ≠ BitVec.ofNat 64 (sibByte even+24) → h.getMem a = c.getMem a) :
    readBuffer h (8*slotWord (!even)) 32 = readBuffer c (8*slotWord (!even)) 32 := by
  apply read_digest_congr _ _ _ (by cases even <;> decide)
  intro i hi
  apply other
  apply ne_word (by cases even <;> simp [slotWord] <;> omega) (by cases even <;> simp [sibByte, slotWord])
  cases even <;> simp [sibByte, slotWord] <;> omega

theorem mid_input (c h : MachineState) (node : Nat) (even : Bool) (parity : even = decide (node % 2 = 0))
    (R : BitVec 240) (child : Digest)
    (cchild : readBuffer c (8*slotWord (!even)) 32 = child) (csib : readBuffer c (sibByte even) 32 = 0#16 ++ R)
    (word : h.getMem (BitVec.ofNat 64 (sibByte even+24)) = (c.getMem (BitVec.ofNat 64 (sibByte even+24)) <<< 18) >>> 18)
    (other : ∀ a, a ≠ BitVec.ofNat 64 (sibByte even+24) → h.getMem a = c.getMem a) :
    readBuffer h 12576 32 ++ readBuffer h 12544 32 = pathPair node child (0#18 ++ R.extractLsb' 0 238) := by
  have sr := sib_room even
  obtain ⟨d0, d1, d2, d3⟩ := dwords_of_read c (sibByte even) sr.2.1 _ csib
  have n0 : BitVec.ofNat 64 (sibByte even) ≠ BitVec.ofNat 64 (sibByte even+24) := ne_word (by omega) (by omega) (by omega)
  have n1 : BitVec.ofNat 64 (sibByte even+8) ≠ BitVec.ofNat 64 (sibByte even+24) := ne_word (by omega) (by omega) (by omega)
  have n2 : BitVec.ofNat 64 (sibByte even+16) ≠ BitVec.ofNat 64 (sibByte even+24) := ne_word (by omega) (by omega) (by omega)
  have agree : ∀ i < 192, ((0#16) ++ R).getLsbD i = ((0#18) ++ R.extractLsb' 0 238).getLsbD i :=
    fun i hi => (wide_low R i hi).trans (mid_low R i hi).symm
  apply pair_of_slots h node even parity _ _ ((child_kept c h even other).trans cchild)
  apply read_of_dwords h (sibByte even) sr.2.1
  · rw [other _ n0, d0]; exact agree_dword _ _ 0 (by decide) agree
  · rw [other _ n1, d1]; exact agree_dword _ _ 64 (by decide) agree
  · rw [other _ n2, d2]; exact agree_dword _ _ 128 (by decide) agree
  · rw [word, d3]; exact mid_top R

theorem short_input (c h : MachineState) (node : Nat) (even : Bool) (parity : even = decide (node % 2 = 0))
    (R : BitVec 240) (T : BitVec 14) (child : Digest)
    (cchild : readBuffer c (8*slotWord (!even)) 32 = child) (csib : readBuffer c (sibByte even) 32 = 0#16 ++ R)
    (word : h.getMem (BitVec.ofNat 64 (sibByte even+24)) =
      replaceWord32 (c.getMem (BitVec.ofNat 64 (sibByte even+24))) 1 ((T.zeroExtend 64).truncate 32))
    (other : ∀ a, a ≠ BitVec.ofNat 64 (sibByte even+24) → h.getMem a = c.getMem a) :
    readBuffer h 12576 32 ++ readBuffer h 12544 32 = pathPair node child (0#18 ++ (T ++ R.extractLsb' 0 224)) := by
  have sr := sib_room even
  obtain ⟨d0, d1, d2, d3⟩ := dwords_of_read c (sibByte even) sr.2.1 _ csib
  have n0 : BitVec.ofNat 64 (sibByte even) ≠ BitVec.ofNat 64 (sibByte even+24) := ne_word (by omega) (by omega) (by omega)
  have n1 : BitVec.ofNat 64 (sibByte even+8) ≠ BitVec.ofNat 64 (sibByte even+24) := ne_word (by omega) (by omega) (by omega)
  have n2 : BitVec.ofNat 64 (sibByte even+16) ≠ BitVec.ofNat 64 (sibByte even+24) := ne_word (by omega) (by omega) (by omega)
  have agree : ∀ i < 192, ((0#16) ++ R).getLsbD i = ((0#18) ++ (T ++ R.extractLsb' 0 224)).getLsbD i :=
    fun i hi => (wide_low R i hi).trans (short_low R T i hi).symm
  apply pair_of_slots h node even parity _ _ ((child_kept c h even other).trans cchild)
  apply read_of_dwords h (sibByte even) sr.2.1
  · rw [other _ n0, d0]; exact agree_dword _ _ 0 (by decide) agree
  · rw [other _ n1, d1]; exact agree_dword _ _ 64 (by decide) agree
  · rw [other _ n2, d2]; exact agree_dword _ _ 128 (by decide) agree
  · rw [word, d3]; exact short_top R T

/-- A proof-region halfword is untouched by the pair writes. -/
theorem spare_frame {s t : MachineState} (P j : Nat)
    (frame : ∀ w < 2^61, (w < 1568 ∨ 1576 ≤ w) → memoryView t w = memoryView s w)
    (above : 32768 ≤ P) (fits : P ≤ MEMORY_BYTES) (small : j ≤ 6) :
    spareHalf t P j = spareHalf s P j := by
  have lim : MEMORY_BYTES = 2^36 := rfl
  unfold spareHalf MachineState.getHalfword
  have e : BitVec.ofNat 64 (P-182+30*j) = BitVec.ofNat 64 (8*((P-182+30*j)/8) + (P-182+30*j)%8) :=
    congrArg _ (by omega)
  have al : alignToDword (BitVec.ofNat 64 (P-182+30*j)) = BitVec.ofNat 64 (8*((P-182+30*j)/8)) := by
    rw [e]; exact arm_align (8*((P-182+30*j)/8)) ((P-182+30*j)%8) (by omega) (by omega)
  have kept := frame ((P-182+30*j)/8) (by omega) (Or.inr (by omega))
  simp only [memoryView, wordAddress] at kept
  rw [al, kept]

theorem gather_tail_frame {s t : MachineState} (P : Nat)
    (frame : ∀ w < 2^61, (w < 1568 ∨ 1576 ≤ w) → memoryView t w = memoryView s w)
    (above : 32768 ≤ P) (fits : P ≤ MEMORY_BYTES) : gatherTail t P = gatherTail s P := by
  unfold gatherTail
  rw [spare_frame P 0 frame above fits (by decide), spare_frame P 1 frame above fits (by decide),
    spare_frame P 2 frame above fits (by decide), spare_frame P 3 frame above fits (by decide),
    spare_frame P 4 frame above fits (by decide), spare_frame P 5 frame above fits (by decide),
    spare_frame P 6 frame above fits (by decide)]

theorem gather_val_tail (z : MachineState) (P : Nat) :
    gatherVal z P 6 = (gatherTail z P).zeroExtend 64 :=
  gather_bits (spareHalf z P 0) (spareHalf z P 1) (spareHalf z P 2) (spareHalf z P 3) (spareHalf z P 4)
    (spareHalf z P 5) (spareHalf z P 6)

/-! ### The run to the call -/

attribute [local irreducible] t238Copy t238Entry t238Parity t238Mid t238Short readBuffer

theorem t238_pre_facts (s : MachineState) (node proof left : Nat) (even : Bool)
    (pc : s.pc = 4348) (nodeReg : s.getReg .x6 = BitVec.ofNat 64 node) (nodeBound : node < 2^64)
    (parity : even = decide (node % 2 = 0)) (proofReg : s.getReg .x21 = BitVec.ofNat 64 proof)
    (counter : s.getReg .x29 = BitVec.ofNat 64 left) (low : 1 ≤ left) (high : left ≤ 9)
    (digest : s.getReg .x23 = 12288) (pair : s.getReg .x24 = 12544)
    (above : 32768 ≤ proof) (aligned : proof % 2 = 0) (room : proof + 30 ≤ MEMORY_BYTES) :
    PreFacts s (t238Pre s left even) node proof left even := by
  have lim : MEMORY_BYTES = 2^36 := rfl
  have cf := t238_copy s node proof left even pc nodeReg nodeBound parity proofReg counter (by omega) digest pair
    above aligned room
  generalize hc : t238Copy s even = c at cf
  have cx (r : Reg) (a : r ≠ .x31) (b : r ≠ .x7) (d : r ≠ .x30) : c.getReg r = s.getReg r := cf.regs r a b d
  have c29 : c.getReg .x29 = BitVec.ofNat 64 left := (cx _ (by decide) (by decide) (by decide)).trans counter
  have c24 : c.getReg .x24 = 12544 := (cx _ (by decide) (by decide) (by decide)).trans pair
  have ent := execute_entry c left cf.pc c29 (by omega)
  obtain ⟨epc, emem, ex7, ex10, eregs⟩ := entry_facts c c24
  generalize he : t238Entry c = e at ent epc emem ex7 ex10 eregs
  have ex (r : Reg) (a : r ≠ .x31) (b : r ≠ .x7) (d : r ≠ .x30) (f : r ≠ .x10) : e.getReg r = s.getReg r :=
    (eregs r b f).trans (cx r a b d)
  have e29 : e.getReg .x29 = BitVec.ofNat 64 left := (eregs _ (by decide) (by decide)).trans c29
  have e23 : e.getReg .x23 = 12288 := ex _ (by decide) (by decide) (by decide) (by decide) |>.trans digest
  have e30 : e.getReg .x30 = BitVec.ofNat 64 30 := (eregs _ (by decide) (by decide)).trans cf.width
  have hpre : t238Pre s left even = execInstrBr (preBody e left even) (.ADDI .x12 .x23 0) := by
    unfold t238Pre; rw [hc, he]
  rw [hpre]
  -- the call output register and the final step, from any body state at word 621
  have finish (b : MachineState) (bpc : b.pc = pcAt 621) (b23 : b.getReg .x23 = 12288) :
      GroupHop b (execInstrBr b (.ADDI .x12 .x23 0)) 1 ∧ (execInstrBr b (.ADDI .x12 .x23 0)).pc = pcAt 622 ∧
        (execInstrBr b (.ADDI .x12 .x23 0)).getReg .x12 = BitVec.ofNat 64 12288 ∧
        (∀ r, r ≠ .x12 → (execInstrBr b (.ADDI .x12 .x23 0)).getReg r = b.getReg r) ∧
        (execInstrBr b (.ADDI .x12 .x23 0)).mem = b.mem := by
    refine ⟨arm_hop b 621 _ (by decide) bpc rfl rfl rfl, ?_, ?_, ?_, rfl⟩
    · show b.pc + 4 = _; rw [bpc]; rfl
    · simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x12 ≠ .x0 by decide), b23]
      rfl
    · intro r a
      simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a)]
  by_cases nine : left = 9
  · -- loop level 5: the 30-byte sibling as copied, straight to the call
    have br := arm_branch e 581 621 (.BEQ .x29 .x7 160) (by decide) epc rfl (by
      show (if (e.getReg .x29 == e.getReg .x7) = true then e.setPC (e.pc + signExtend13 160) else e.setPC (e.pc + 4)) = _
      rw [if_pos (by rw [e29, ex7, nine]; rfl), epc]; rfl) rfl rfl
    have body : preBody e left even = e.setPC (pcAt 621) := by unfold preBody; rw [if_pos nine]
    rw [body]
    obtain ⟨hop, hpc, h12, hregs, hmem⟩ := finish (e.setPC (pcAt 621)) rfl (by rw [MachineState.getReg_setPC, e23])
    have steps : preSteps left even = 45+5+1+1 := by simp [preSteps, nine]
    refine ⟨?_, hpc, ?_, h12, ?_, ?_, ?_, ?_⟩
    · rw [steps]; exact ((cf.run.thenDo ent).thenDo br).thenDo hop
    · rw [hregs _ (by decide), MachineState.getReg_setPC, ex10]
    · rw [hregs _ (by decide), MachineState.getReg_setPC, e30, if_neg (by omega)]
    · intro r scr
      have a : r ≠ .x7 := fun h => scr (Or.inl h)
      have b : r ≠ .x10 := fun h => scr (Or.inr (Or.inl h))
      have d : r ≠ .x12 := fun h => scr (Or.inr (Or.inr (Or.inl h)))
      have f : r ≠ .x30 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      have g : r ≠ .x31 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      rw [hregs r d, MachineState.getReg_setPC]
      exact ex r g a f b
    · have m : (execInstrBr (e.setPC (pcAt 621)) (.ADDI .x12 .x23 0)).mem = c.mem := hmem.trans emem
      rw [read_mem m, read_mem m]
      unfold preSibling; rw [if_pos nine]
      exact pair_of_slots c node even parity _ _ cf.child cf.sibling
    · intro w hw outside
      have m : (execInstrBr (e.setPC (pcAt 621)) (.ADDI .x12 .x23 0)).mem = c.mem := hmem.trans emem
      rw [view_mem m]
      exact cf.frame w hw outside
  · -- loop levels 6..13: the sibling's halfword 14
    have br := arm_branch e 581 582 (.BEQ .x29 .x7 160) (by decide) epc rfl (by
      show (if (e.getReg .x29 == e.getReg .x7) = true then e.setPC (e.pc + signExtend13 160) else e.setPC (e.pc + 4)) = _
      rw [if_neg (by rw [e29, ex7, beq_word _ _ (by omega) (by decide)]; simp [nine]), epc]; rfl) rfl rfl
    let y := e.setPC (pcAt 582)
    have y6 : y.getReg .x6 = BitVec.ofNat 64 node :=
      (MachineState.getReg_setPC).trans ((ex _ (by decide) (by decide) (by decide) (by decide)).trans nodeReg)
    have par := execute_parity y node even rfl y6 nodeBound parity
    obtain ⟨fpc, fmem, fx7, fx28, fregs⟩ := parity_facts y even ((MachineState.getReg_setPC).trans (by
      rw [eregs _ (by decide) (by decide)]; exact c24))
    generalize hf : t238Parity y even = f at par fpc fmem fx7 fx28 fregs
    have fy (r : Reg) (a : r ≠ .x7) (b : r ≠ .x28) : f.getReg r = e.getReg r :=
      (fregs r a b).trans MachineState.getReg_setPC
    have f29 : f.getReg .x29 = BitVec.ofNat 64 left := (fy _ (by decide) (by decide)).trans e29
    have fm : f.mem = c.mem := fmem.trans emem
    by_cases one : left = 1
    · -- loop level 13: gather the last sibling's top bits
      have br2 := arm_branch f 587 593 (.BEQ .x29 .x7 24) (by decide) fpc rfl (by
        show (if (f.getReg .x29 == f.getReg .x7) = true then f.setPC (f.pc + signExtend13 24) else f.setPC (f.pc + 4)) = _
        rw [if_pos (by rw [f29, fx7, one]; rfl), fpc]; rfl) rfl rfl
      let z := f.setPC (pcAt 593)
      have z21 : z.getReg .x21 = BitVec.ofNat 64 proof := (MachineState.getReg_setPC).trans
        ((fy _ (by decide) (by decide)).trans ((ex _ (by decide) (by decide) (by decide) (by decide)).trans proofReg))
      have z28 : z.getReg .x28 = BitVec.ofNat 64 (sibByte even+28) := (MachineState.getReg_setPC).trans fx28
      obtain ⟨sh, spost⟩ := execute_short z even proof rfl z21 (by omega) aligned (by omega) z28
      have body : preBody e left even = t238Short z := by
        unfold preBody; rw [if_neg nine]; dsimp only; rw [hf, if_pos one]
      rw [body]
      have s23 : (t238Short z).getReg .x23 = 12288 :=
        (spost.regs _ (by decide) (by decide) (by decide)).trans ((MachineState.getReg_setPC).trans
          ((fy _ (by decide) (by decide)).trans e23))
      obtain ⟨hop, hpc, h12, hregs, hmem⟩ := finish (t238Short z) spost.pc s23
      have steps : preSteps left even = 45+5+1+parityCost even+1+28+1 := by
        simp [preSteps, nine, one]; omega
      refine ⟨?_, hpc, ?_, h12, ?_, ?_, ?_, ?_⟩
      · rw [steps]; exact (((((cf.run.thenDo ent).thenDo br).thenDo par).thenDo br2).thenDo sh).thenDo hop
      · rw [hregs _ (by decide), spost.regs _ (by decide) (by decide) (by decide), MachineState.getReg_setPC,
          fy _ (by decide) (by decide), ex10]
      · rw [hregs _ (by decide), spost.x30, if_pos one]
      · intro r scr
        have a : r ≠ .x7 := fun h => scr (Or.inl h)
        have b : r ≠ .x10 := fun h => scr (Or.inr (Or.inl h))
        have d : r ≠ .x12 := fun h => scr (Or.inr (Or.inr (Or.inl h)))
        have k : r ≠ .x28 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        have f' : r ≠ .x30 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        have g : r ≠ .x31 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        rw [hregs r d, spost.regs r g a f', MachineState.getReg_setPC, fy r a k]
        exact ex r g a f' b
      · have m : (execInstrBr (t238Short z) (.ADDI .x12 .x23 0)).mem = (t238Short z).mem := hmem
        rw [read_mem m, read_mem m]
        have zc : ∀ a, z.getMem a = c.getMem a := fun a => by
          show f.getMem a = c.getMem a
          simp only [MachineState.getMem, fm]
        have tail : gatherTail z proof = gatherTail s proof := by
          apply gather_tail_frame proof _ above (by omega)
          intro w hw outside
          rw [show memoryView z w = memoryView c w from by simp only [memoryView, zc]]
          exact cf.frame w hw outside
        unfold preSibling; rw [if_neg nine, if_pos one]
        have word := spost.word
        rw [zc, gather_val_tail, tail] at word
        apply short_input c (t238Short z) node even parity (readBuffer s proof 30) (gatherTail s proof) _ cf.child
          cf.sibling word
        intro a ha
        exact (spost.other a ha).trans (zc a)
      · intro w hw outside
        have m : (execInstrBr (t238Short z) (.ADDI .x12 .x23 0)).mem = (t238Short z).mem := hmem
        rw [view_mem m]
        have ne : wordAddress w ≠ BitVec.ofNat 64 (sibByte even+24) := by
          have sr := sib_room even
          unfold wordAddress
          apply ne_word (by omega) (by omega)
          cases even <;> simp [sibByte, slotWord] at outside ⊢ <;> omega
        show (t238Short z).getMem (wordAddress w) = s.getMem (wordAddress w)
        rw [spost.other _ ne]
        show f.getMem (wordAddress w) = _
        rw [show f.getMem (wordAddress w) = c.getMem (wordAddress w) from by simp only [MachineState.getMem, fm]]
        exact cf.frame w hw outside
    · -- loop levels 6..12: clear the sibling's bits 238..255
      have br2 := arm_branch f 587 588 (.BEQ .x29 .x7 24) (by decide) fpc rfl (by
        show (if (f.getReg .x29 == f.getReg .x7) = true then f.setPC (f.pc + signExtend13 24) else f.setPC (f.pc + 4)) = _
        rw [if_neg (by rw [f29, fx7, beq_word _ _ (by omega) (by decide)]; simp [one]), fpc]; rfl) rfl rfl
      let z := f.setPC (pcAt 588)
      have z28 : z.getReg .x28 = BitVec.ofNat 64 (sibByte even+28) := (MachineState.getReg_setPC).trans fx28
      obtain ⟨md, mpost⟩ := execute_mid z even rfl z28
      have mpc := mid_pc z even rfl z28
      have body : preBody e left even = t238Mid z := by
        unfold preBody; rw [if_neg nine]; dsimp only; rw [hf, if_neg one]
      rw [body]
      have jeq : t238Mid z = (maskAfter z .x28 0).setPC ((maskAfter z .x28 0).pc + signExtend21 116) := by
        unfold t238Mid; exact jal_x0 _ _
      have midMem : ∀ a, (t238Mid z).getMem a = (maskAfter z .x28 0).getMem a := fun a => by
        rw [jeq, arm_getMem_set_pc]
      have midReg : ∀ r, (t238Mid z).getReg r = (maskAfter z .x28 0).getReg r := fun r => by
        rw [jeq, MachineState.getReg_setPC]
      have s23 : (t238Mid z).getReg .x23 = 12288 := by
        rw [midReg, mpost.regs _ (by decide), MachineState.getReg_setPC, fy _ (by decide) (by decide)]
        exact e23
      obtain ⟨hop, hpc, h12, hregs, hmem⟩ := finish (t238Mid z) mpc s23
      have steps : preSteps left even = 45+5+1+parityCost even+1+5+1 := by
        simp [preSteps, nine, one]; omega
      refine ⟨?_, hpc, ?_, h12, ?_, ?_, ?_, ?_⟩
      · rw [steps]; exact (((((cf.run.thenDo ent).thenDo br).thenDo par).thenDo br2).thenDo md).thenDo hop
      · rw [hregs _ (by decide), midReg, mpost.regs _ (by decide), MachineState.getReg_setPC,
          fy _ (by decide) (by decide), ex10]
      · rw [hregs _ (by decide), midReg, mpost.regs _ (by decide), MachineState.getReg_setPC,
          fy _ (by decide) (by decide), e30, if_neg one]
      · intro r scr
        have a : r ≠ .x7 := fun h => scr (Or.inl h)
        have b : r ≠ .x10 := fun h => scr (Or.inr (Or.inl h))
        have d : r ≠ .x12 := fun h => scr (Or.inr (Or.inr (Or.inl h)))
        have k : r ≠ .x28 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        have f' : r ≠ .x30 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        have g : r ≠ .x31 := fun h => scr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        rw [hregs r d, midReg, mpost.regs r g, MachineState.getReg_setPC, fy r a k]
        exact ex r g a f' b
      · have m : (execInstrBr (t238Mid z) (.ADDI .x12 .x23 0)).mem = (t238Mid z).mem := hmem
        rw [read_mem m, read_mem m]
        have zc : ∀ a, z.getMem a = c.getMem a := fun a => by
          show f.getMem a = c.getMem a
          simp only [MachineState.getMem, fm]
        unfold preSibling; rw [if_neg nine, if_neg one]
        have word := mpost.word
        rw [zc] at word
        apply mid_input c (t238Mid z) node even parity (readBuffer s proof 30) _ cf.child cf.sibling
          ((midMem _).trans word)
        intro a ha
        exact (midMem a).trans ((mpost.other a ha).trans (zc a))
      · intro w hw outside
        have m : (execInstrBr (t238Mid z) (.ADDI .x12 .x23 0)).mem = (t238Mid z).mem := hmem
        rw [view_mem m]
        have ne : wordAddress w ≠ BitVec.ofNat 64 (sibByte even+24) := by
          have sr := sib_room even
          unfold wordAddress
          apply ne_word (by omega) (by omega)
          cases even <;> simp [sibByte, slotWord] at outside ⊢ <;> omega
        show (t238Mid z).getMem (wordAddress w) = s.getMem (wordAddress w)
        rw [midMem, mpost.other _ ne]
        show f.getMem (wordAddress w) = _
        rw [show f.getMem (wordAddress w) = c.getMem (wordAddress w) from by simp only [MachineState.getMem, fm]]
        exact cf.frame w hw outside

theorem charge_charge (r : Execution) (a b c d : Nat) : (r.charge a b).charge c d = r.charge (c + a) (d + b) := by
  simp only [Execution.charge, Nat.add_assoc]

/-! ### The call (622), its 238-bit mask (623..626), the jump to the latch (627) -/

def callPost (h : MachineState) (answer : BitVec 256) : MachineState :=
  execInstrBr (maskAfter (capCompressionAnswer h answer) .x23 28) (.JAL .x0 2095588)

def t238Post (h : MachineState) (answer : BitVec 256) : MachineState := latch (callPost h answer)

structure CallFacts (h : MachineState) (answer : BitVec 256) (t : MachineState) : Prop where
  hop : GroupHop (capCompressionAnswer h answer) t 5
  pc : t.pc = 0x13b0
  regs : ∀ r, r ≠ .x31 → t.getReg r = h.getReg r
  node : readBuffer t 12288 32 = pad238 answer
  frame : ∀ w < 2^33, (w < 1536 ∨ 1540 ≤ w) → memoryView t w = memoryView h w

theorem call_facts (h : MachineState) (answer : BitVec 256) (pc : h.pc = pcAt 622)
    (dst : h.getReg .x12 = BitVec.ofNat 64 12288) (x23 : h.getReg .x23 = 12288) :
    CallFacts h answer (callPost h answer) := by
  let k := capCompressionAnswer h answer
  have kmem : k = writeBits h (wordAddress 1536) answer := by
    show writeBits h (h.getReg .x12) answer = _
    rw [dst]; rfl
  have kpc : k.pc = pcAt 623 := by
    have moved : k.pc = h.pc + 4 := by
      show (capCompressionAnswer h answer).pc = _
      unfold capCompressionAnswer writeBits; rfl
    rw [moved, pc]; rfl
  have kreg : ∀ r, k.getReg r = h.getReg r := by
    intro r; rw [kmem]; exact writeBits_register h _ answer r
  have k23 : k.getReg .x23 = 12288 := (kreg _).trans x23
  have address : k.getReg .x23 + signExtend12 28 = BitVec.ofNat 64 (12312+4) := by rw [k23]; rfl
  have run := execute_mask k 623 .x23 28 12312 (by decide) kpc rfl rfl rfl rfl address (by decide) (by decide)
    (by decide)
  have post := mask_post k .x23 28 12312 address (by decide) (by decide)
  have mpc : (maskAfter k .x23 28).pc = pcAt 627 := by rw [post.pc, kpc]; rfl
  have jump := arm_hop (maskAfter k .x23 28) 627 (.JAL .x0 2095588) (by decide) mpc rfl rfl rfl
  have kread : readBuffer k 12288 32 = answer := by rw [kmem]; exact compressed_digest h 1536 answer
  obtain ⟨d0, d1, d2, d3⟩ := dwords_of_read k 12288 (by decide) answer kread
  have d3' : k.getMem (BitVec.ofNat 64 12312) = answer.extractLsb' 192 64 := d3
  have hcp : callPost h answer = (maskAfter k .x23 28).setPC ((maskAfter k .x23 28).pc + signExtend21 2095588) :=
    jal_x0 _ _
  have callMem : ∀ a, (callPost h answer).getMem a = (maskAfter k .x23 28).getMem a := fun a => by
    rw [hcp, arm_getMem_set_pc]
  have hop : GroupHop k (callPost h answer) 5 := run.thenDo jump
  refine ⟨hop, ?_, ?_, ?_, ?_⟩
  · rw [hcp, arm_pc_set_pc, mpc]; rfl
  · intro r hr
    rw [hcp, MachineState.getReg_setPC, post.regs r hr]
    exact kreg r
  · apply read_pad238 _ 12288 (by decide) answer
    · rw [callMem, post.other _ (by decide), d0]
    · rw [callMem, post.other _ (by decide), d1]
    · rw [callMem, post.other _ (by decide), d2]
    · show (callPost h answer).getMem (BitVec.ofNat 64 12312) = _
      rw [callMem, post.word, d3', top238_shift]
  · intro w hw outside
    show (callPost h answer).getMem (wordAddress w) = h.getMem (wordAddress w)
    have ne : wordAddress w ≠ BitVec.ofNat 64 12312 := by
      unfold wordAddress; exact ne_word (by omega) (by decide) (by omega)
    rw [callMem, post.other _ ne, kmem]
    exact write_bits_word_outside h answer 1536 w (by decide) (by omega) (by omega)

theorem t238_call (h : MachineState) (pc : h.pc = pcAt 622) (src : h.getReg .x10 = BitVec.ofNat 64 12544)
    (dst : h.getReg .x12 = BitVec.ofNat 64 12288) (x23 : h.getReg .x23 = 12288)
    (selector : h.getReg .x5 = 0 ∧ h.getReg .x11 = 64 ∧ h.getReg .x13 = 0) (fuel : Nat) :
    execute packedImage (1+5+4+fuel) h false = do
      let answer ← World.query (.inr (.inl (readBuffer h 12576 32 ++ readBuffer h 12544 32)))
      let result ← execute packedImage fuel (t238Post h answer) false
      return result.charge (8+5+4) 1 := by
  have srcV : rangeValid (h.getReg .x10) 64 = true := by rw [src]; decide
  have dstV : rangeValid (h.getReg .x12) 32 = true := by rw [dst]; decide
  have asrc : (h.getReg .x10).toNat % 8 = 0 := by rw [src]; decide
  have adst : (h.getReg .x12).toNat % 8 = 0 := by rw [dst]; decide
  have call := cap_compression_execute packedImage h (fetch_at h 622 .ECALL (by decide) pc rfl) selector
    srcV dstV asrc adst (5+(4+fuel)) false
  change execute packedImage (1+(5+(4+fuel))) h false = (do
    let answer ← World.query (.inr (.inl (readBuffer h (h.getReg .x10).toNat 64)))
    let result ← execute packedImage (5+(4+fuel)) (capCompressionAnswer h answer) false
    return result.charge 8 1) at call
  rw [src, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide : 12544 < 2^64),
    read_compression_halves h 12544 (by decide), show (12544:Nat)+32 = 12576 from rfl] at call
  rw [show 1+5+4+fuel = 1+(5+(4+fuel)) by omega, call]
  congr 1
  funext answer
  have cf := call_facts h answer pc dst x23
  rw [cf.hop (4+fuel), execute_latch _ cf.pc fuel]
  simp only [t238Post, bind_assoc, pure_bind, charge_charge]

/-! ### The step -/

def t238Query (h : MachineState) (pair : BitVec 512) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inl pair))
  return t238Post h answer

theorem t238_rows (oracle : Oracle) (h : MachineState) (pair : BitVec 512) :
    checkEvaluation oracle (recordRows (t238Query h pair)) =
      ((t238Post h (oracle.compression pair), [.compression pair (oracle.compression pair)]), 1) := by
  simp only [t238Query, record_rows_query, check_evaluation_public_bind, check_evaluation_map, record_rows_pure,
    check_evaluation_pure]
  rfl

/-- One T238 loop level (`5 ≤ level < 14`). -/
def t238Step (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState) : RecordBlock :=
  let node := Opening.lowerNode index (level+2)
  let even := decide (node % 2 = 0)
  let h := t238Pre state (14-level) even
  let pair := pathPair node (readBuffer state 12288 32) (lowerWireSibling state ordinal level)
  let answer := oracle.compression pair
  ⟨t238Post h answer, preSteps (14-level) even + 10, preSteps (14-level) even + 17, [.compression pair answer]⟩

theorem node_keep_lower_t238 (index : Index) (level : Nat) (low : 5 ≤ level) (high : level < 14) (x : Digest) :
    nodeKeep (Opening.lowerNode index (level+3)) x = pad238 x := by
  have shift := QuartetCheck.lower_node_shift index (level+1)
  rw [show level+1+2 = level+3 by omega] at shift
  have bounded := index.isLt
  change index.val < 16777216 at bounded
  have lo : (2:Nat)^6 ≤ 2^(level+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hi : (2:Nat)^(level+1) ≤ 2^14 := Nat.pow_le_pow_right (by decide) (by omega)
  have lo8 : 2^8 ≤ Opening.lowerNode index (level+3) := by
    rw [shift]
    apply (Nat.le_div_iff_mul_le (by positivity)).2
    have m : 2^8 * 2^(level+1) ≤ 2^8 * 2^14 := Nat.mul_le_mul_left _ hi
    have q : (2:Nat)^8 * 2^14 = 4194304 := by norm_num
    omega
  have hi17 : Opening.lowerNode index (level+3) < 2^17 := by
    rw [shift]
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    have m : 2^17 * 2^6 ≤ 2^17 * 2^(level+1) := Nat.mul_le_mul_left _ lo
    have q : (2:Nat)^17 * 2^6 = 8388608 := by norm_num
    omega
  exact node_keep_238 hi17 x

theorem spare_eq (s : MachineState) (ordinal j : Nat) (small : j ≤ 6)
    (even6 : lowerProofByte ordinal 6 % 2 = 0) (fits : lowerProofByte ordinal 6 + 238 ≤ MEMORY_BYTES) :
    (spareHalf s (lowerProofByte ordinal 13) j).extractLsb' 14 2 = packedSpare s ordinal j := by
  have p13 := packed_slot_byte ordinal 13 (by decide) (by decide)
  have pj := packed_slot_byte ordinal (6+j) (by omega) (by omega)
  unfold spareHalf packedSpare
  rw [show lowerProofByte ordinal 13 - 182 + 30*j = lowerProofByte ordinal (6+j) + 28 by rw [p13, pj]; omega]
  exact half_spare s _ (by rw [pj]; omega) (by rw [pj]; omega)

theorem pre_sibling_wire (s : MachineState) (ordinal level : Nat) (low : 5 ≤ level) (high : level < 14)
    (even6 : lowerProofByte ordinal 6 % 2 = 0) (fits : lowerProofByte ordinal 6 + 238 ≤ MEMORY_BYTES) :
    preSibling s (lowerProofByte ordinal level) (14-level) = lowerWireSibling s ordinal level := by
  unfold preSibling lowerWireSibling
  by_cases five : level = 5
  · subst five; simp
  · have n9 : ¬ (14 - level = 9) := by omega
    have n1 : ¬ level ≤ 1 := by omega
    have n5 : ¬ level ≤ 5 := by omega
    rw [if_neg n9, if_neg n1, if_neg n5]
    unfold packedSibling
    by_cases last : level = 13
    · subst last
      rw [if_pos (show 14 - 13 = 1 from rfl), if_pos (show (13:Nat) = 13 from rfl)]
      have slice := read_buffer_slice s (lowerProofByte ordinal 13) 30 0 28 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero] at slice
      rw [slice]
      unfold gatherTail packedTail
      rw [spare_eq s ordinal 0 (by decide) even6 fits, spare_eq s ordinal 1 (by decide) even6 fits,
        spare_eq s ordinal 2 (by decide) even6 fits, spare_eq s ordinal 3 (by decide) even6 fits,
        spare_eq s ordinal 4 (by decide) even6 fits, spare_eq s ordinal 5 (by decide) even6 fits,
        spare_eq s ordinal 6 (by decide) even6 fits]
      rfl
    · rw [if_neg (show ¬ (14 - level = 1) by omega), if_neg last]
      rfl

theorem ofNat_eq_zero (a : Nat) (h : a < 2^64) : BitVec.ofNat 64 a = 0 ↔ a = 0 := by
  rw [show (0:Word) = BitVec.ofNat 64 0 from rfl, ← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.zero_mod]

theorem dec_word (level : Nat) (h : level < 14) : BitVec.ofNat 64 (14-level) - 1 = BitVec.ofNat 64 (14-(level+1)) := by
  have eq : BitVec.ofNat 64 (14-level) = BitVec.ofNat 64 (14-(level+1)) + 1 := by
    change _ = BitVec.ofNat 64 (14-(level+1)) + BitVec.ofNat 64 1
    rw [← BitVec.ofNat_add, show 14-(level+1)+1 = 14-level by omega]
  rw [eq, BitVec.add_sub_cancel]

theorem latch_facts (q : MachineState) :
    (latch q).getReg .x6 = q.getReg .x6 >>> 1 ∧ (latch q).getReg .x21 = q.getReg .x21 + q.getReg .x30 ∧
    (latch q).getReg .x29 = q.getReg .x29 - 1 ∧ (latch q).pc = (if q.getReg .x29 - 1 = 0 then 0x13c0 else 0x10fc) ∧
    (∀ r, r ≠ .x6 → r ≠ .x21 → r ≠ .x29 → (latch q).getReg r = q.getReg r) ∧ (latch q).mem = q.mem := by
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl⟩
  · simp only [latch, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x29 ≠ .x6 by decide),
      MachineState.getReg_setReg_eq (show Reg.x6 ≠ .x0 by decide)]
  · simp only [latch, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x29 ≠ .x21 by decide),
      MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x6 ≠ .x21 by decide),
      MachineState.getReg_setReg_eq (show Reg.x21 ≠ .x0 by decide)]
  · simp only [latch, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (show Reg.x29 ≠ .x0 by decide)]
  · intro r a b c
    simp only [latch, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b), MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm c)]

theorem t238_step_facts (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState)
    (mid : 5 ≤ level) (within : level < 14) (room : checkProofByte ordinal+536 ≤ MEMORY_BYTES)
    (cursor : LowerCursor ordinal index level state) :
    LowerStepFacts oracle ordinal index level state (t238Step oracle ordinal index level state) := by
  have lim : MEMORY_BYTES = 2^36 := rfl
  let node := Opening.lowerNode index (level+2)
  let proof := lowerProofByte ordinal level
  let even := decide (node % 2 = 0)
  have proofEq : proof = checkProofByte ordinal + 176 + 30*(level-2) := by
    show lowerProofByte ordinal level = _
    unfold lowerProofByte; rw [if_neg (show ¬ level ≤ 1 by omega), if_pos (show level ≤ 13 by omega)]
    all_goals omega
  have six : lowerProofByte ordinal 6 = checkProofByte ordinal + 296 := by
    unfold lowerProofByte; rw [if_neg (show ¬ (6:Nat) ≤ 1 by decide), if_pos (show (6:Nat) ≤ 13 by decide)]
    all_goals omega
  have base : 32768 ≤ checkProofByte ordinal ∧ checkProofByte ordinal % 2 = 0 := by
    unfold checkProofByte; omega
  have nodeBound : node < 2^64 := by
    have fit := Opening.lower_node_bound index (level+2)
    change Opening.lowerNode index (level+2) < 33554432 at fit
    exact fit.trans (by decide)
  have pf := t238_pre_facts state node proof (14-level) even (cursor.pc.trans (if_neg (by omega))) cursor.node
    nodeBound rfl cursor.proof cursor.counter (by omega) (by omega) cursor.digest cursor.pair (by omega) (by omega)
    (by omega)
  let pair := pathPair node (readBuffer state 12288 32) (lowerWireSibling state ordinal level)
  have input : readBuffer (t238Pre state (14-level) even) 12576 32 ++
      readBuffer (t238Pre state (14-level) even) 12544 32 = pair := by
    rw [pf.input, pre_sibling_wire state ordinal level mid within (by rw [six]; omega) (by rw [six]; omega)]
  show LowerStepFacts oracle ordinal index level state
    ⟨t238Post (t238Pre state (14-level) even) (oracle.compression pair), preSteps (14-level) even + 10,
      preSteps (14-level) even + 17, [.compression pair (oracle.compression pair)]⟩
  generalize t238Pre state (14-level) even = h at pf input
  have h23 : h.getReg .x23 = 12288 := (pf.regs _ (by decide)).trans cursor.digest
  have sel : h.getReg .x5 = 0 ∧ h.getReg .x11 = 64 ∧ h.getReg .x13 = 0 :=
    ⟨(pf.regs _ (by decide)).trans cursor.selector, (pf.regs _ (by decide)).trans cursor.syscallBytes,
      (pf.regs _ (by decide)).trans cursor.syscallSelector⟩
  have cfx := call_facts h (oracle.compression pair) pf.pc pf.dst h23
  obtain ⟨l6, l21, l29, lpc, lregs, lmem⟩ := latch_facts (callPost h (oracle.compression pair))
  have q (r : Reg) (a : r ≠ .x31) : (callPost h (oracle.compression pair)).getReg r = h.getReg r := cfx.regs r a
  have keep (r : Reg) (scr : ¬ Scratch r) (a : r ≠ .x6) (b : r ≠ .x21) (c : r ≠ .x29) :
      (t238Post h (oracle.compression pair)).getReg r = state.getReg r :=
    (lregs r a b c).trans ((q r (fun e => scr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))))).trans (pf.regs r scr))
  have width : lowerSiblingWidth level = if 14 - level = 1 then 28 else 30 := by
    unfold lowerSiblingWidth
    by_cases last : level = 13
    · subst last; rfl
    · rw [if_neg (show ¬ level ≤ 1 by omega), if_pos (show level ≤ 12 by omega), if_neg (show ¬ (14 - level = 1) by omega)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- pc
    show (latch (callPost h (oracle.compression pair))).pc = _
    rw [lpc, q _ (by decide), pf.regs _ (by decide), cursor.counter]
    rw [dec_word level within]
    by_cases last : level+1 = 14
    · rw [if_pos ((ofNat_eq_zero _ (by omega)).mpr (by omega)), if_pos last]; try rfl
    · rw [if_neg (fun e => last (by have := (ofNat_eq_zero _ (by omega)).mp e; omega)), if_neg last]; try rfl
  · -- node
    show (latch (callPost h (oracle.compression pair))).getReg .x6 = _
    rw [l6, q _ (by decide), pf.regs _ (by decide), cursor.node, show level+1+2 = (level+2)+1 by omega,
      Opening.lower_node_next index (level+2)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt nodeBound,
      Nat.mod_eq_of_lt (by omega : node/2 < 2^64), Nat.shiftRight_eq_div_pow]
    try rfl
  · -- proof cursor
    show (latch (callPost h (oracle.compression pair))).getReg .x21 = _
    rw [l21, q _ (by decide), q _ (by decide), pf.regs _ (by decide), cursor.proof, pf.width,
      lower_proof_byte_next ordinal level within, width, ← BitVec.ofNat_add]
  · -- counter
    show (latch (callPost h (oracle.compression pair))).getReg .x29 = _
    rw [l29, q _ (by decide), pf.regs _ (by decide), cursor.counter, dec_word level within]
  · exact (keep _ (by decide) (by decide) (by decide) (by decide)).trans cursor.digest
  · exact (keep _ (by decide) (by decide) (by decide) (by decide)).trans cursor.pair
  · exact (keep _ (by decide) (by decide) (by decide) (by decide)).trans cursor.selector
  · exact (keep _ (by decide) (by decide) (by decide) (by decide)).trans cursor.syscallBytes
  · exact (keep _ (by decide) (by decide) (by decide) (by decide)).trans cursor.syscallSelector
  · -- steps
    show preSteps (14-level) even + 10 ≤ 116
    unfold preSteps parityCost
    split_ifs <;> omega
  · -- saved
    intro r ok
    unfold RecordSaved at ok
    apply keep
    all_goals rcases ok with e|e|e|e|e|e|e|e|e|e|e|e|e|e <;> subst e <;> decide
  · -- frame
    intro w hw lowOut pairOut
    show memoryView (latch (callPost h (oracle.compression pair))) w = _
    rw [view_mem lmem, cfx.frame w hw lowOut, pf.frame w (by omega) pairOut]
  · -- digest
    show readBuffer (latch (callPost h (oracle.compression pair))) 12288 32 = _
    rw [read_mem lmem, cfx.node]
    exact (node_keep_lower_t238 index level mid within _).symm
  · exact List.mem_singleton_self _
  · -- run
    intro fuel
    have exec : execute packedImage (preSteps (14-level) even + 10 + fuel) state false = do
        let next ← t238Query h pair
        let result ← execute packedImage fuel next false
        return result.charge (preSteps (14-level) even + 17) 1 := by
      rw [show preSteps (14-level) even + 10 + fuel = preSteps (14-level) even + (1+5+4+fuel) by omega, pf.run,
        t238_call h pf.pc pf.src pf.dst h23 sel fuel, input]
      simp only [t238Query, bind_assoc, pure_bind, Execution.charge]
      congr 1
      funext answer
      congr 1
      funext result
      congr 2 <;> omega
    dsimp only
    rw [exec, check_recorded_bind, t238_rows]
    dsimp only
    erw [show (do
      let result ← execute packedImage fuel (t238Post h (oracle.compression pair)) false
      pure (result.charge (preSteps (14-level) even + 17) 1)) =
      (fun result => result.charge (preSteps (14-level) even + 17) 1) <$>
        execute packedImage fuel (t238Post h (oracle.compression pair)) false from bind_pure_comp _ _]
    rw [check_recorded_map]
    try rfl

end TwoPermutationPrototype.Packed.Checker
