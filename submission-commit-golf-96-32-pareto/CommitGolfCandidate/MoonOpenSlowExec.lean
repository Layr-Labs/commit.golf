import CommitGolfCandidate.MoonOpenSlow

/-! Symbolic execution of `slow_mid` (`5,592,064 ≤ g < 5,592,384`), `slow_tail`
(`5,592,384 ≤ g ≤ 5,592,405`), and the combined `openRuns_slow_body` handler (`PC 4488`),
plus the shared `RecInv` and `CapEntryInv` state invariants for the record loop. -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Shared Record-Loop & Cap-Entry Invariants -/

/-- Persistent 20-register invariant at the start of every record iteration `rec_r`. -/
structure RecRegs (positions : Positions) (ordinal : Nat) (s : MachineState) : Prop where
  rx1 : s.getReg .x1 = BitVec.ofNat 64 (4294971424 + levelBase 1)
  rx2 : s.getReg .x2 = BitVec.ofNat 64 (4294971424 + levelBase 2)
  rx3 : s.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11)
  rx4 : s.getReg .x4 = 1#64
  rx7 : s.getReg .x7 = BitVec.ofNat 64 (4294971424 + levelBase 10)
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx11 : s.getReg .x11 = mask40Word
  rx13 : s.getReg .x13 = BitVec.ofNat 64 5592064
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (4294971424 + levelBase 3)
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952)
  rx19 : s.getReg .x19 = BitVec.ofNat 64 1364
  rx20 : s.getReg .x20 = BitVec.ofNat 64 3
  rx21 : s.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4)
  rx23 : s.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9)
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ordinal)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 (4294971424 + levelBase 5)
  rx27 : s.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card)
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (4294971424 + levelBase 6)
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7)
  rx31 : s.getReg .x31 = BitVec.ofNat 64 (4294971424 + levelBase 8)

/-- Full machine invariant at `pcRec r` before processing record `ordinal`. -/
structure RecInv (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (r : Fin 8) (base : Nat) (written : List Byte)
    (tails : List (BitVec 6)) (flushes : Nat) (tblInit : Bool) (s : MachineState) : Prop where
  hpc : s.pc = pcAt (pcRec r)
  regs : RecRegs positions ordinal s
  hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s
  hbt : BaseTableReady s
  hcm : CapMarks15State s positions ordinal
  htbl : SlowTablesState s tblInit
  hw : WriterState (CleanTrapdoor trapdoor) s r false base 0 written
  ht : TailState (CleanTrapdoor trapdoor) s tails flushes

/-- Machine invariant upon jumping to `PC_cap_pass = 6793` after all records complete. -/
structure CapEntryInv (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions)
    (r : Fin 8) (base : Nat) (written : List Byte)
    (tails : List (BitVec 6)) (flushes : Nat) (s : MachineState) : Prop where
  hpc : s.pc = pcAt PC_cap_pass
  rx4 : s.getReg .x4 = 1#64
  rx11 : s.getReg .x11 = mask40Word
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r.val)
  hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s
  hbt : BaseTableReady s
  hcm : CapMarks15State s positions positions.card
  hw : WriterState (CleanTrapdoor trapdoor) s r false base 0 written
  ht : TailState (CleanTrapdoor trapdoor) s tails flushes

/-- Machine state at `PC_slow_body = 4488` right after `slow_stub_r{r0}` has copied the 24-byte salt. -/
structure SlowEntryInv (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (r0 : Fin 8) (base : Nat) (written : List Byte)
    (tails : List (BitVec 6)) (flushes : Nat) (tblInit : Bool) (i : Index) (s : MachineState) : Prop where
  hpc : s.pc = pcAt PC_slow_body
  rx1 : s.getReg .x1 = BitVec.ofNat 64 (4294971424 + levelBase 1)
  rx2 : s.getReg .x2 = BitVec.ofNat 64 (4294971424 + levelBase 2)
  rx3 : s.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11)
  rx4 : s.getReg .x4 = 1#64
  rx6 : s.getReg .x6 = BitVec.ofNat 64 (3 * (i.val / 3))
  rx7 : s.getReg .x7 = BitVec.ofNat 64 (4294971424 + levelBase 10)
  rx8 : s.getReg .x8 = BitVec.ofNat 64 (i.val % 3)
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx11 : s.getReg .x11 = mask40Word
  rx13 : s.getReg .x13 = BitVec.ofNat 64 5592064
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r0.val)
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952)
  rx19 : s.getReg .x19 = BitVec.ofNat 64 1364
  rx20 : s.getReg .x20 = BitVec.ofNat 64 3
  rx21 : s.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4)
  rx22 : s.getReg .x22 = BitVec.ofNat 64 (i.val / 3)
  rx23 : s.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9)
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ordinal)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 (4294971424 + levelBase 5)
  rx27 : s.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card)
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (4294971424 + levelBase 6)
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7)
  rx31 : s.getReg .x31 = BitVec.ofNat 64 (4294971424 + levelBase 8)
  hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s
  hbt : BaseTableReady s
  hcm : CapMarks15State s positions ordinal
  htbl : SlowTablesState s tblInit
  hw : WriterState (CleanTrapdoor trapdoor) s r0 false (base + 24) 0
         (written ++ bitsToBytes (tdSalt trapdoor i) 24)
  ht : TailState (CleanTrapdoor trapdoor) s tails flushes

/-! ### 2. Subroutine Call & Finish Helpers -/

theorem call_ld_jalr {s : MachineState} {pc tblOff tgt : Nat} {r : Fin 8}
    (hi0 : openInstr pc = .base (.LD .x6 .x14 (BitVec.ofNat 12 tblOff)))
    (hi1 : openInstr (pc + 1) = .base (.JALR .x1 .x6 (0#12)))
    (hbd : pc + 2 ≤ OPEN_CODE_LEN)
    (htbl_off : tblOff + 64 < 2048) (htbl_al : tblOff % 8 = 0)
    (hpc : s.pc = pcAt pc)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r.val))
    (hmem : s.getMem (BitVec.ofNat 64 (tblOff + 8 * r.val)) = pcAt tgt) :
    ∃ s' : MachineState,
      OpenRuns s 2 2 s' ∧
      s'.pc = pcAt tgt ∧
      s'.getReg .x1 = pcAt (pc + 2) ∧
      RegsEqExcept [.x1, .x6] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hr := r.isLt
  have haddr : s.getReg .x14 + signExtend12 (BitVec.ofNat 12 tblOff) = BitVec.ofNat 64 (tblOff + 8 * r.val) := by
    rw [hx14, signExtend12_nonneg tblOff (by omega), ← BitVec.ofNat_add]; congr 1; omega
  have hval : accessValid (s.getReg .x14 + signExtend12 (BitVec.ofNat 12 tblOff)) 8 = true := by
    rw [haddr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
  have h0 := step_LD (s := s) (by omega) hpc hi0 hval
  set s1 := (s.setReg .x6 (s.getMem (s.getReg .x14 + signExtend12 (BitVec.ofNat 12 tblOff)))).setPC (pcAt (pc + 1))
  have hx6 : s1.getReg .x6 = pcAt tgt := by simp [s1, haddr, hmem]
  have h1 := step_JALR (s := s1) (by omega) rfl hi1 hx6
  set s2 := (s1.setReg .x1 (pcAt (pc + 1 + 1))).setPC (pcAt tgt)
  refine ⟨s2, h0.trans h1, rfl, by simp [s2], ?_, fun _ => by simp [s2, s1]⟩
  intro reg hreg
  have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
  have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
  simp [s2, s1, getReg_setReg_ne' .x1 reg h1'.symm, getReg_setReg_ne' .x6 reg h6'.symm]

theorem proofWrite_pres_low {s s' : MachineState} (hp : ProofWritePreserves s s') :
    (∀ a : Word, a.toNat < 512 → s'.getMem a = s.getMem a) ∧
    (∀ a : Word, 512 ≤ a.toNat → a.toNat < 1344 → s'.getMem a = s.getMem a) ∧
    (∀ a : Word, 1344 ≤ a.toNat → a.toNat < 1792 → s'.getMem a = s.getMem a) :=
  ⟨fun a h => hp a (by omega), fun a h1 h2 => hp a (by omega), fun a h1 h2 => hp a (by omega)⟩

theorem tailWrite_pres_low {s s' : MachineState} (ht : TailWritePreserves s s') :
    (∀ a : Word, a.toNat < 512 → s'.getMem a = s.getMem a) ∧
    (∀ a : Word, 512 ≤ a.toNat → a.toNat < 1344 → s'.getMem a = s.getMem a) ∧
    (∀ a : Word, 1344 ≤ a.toNat → a.toNat < 1792 → s'.getMem a = s.getMem a) := by
  have htbb : tailBufBase = 20000000000 := rfl
  exact ⟨fun a h => ht a (by omega), fun a h1 h2 => ht a (by omega), fun a h1 h2 => ht a (by omega)⟩

theorem setByte_cap_pres {s : MachineState} {c : Nat} (hc : c < 342) :
    (∀ a : Word, ¬ (512 ≤ a.toNat ∧ a.toNat < 1344) →
      (s.setByte (BitVec.ofNat 64 (512 + c)) 1#8).getMem a = s.getMem a) := by
  intro a ha
  have hal := alignToDword_ofNat_eq (8 * ((512 + c) / 8)) ((512 + c) % 8) (by omega) (by omega)
  rw [show 8 * ((512 + c) / 8) + (512 + c) % 8 = 512 + c by omega] at hal
  simp only [MachineState.setByte]
  apply MachineState.getMem_setMem_ne
  rw [hal]; intro h; apply ha
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- Shared slow-path exit epilogue: `SB x22, x4, 512; ADDI x24, x24, 8; BNE x24, x27, 8; JAL cap_pass; ...`.
Handles both `sm_done` (`4793`, restore `x1, x14, x19`, `8` cyc continue / `4` cyc cap) and
`st_done` (`4908`, restore `x1, x2, x14, x19`, `9` cyc continue / `4` cyc cap). -/
theorem openRuns_slow_epilogue {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {rEnd : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    {isTail : Bool}
    (hord : ordinal < positions.card)
    (hpc : s.pc = pcAt (if isTail then 4908 else 4793))
    (hx2 : isTail = false → s.getReg .x2 = BitVec.ofNat 64 (4294971424 + levelBase 2))
    (hx3 : s.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11))
    (hx4 : s.getReg .x4 = 1#64)
    (hx7 : s.getReg .x7 = BitVec.ofNat 64 (4294971424 + levelBase 10))
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx11 : s.getReg .x11 = mask40Word)
    (hx13 : s.getReg .x13 = BitVec.ofNat 64 5592064)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * rEnd.val))
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952))
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 3)
    (hx21 : s.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (capLeafOf ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord]))))
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9))
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ordinal))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 (4294971424 + levelBase 5))
    (hx27 : s.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (4294971424 + levelBase 6))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7))
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 (4294971424 + levelBase 8))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hbt : BaseTableReady s)
    (hcm : CapMarks15State s positions ordinal)
    (htbl : SlowTablesState s true)
    (hw : WriterState (CleanTrapdoor trapdoor) s rEnd false base 0 written)
    (ht : TailState (CleanTrapdoor trapdoor) s tails flushes) :
    let cyc := if ordinal + 1 = positions.card then 4 else if isTail then 9 else 8
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      if hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd base written tails flushes s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd base written tails flushes true s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  have hcard := positions_card_le' positions
  have hcl_lt : capLeafOf i < 342 := by
    unfold capLeafOf; have hi : i.val < 16777216 := i.isLt
    simp only [Nat.shiftRight_eq_div_pow]; omega
  set pc0 := if isTail then 4908 else 4793
  have hi0 : openInstr pc0 = .base (.SB .x22 .x4 (512#12)) := by cases isTail <;> dsimp [pc0] <;> rfl
  have hi1 : openInstr (pc0 + 1) = .base (.ADDI .x24 .x24 (8#12)) := by cases isTail <;> dsimp [pc0] <;> rfl
  have hi2 : openInstr (pc0 + 2) = .base (.BNE .x24 .x27 (8#13)) := by cases isTail <;> dsimp [pc0] <;> rfl
  have hbd0 : pc0 + 10 ≤ OPEN_CODE_LEN := by cases isTail <;> dsimp [pc0] <;> decide
  have hsb_addr : s.getReg .x22 + signExtend12 (512#12) = BitVec.ofNat 64 (512 + capLeafOf i) := by
    rw [hx22, signExtend12_nonneg 512 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
  have hsb_val : accessValid (s.getReg .x22 + signExtend12 (512#12)) 1 = true := by
    rw [hsb_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
  have h0 := step_SB (s := s) (by omega) hpc hi0 hsb_val
  set s1 := (s.setByte (s.getReg .x22 + signExtend12 (512#12)) ((s.getReg .x4).truncate 8)).setPC (pcAt (pc0 + 1))
  have h1 := step_ADDI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x24 (s1.getReg .x24 + signExtend12 (8#12))).setPC (pcAt (pc0 + 1 + 1))
  have hs2_24 : s2.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ordinal + 1)) := by
    simp only [s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      getReg_setByte, hx24, signExtend12_nonneg 8 (by omega), ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64); omega
  have hs2_27 : s2.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card) := by
    simp [s2, s1, getReg_setReg_ne', hx27]
  have hmem2 : ∀ a : Word, ¬ (512 ≤ a.toNat ∧ a.toNat < 1344) → s2.getMem a = s.getMem a := by
    intro a ha
    simp only [s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsb_addr, hx4,
      show (1#64 : Word).truncate 8 = 1#8 from rfl]
    exact setByte_cap_pres hcl_lt a ha
  have hro2 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s2 :=
    fun a ha => (hmem2 a (by omega)).trans (hro a ha)
  have hbt2 : BaseTableReady s2 := baseTableReady_of_lowEq hbt (fun a ha => hmem2 a (by omega))
  have htbl2 : SlowTablesState s2 true := slowTablesState_of_eq htbl (fun a h1 h2 => hmem2 a (by omega))
  have hcm2 : CapMarks15State s2 positions (ordinal + 1) := by
    have hc := capMarks15_set_mark hord hcm
    refine ⟨fun c hcl => ?_, fun q hq1 hq2 => ?_⟩
    · simp only [s2, s1, getByte_setPC, getByte_setReg, hsb_addr, hx4, show (1#64 : Word).truncate 8 = 1#8 from rfl]
      exact hc.l15 c hcl
    · simp only [s2, s1, getByte_setPC, getByte_setReg, hsb_addr, hx4, show (1#64 : Word).truncate 8 = 1#8 from rfl]
      exact hc.hiZero q hq1 hq2
  have hw2 : WriterState (CleanTrapdoor trapdoor) s2 rEnd false base 0 written := by
    have hbyte : ∀ q < 8556390424, s2.getByte (BitVec.ofNat 64 (11341403200 + q)) = s.getByte (BitVec.ofNat 64 (11341403200 + q)) := by
      intro q hq; simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
      have hal := alignToDword_ofNat_eq (8 * ((11341403200 + q) / 8)) ((11341403200 + q) % 8) (by omega) (by omega)
      rw [show 8 * ((11341403200 + q) / 8) + (11341403200 + q) % 8 = 11341403200 + q by omega] at hal
      apply hmem2; rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    refine ⟨hw.hbase8, hw.hdst8, hw.hlen, hw.hbound, by simp [s2, s1, getReg_setReg_ne', hw.rx25], by simp,
      fun hcl j hj => by have h1 := hw.hlen; have h2 := hw.hbound; rw [hbyte j (by omega)]; exact hw.hbytes hcl j hj, fun hcl => ?_⟩
    have hrem := hw.hrem hcl; simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
    by_cases hr0 : rEnd.val = 0
    · simp [hr0]
    · simp only [hr0, ↓reduceIte] at hrem ⊢
      have h12 : s2.getReg .x12 = s.getReg .x12 := by simp [s2, s1, getReg_setReg_ne']
      rw [h12]; exact hrem
  have ht2 : TailState (CleanTrapdoor trapdoor) s2 tails flushes := by
    refine ⟨ht.hbits, ht.hbound, by simp [s2, s1, getReg_setReg_ne', ht.rx15], by simp [s2, s1, getReg_setReg_ne', ht.rx17], fun hcl => ?_⟩
    obtain ⟨tBuf, hlt, hx16', hsum⟩ := ht.hdata hcl
    refine ⟨tBuf, hlt, by simp [s2, s1, getReg_setReg_ne', hx16'], ?_⟩
    have hmap : ((List.range (8 * flushes)).map fun j => s2.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
        ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) := by
      apply List.map_congr_left; intro j hj; have hjlt := List.mem_range.mp hj
      have htbb : tailBufBase = 20000000000 := rfl; have hbd := ht.hbound
      simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
      have hal := alignToDword_ofNat_eq (8 * ((tailBufBase + j) / 8)) ((tailBufBase + j) % 8) (by omega) (by omega)
      rw [show 8 * ((tailBufBase + j) / 8) + (tailBufBase + j) % 8 = tailBufBase + j by omega] at hal
      apply hmem2; rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hmap]; exact hsum
  by_cases hlast : ordinal + 1 = positions.card
  · have heq24 : s2.getReg .x24 = s2.getReg .x27 := by rw [hs2_24, hs2_27, hlast]
    have h2 := step_BNE_not_taken (s := s2) (by omega) (by congr 1) hi2 heq24
    set s3 := s2.setPC (pcAt (pc0 + 2 + 1))
    have hjal_ins : openInstr (pc0 + 3) = .base (.JAL .x0 (if isTail then 7528#21 else 7988#21)) := by
      cases isTail <;> dsimp [pc0] <;> rfl
    have hjal_tgt : pcAt (pc0 + 3) + signExtend21 (if isTail then 7528#21 else 7988#21) = pcAt PC_cap_pass := by
      cases isTail <;> dsimp [pc0]
      · simpa only [show 4 * (PC_cap_pass - (4793 + 3)) = 7988 by decide] using pcAt_add_pos21 (4793 + 3) PC_cap_pass (by decide) (by decide)
      · simpa only [show 4 * (PC_cap_pass - (4908 + 3)) = 7528 by decide] using pcAt_add_pos21 (4908 + 3) PC_cap_pass (by decide) (by decide)
    have h3 := step_JAL (s := s3) (by omega) (by congr 1) hjal_ins hjal_tgt
    set s4 := (s3.setReg .x0 (pcAt (pc0 + 3 + 1))).setPC (pcAt PC_cap_pass)
    simp only [hlast, ↓reduceIte, ↓reduceDIte]
    refine ⟨s4, ((h0.trans h1).trans h2).trans h3, rfl,
      by simp [s4, s3, s2, s1, getReg_setReg_ne', hx4],
      by simp [s4, s3, s2, s1, getReg_setReg_ne', hx11],
      by simp [s4, s3, s2, s1, getReg_setReg_ne', hx14],
      fun a ha => (by simp [s4, s3] : s4.getMem a = s2.getMem a).trans (hro2 a ha),
      baseTableReady_of_lowEq hbt2 (fun a _ => by simp [s4, s3]),
      by rw [← hlast]; exact capMarks15State_of_lowEq hcm2 (fun a _ _ => by simp [s4, s3]),
      writerState_of_mem_eq hw2 (fun _ => by simp [s4, s3]) (by simp [s4, s3, getReg_setReg_ne']) (by simp [s4, s3, getReg_setReg_ne']),
      TailState.of_proofWrite ht2 (fun _ _ => by simp [s4, s3]) (by simp [s4, s3, getReg_setReg_ne']) (by simp [s4, s3, getReg_setReg_ne']) (by simp [s4, s3, getReg_setReg_ne'])⟩
  · have hne24 : s2.getReg .x24 ≠ s2.getReg .x27 := by
      rw [hs2_24, hs2_27]; intro h; have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 6912218176 + 8 * (ordinal + 1) < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 6912218176 + 8 * positions.card < 2 ^ 64)] at hn; omega
    have hbr2 : pcAt (pc0 + 2) + signExtend13 (8#13) = pcAt (pc0 + 4) := by
      simpa only [show 4 * (pc0 + 4 - (pc0 + 2)) = 8 by omega] using pcAt_add_pos13 (pc0 + 2) (pc0 + 4) (by omega) (by omega)
    have h2 := step_BNE_taken (s := s2) (by omega) (by congr 1) hi2 hne24 hbr2
    set s3 := s2.setPC (pcAt (pc0 + 4))
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 (8 * rEnd.val) := by simp [s3, s2, s1, getReg_setReg_ne', hx14]
    have hrec_addr : s3.getReg .x14 + signExtend12 (1536#12) = BitVec.ofNat 64 (1536 + 8 * rEnd.val) := by
      rw [hs3_14, signExtend12_nonneg 1536 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have hrec_val : accessValid (s3.getReg .x14 + signExtend12 (1536#12)) 8 = true := by
      have := rEnd.isLt; rw [hrec_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
    have hld_val : ∀ k (hk : k < 2048), k % 8 = 0 → accessValid (0#64 + signExtend12 (BitVec.ofNat 12 k)) 8 = true :=
      fun k hk hal => by rw [signExtend12_nonneg k hk, BitVec.zero_add]; exact accessValid_ofNat k 8 (by omega) hal
    have htbl_rec : s3.getMem (BitVec.ofNat 64 (1536 + 8 * rEnd.val)) = pcAt (pcRec rEnd) := by
      unfold SlowTablesState at htbl2; simp only [↓reduceIte] at htbl2; simpa [s3] using (htbl2 rEnd).2.2.2.1
    cases isTail with
    | false =>
      simp only [hlast, ↓reduceIte, ↓reduceDIte, Bool.false_eq_true]
      have h3 := step_LD (s := s3) (by decide) rfl (rfl : openInstr 4797 = .base (.LD .x6 .x14 (1536#12))) hrec_val
      set s4 := (s3.setReg .x6 (s3.getMem (s3.getReg .x14 + signExtend12 (1536#12)))).setPC (pcAt 4798)
      have h4 := step_LD (s := s4) (by decide) rfl (rfl : openInstr 4798 = .base (.LD .x1 .x0 (8#12))) (hld_val 8 (by omega) (by omega))
      set s5 := (s4.setReg .x1 (s4.getMem (s4.getReg .x0 + signExtend12 (8#12)))).setPC (pcAt 4799)
      have h5 := step_LD (s := s5) (by decide) rfl (rfl : openInstr 4799 = .base (.LD .x14 .x0 (24#12))) (hld_val 24 (by omega) (by omega))
      set s6 := (s5.setReg .x14 (s5.getMem (s5.getReg .x0 + signExtend12 (24#12)))).setPC (pcAt 4800)
      have h6 := step_ADDI (s := s6) (by decide) rfl (rfl : openInstr 4800 = .base (.ADDI .x19 .x0 (1364#12)))
      set s7 := (s6.setReg .x19 (s6.getReg .x0 + signExtend12 (1364#12))).setPC (pcAt 4801)
      have hs7_6 : s7.getReg .x6 = pcAt (pcRec rEnd) := by simp [s7, s6, s5, s4, getReg_setReg_ne', hrec_addr, htbl_rec]
      have h7 := step_JALR (s := s7) (by decide) rfl (rfl : openInstr 4801 = .base (.JALR .x0 .x6 (0#12))) hs7_6
      set s8 := (s7.setReg .x0 (pcAt 4802)).setPC (pcAt (pcRec rEnd))
      have hmem8 : ∀ a, s8.getMem a = s2.getMem a := fun a => by simp [s8, s7, s6, s5, s4, s3]
      refine ⟨s8, ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7,
        rfl,
        ⟨by
           have e : s8.getReg .x1 = s4.getMem (s4.getReg .x0 + signExtend12 (8#12)) := by
             simp [s8, s7, s6, s5, getReg_setReg_ne']
           rw [e, show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 8 (by omega), BitVec.zero_add]
           have hm : s4.getMem (BitVec.ofNat 64 8) = s2.getMem (BitVec.ofNat 64 8) := by simp [s4, s3]
           rw [hm]; exact hbt2.lvlBase 1 (by omega) (by omega),
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx2 rfl],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx3],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx4],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx7],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx9],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx11],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx13],
         by
           have e : s8.getReg .x14 = s5.getMem (s5.getReg .x0 + signExtend12 (24#12)) := by
             simp [s8, s7, s6, getReg_setReg_ne']
           rw [e, show s5.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 24 (by omega), BitVec.zero_add]
           have hm : s5.getMem (BitVec.ofNat 64 24) = s2.getMem (BitVec.ofNat 64 24) := by simp [s5, s4, s3]
           rw [hm]; exact hbt2.lvlBase 3 (by omega) (by omega),
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx18],
         by
           have e : s8.getReg .x19 = s6.getReg .x0 + signExtend12 (1364#12) := by
             simp [s8, s7, getReg_setReg_ne']
           rw [e, show s6.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1364 (by omega), BitVec.zero_add],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx20],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx21],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx23],
         by simp [s8, s7, s6, s5, s4, s3, getReg_setReg_ne', hs2_24],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx26],
         by simp [s8, s7, s6, s5, s4, s3, getReg_setReg_ne', hs2_27],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx29],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx30],
         by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx31]⟩,
        fun a ha => (hmem8 a).trans (hro2 a ha),
        baseTableReady_of_lowEq hbt2 (fun a _ => hmem8 a),
        capMarks15State_of_lowEq hcm2 (fun a _ _ => hmem8 a),
        slowTablesState_of_eq htbl2 (fun a _ _ => hmem8 a),
        writerState_of_mem_eq hw2 hmem8 (by simp [s8, s7, s6, s5, s4, s3, getReg_setReg_ne']) (by simp [s8, s7, s6, s5, s4, s3, getReg_setReg_ne']),
        TailState.of_proofWrite ht2 (fun a _ => hmem8 a) (by simp [s8, s7, s6, s5, s4, s3, getReg_setReg_ne']) (by simp [s8, s7, s6, s5, s4, s3, getReg_setReg_ne']) (by simp [s8, s7, s6, s5, s4, s3, getReg_setReg_ne'])⟩
    | true =>
      simp only [hlast, ↓reduceIte, ↓reduceDIte]
      have h3 := step_LD (s := s3) (by decide) rfl (rfl : openInstr 4912 = .base (.LD .x6 .x14 (1536#12))) hrec_val
      set s4 := (s3.setReg .x6 (s3.getMem (s3.getReg .x14 + signExtend12 (1536#12)))).setPC (pcAt 4913)
      have h4 := step_LD (s := s4) (by decide) rfl (rfl : openInstr 4913 = .base (.LD .x1 .x0 (8#12))) (hld_val 8 (by omega) (by omega))
      set s5 := (s4.setReg .x1 (s4.getMem (s4.getReg .x0 + signExtend12 (8#12)))).setPC (pcAt 4914)
      have h5 := step_LD (s := s5) (by decide) rfl (rfl : openInstr 4914 = .base (.LD .x2 .x0 (16#12))) (hld_val 16 (by omega) (by omega))
      set s6 := (s5.setReg .x2 (s5.getMem (s5.getReg .x0 + signExtend12 (16#12)))).setPC (pcAt 4915)
      have h6 := step_LD (s := s6) (by decide) rfl (rfl : openInstr 4915 = .base (.LD .x14 .x0 (24#12))) (hld_val 24 (by omega) (by omega))
      set s7 := (s6.setReg .x14 (s6.getMem (s6.getReg .x0 + signExtend12 (24#12)))).setPC (pcAt 4916)
      have h7 := step_ADDI (s := s7) (by decide) rfl (rfl : openInstr 4916 = .base (.ADDI .x19 .x0 (1364#12)))
      set s8 := (s7.setReg .x19 (s7.getReg .x0 + signExtend12 (1364#12))).setPC (pcAt 4917)
      have hs8_6 : s8.getReg .x6 = pcAt (pcRec rEnd) := by simp [s8, s7, s6, s5, s4, getReg_setReg_ne', hrec_addr, htbl_rec]
      have h8 := step_JALR (s := s8) (by decide) rfl (rfl : openInstr 4917 = .base (.JALR .x0 .x6 (0#12))) hs8_6
      set s9 := (s8.setReg .x0 (pcAt 4918)).setPC (pcAt (pcRec rEnd))
      have hmem9 : ∀ a, s9.getMem a = s2.getMem a := fun a => by simp [s9, s8, s7, s6, s5, s4, s3]
      refine ⟨s9, (((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8,
        rfl,
        ⟨by
           have e : s9.getReg .x1 = s4.getMem (s4.getReg .x0 + signExtend12 (8#12)) := by
             simp [s9, s8, s7, s6, s5, getReg_setReg_ne']
           rw [e, show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 8 (by omega), BitVec.zero_add]
           have hm : s4.getMem (BitVec.ofNat 64 8) = s2.getMem (BitVec.ofNat 64 8) := by simp [s4, s3]
           rw [hm]; exact hbt2.lvlBase 1 (by omega) (by omega),
         by
           have e : s9.getReg .x2 = s5.getMem (s5.getReg .x0 + signExtend12 (16#12)) := by
             simp [s9, s8, s7, s6, getReg_setReg_ne']
           rw [e, show s5.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega), BitVec.zero_add]
           have hm : s5.getMem (BitVec.ofNat 64 16) = s2.getMem (BitVec.ofNat 64 16) := by simp [s5, s4, s3]
           rw [hm]; exact hbt2.lvlBase 2 (by omega) (by omega),
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx3],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx4],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx7],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx9],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx11],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx13],
         by
           have e : s9.getReg .x14 = s6.getMem (s6.getReg .x0 + signExtend12 (24#12)) := by
             simp [s9, s8, s7, getReg_setReg_ne']
           rw [e, show s6.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 24 (by omega), BitVec.zero_add]
           have hm : s6.getMem (BitVec.ofNat 64 24) = s2.getMem (BitVec.ofNat 64 24) := by simp [s6, s5, s4, s3]
           rw [hm]; exact hbt2.lvlBase 3 (by omega) (by omega),
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx18],
         by
           have e : s9.getReg .x19 = s7.getReg .x0 + signExtend12 (1364#12) := by
             simp [s9, s8, getReg_setReg_ne']
           rw [e, show s7.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1364 (by omega), BitVec.zero_add],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx20],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx21],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx23],
         by simp [s9, s8, s7, s6, s5, s4, s3, getReg_setReg_ne', hs2_24],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx26],
         by simp [s9, s8, s7, s6, s5, s4, s3, getReg_setReg_ne', hs2_27],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx29],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx30],
         by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx31]⟩,
        fun a ha => (hmem9 a).trans (hro2 a ha),
        baseTableReady_of_lowEq hbt2 (fun a _ => hmem9 a),
        capMarks15State_of_lowEq hcm2 (fun a _ _ => hmem9 a),
        slowTablesState_of_eq htbl2 (fun a _ _ => hmem9 a),
        writerState_of_mem_eq hw2 hmem9 (by simp [s9, s8, s7, s6, s5, s4, s3, getReg_setReg_ne']) (by simp [s9, s8, s7, s6, s5, s4, s3, getReg_setReg_ne']),
        TailState.of_proofWrite ht2 (fun a _ => hmem9 a) (by simp [s9, s8, s7, s6, s5, s4, s3, getReg_setReg_ne']) (by simp [s9, s8, s7, s6, s5, s4, s3, getReg_setReg_ne']) (by simp [s9, s8, s7, s6, s5, s4, s3, getReg_setReg_ne'])⟩

/-! ### 3. `slow_mid` (`4660..4801`) and `slow_tail` (`4802..4917`) Execution -/

theorem reg_not_mem_sub {l1 l2 : List Reg} (h : ∀ r ∈ l1, r ∈ l2) {r : Reg} (hr : r ∉ l2) : r ∉ l1 :=
  fun hm => hr (h r hm)

private theorem bv64_and2_eq_zero_iff (n : Nat) (_hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n &&& signExtend12 (2#12) = 0#64) ↔ n % 4 < 2 := by
  rw [signExtend12_nonneg 2 (by omega)]
  have htb1 : n.testBit 1 = decide (n / 2 % 2 = 1) := by
    simpa [Nat.pow_one] using (@Nat.testBit_eq_decide_div_mod_eq 1 n)
  constructor
  · intro h
    have ht := congrArg (fun w : Word => w.getLsbD 1) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.zero_testBit,
      show (1 : Nat) < 64 by omega, decide_true, Bool.true_and,
      show Nat.testBit 2 1 = true by decide, Bool.and_true, htb1] at ht
    rw [decide_eq_false_iff_not] at ht; omega
  · intro hlt
    apply BitVec.eq_of_getLsbD_eq; intro b hb
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.zero_testBit, hb, decide_true, Bool.true_and]
    by_cases hb1 : b = 1
    · subst hb1
      simp only [show Nat.testBit 2 1 = true by decide, Bool.and_true, htb1, decide_eq_false_iff_not]; omega
    · have h2b : Nat.testBit 2 b = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
        rcases eq_or_ne b 0 with rfl | hb0
        · decide
        · have hpow : 4 ≤ 2 ^ b := by
            have h1 := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (show 2 ≤ b by omega)
            have h2 : (2 : Nat) ^ 2 = 4 := by decide
            omega
          rw [Nat.div_eq_of_lt (by omega : 2 < 2 ^ b)]; omega
      rw [h2b, Bool.and_false]

theorem capLeafOf_eq_div16384 (i : Index) : capLeafOf i = (i.val / 3) >>> 14 := rfl

theorem div2_eq_ushr (a k : Nat) : (a >>> k) / 2 = a >>> (k + 1) := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

theorem div2_ushr_eq (a k k' : Nat) (h : k + 1 = k' := by rfl) : (a >>> k) / 2 = a >>> k' := by
  subst h; exact div2_eq_ushr a k

theorem bv64_ult_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  have hp : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  rw [hp] at ha hb
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem openRuns_load_opening_db {s : MachineState}
    (hpc : s.pc = pcAt 4802) :
    ∃ s' : MachineState,
      OpenRuns s 7 7 s' ∧
      s'.pc = pcAt 4809 ∧
      s'.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      RegsEqExcept [.x2] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have h0 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 4802 = .base (.ADDI .x2 .x0 (7#12)))
  set s1 := (s.setReg .x2 (s.getReg .x0 + signExtend12 (7#12))).setPC (pcAt 4803)
  have h1 := step_SLLI (s := s1) (by decide) rfl (rfl : openInstr 4803 = .base (.SLLI .x2 .x2 (11#6)))
  set s2 := (s1.setReg .x2 (s1.getReg .x2 <<< (11#6).toNat)).setPC (pcAt 4804)
  have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 4804 = .base (.ADDI .x2 .x2 (2047#12)))
  set s3 := (s2.setReg .x2 (s2.getReg .x2 + signExtend12 (2047#12))).setPC (pcAt 4805)
  have h3 := step_SLLI (s := s3) (by decide) rfl (rfl : openInstr 4805 = .base (.SLLI .x2 .x2 (11#6)))
  set s4 := (s3.setReg .x2 (s3.getReg .x2 <<< (11#6).toNat)).setPC (pcAt 4806)
  have h4 := step_ADDI (s := s4) (by decide) rfl (rfl : openInstr 4806 = .base (.ADDI .x2 .x2 (2047#12)))
  set s5 := (s4.setReg .x2 (s4.getReg .x2 + signExtend12 (2047#12))).setPC (pcAt 4807)
  have h5 := step_SLLI (s := s5) (by decide) rfl (rfl : openInstr 4807 = .base (.SLLI .x2 .x2 (11#6)))
  set s6 := (s5.setReg .x2 (s5.getReg .x2 <<< (11#6).toNat)).setPC (pcAt 4808)
  have h6 := step_ADDI (s := s6) (by decide) rfl (rfl : openInstr 4808 = .base (.ADDI .x2 .x2 (1248#12)))
  set s7 := (s6.setReg .x2 (s6.getReg .x2 + signExtend12 (1248#12))).setPC (pcAt 4809)
  refine ⟨s7, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6, rfl, ?_, ?_, fun _ => by simp [s7, s6, s5, s4, s3, s2, s1]⟩
  · have e1 : s1.getReg .x2 = BitVec.ofNat 64 7 := by simp [s1, show s.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 7 (by omega)]
    have e2 : s2.getReg .x2 = BitVec.ofNat 64 (7 * 2 ^ 11) := by simp [s2, e1, bv64_shl]
    have e3 : s3.getReg .x2 = BitVec.ofNat 64 (7 * 2 ^ 11 + 2047) := by simp [s3, e2, signExtend12_nonneg 2047 (by omega), ← BitVec.ofNat_add]
    have e4 : s4.getReg .x2 = BitVec.ofNat 64 ((7 * 2 ^ 11 + 2047) * 2 ^ 11) := by simp [s4, e3, bv64_shl]
    have e5 : s5.getReg .x2 = BitVec.ofNat 64 ((7 * 2 ^ 11 + 2047) * 2 ^ 11 + 2047) := by simp [s5, e4, signExtend12_nonneg 2047 (by omega), ← BitVec.ofNat_add]
    have e6 : s6.getReg .x2 = BitVec.ofNat 64 (((7 * 2 ^ 11 + 2047) * 2 ^ 11 + 2047) * 2 ^ 11) := by simp [s6, e5, bv64_shl]
    simp only [s7, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      e6, signExtend12_nonneg 1248 (by omega), ← BitVec.ofNat_add]; rfl
  · intro reg hreg; have h2' : reg ≠ .x2 := fun h => hreg (by simp [h])
    simp [s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne' .x2 reg h2'.symm]

private def slowMidPreCyc (r0 : Fin 8) (cL0 : Nat) : Nat :=
  cL0 + 6 + 2 + (copy32x3SubCode r0).length + 5 + 6 + 5 + 5 + 2 + (copy30x4SubCode r0).length +
    5 + 5 + 2 + (copy29x2SubCode r0).length + 2

private theorem slowTbl_get' {s' : MachineState} (hs' : SlowTablesState s' true) (r : Fin 8) :
    s'.getMem (BitVec.ofNat 64 (1344 + 8 * r.val)) = pcAt (pcCopy29 r) ∧
    s'.getMem (BitVec.ofNat 64 (1408 + 8 * r.val)) = pcAt (pcCopy30 r) ∧
    s'.getMem (BitVec.ofNat 64 (1472 + 8 * r.val)) = pcAt (pcCopy32 r) ∧
    s'.getMem (BitVec.ofNat 64 (1536 + 8 * r.val)) = pcAt (pcRec r) ∧
    s'.getMem (BitVec.ofNat 64 (1600 + 8 * r.val)) = pcAt (pcCopy32x3 r) ∧
    s'.getMem (BitVec.ofNat 64 (1664 + 8 * r.val)) = pcAt (pcCopy30x4 r) ∧
    s'.getMem (BitVec.ofNat 64 (1728 + 8 * r.val)) = pcAt (pcCopy29x2 r) := by
  unfold SlowTablesState at hs'; simp only [↓reduceIte] at hs'; exact hs' r

/-- Prefix of `slow_mid` (`4660 → 4713`): `L0..L7` copied, `x5 = (g >>> 7) &&& 2`, `x22 = g >>> 7`. -/
private theorem openRuns_slow_mid_prefix {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hord : ordinal < positions.card)
    (hbd_w : base + 528 ≤ 8556390424)
    (hg1 : 5592064 ≤ ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)
    (hg2 : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592384)
    (hpc : s.pc = pcAt 4660)
    (hinv : SlowEntryInv trapdoor positions ordinal r0 base written tails flushes true
              ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) (s.setPC (pcAt PC_slow_body))) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let g := i.val / 3
    let r1 := copy29x2NextR r0
    let b1 := base + 24 + 96 + 120 + copy29x2NextDstOff r0
    let w1 := written ++ bitsToBytes (tdSalt trapdoor i) 24 ++
      bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx i)) 32 ++
      bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32 ++
      bitsToBytes (tdNode trapdoor 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29
    ∃ cL0 s7b,
      cL0 ≤ 6 ∧
      OpenRuns s (slowMidPreCyc r0 cL0) (slowMidPreCyc r0 cL0) s7b ∧
      s7b.pc = pcAt 4713 ∧
      s7b.getReg .x5 = BitVec.ofNat 64 (g >>> 7) &&& signExtend12 (2#12) ∧
      s7b.getReg .x14 = BitVec.ofNat 64 (8 * r1.val) ∧
      s7b.getReg .x22 = BitVec.ofNat 64 (g >>> 7) ∧
      (CleanTrapdoor trapdoor → s7b.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))])) ∧
      RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s7b ∧
      ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7b ∧
      BaseTableReady s7b ∧
      SlowTablesState s7b true ∧
      CapMarks15State s7b positions ordinal ∧
      WriterState (CleanTrapdoor trapdoor) s7b r1 false b1 0 w1 ∧
      TailState (CleanTrapdoor trapdoor) s7b tails flushes := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hi_lt : i.val < 16777216 := i.isLt
  have hsm := level_sib_of_slow_mid g hg1 hg2
  have hrx2 : s.getReg .x2 = BitVec.ofNat 64 (4294971424 + levelBase 2) := hinv.rx2
  have hrx4 : s.getReg .x4 = 1#64 := hinv.rx4
  have hrx6 : s.getReg .x6 = BitVec.ofNat 64 (3 * g) := hinv.rx6
  have hrx8 : s.getReg .x8 = BitVec.ofNat 64 (i.val % 3) := hinv.rx8
  have hrx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424 := hinv.rx9
  have hrx11 : s.getReg .x11 = mask40Word := hinv.rx11
  have hrx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r0.val) := hinv.rx14
  have hrx21 : s.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4) := hinv.rx21
  have hrx22 : s.getReg .x22 = BitVec.ofNat 64 g := hinv.rx22
  have hrx26 : s.getReg .x26 = BitVec.ofNat 64 (4294971424 + levelBase 5) := hinv.rx26
  have hrx29 : s.getReg .x29 = BitVec.ofNat 64 (4294971424 + levelBase 6) := hinv.rx29
  have hrx30 : s.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7) := hinv.rx30
  have hro0 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s := hinv.hro
  have hbt0 : BaseTableReady s := baseTableReady_of_lowEq hinv.hbt (fun _ _ => rfl)
  have hcm0 : CapMarks15State s positions ordinal := capMarks15State_of_lowEq hinv.hcm (fun _ _ _ => rfl)
  have htbl0 : SlowTablesState s true := slowTablesState_of_eq hinv.htbl (fun _ _ _ => rfl)
  have hw0 : WriterState (CleanTrapdoor trapdoor) s r0 false (base + 24) 0
      (written ++ bitsToBytes (tdSalt trapdoor i) 24) := writerState_of_mem_eq hinv.hw (fun _ => rfl) rfl rfl
  have ht0 : TailState (CleanTrapdoor trapdoor) s tails flushes := TailState.of_proofWrite hinv.ht (fun _ _ => rfl) rfl rfl rfl
  have hl0a_lt : l0Sib1Idx i < levelSize 0 := by unfold l0Sib1Idx; rw [levelSize_0]; split_ifs <;> omega
  have hl0b_lt : l0Sib2Idx i < levelSize 0 := by unfold l0Sib2Idx; rw [levelSize_0]; split_ifs <;> omega
  have hl1_lt : (g ^^^ 1) < levelSize 1 := by rw [levelSize_1]; exact xor_one_lt_even (m := 2796203) (by omega)
  obtain ⟨cL0, s1, hr1, hcL0, hpc1, hs1_10, hs1_28, hreg1, hmem1⟩ :=
    openRuns_l0_sibs (codeAt_of_list_eq 4660 l0SibsCode (by decide) rfl) hpc hrx4 hrx6 hrx8 hrx9
  obtain ⟨s2, hr2, hpc2, hs2_22, hs2_8, hreg2, hmem2⟩ :=
    openRuns_lvl_addr_inmem (codeAt_of_list_eq 4668 (lvlAddrInMemCode .x8 1) (by decide) rfl)
      hpc1 (by omega) (by omega) (by omega) (by decide) ((hreg1 .x22 (by simp)).trans hrx22)
      (baseTableReady_of_lowEq hbt0 (fun a _ => hmem1 a))
  have hmem20 : ∀ a, s2.getMem a = s.getMem a := fun a => (hmem2 a).trans (hmem1 a)
  obtain ⟨s2c, hr2c, hpc2c, hs2c_1, hreg2c, hmem2c⟩ :=
    call_ld_jalr (r := r0) (tblOff := 1600) (tgt := pcCopy32x3 r0)
      (rfl : openInstr 4674 = .base (.LD .x6 .x14 (1600#12)))
      (rfl : openInstr 4675 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc2
      ((hreg2 .x14 (by simp)).trans ((hreg1 .x14 (by simp)).trans hrx14))
      (by rw [hmem20]; exact (slowTbl_get' htbl0 r0).2.2.2.2.1)
  have hmem2c0 : ∀ a, s2c.getMem a = s.getMem a := fun a => (hmem2c a).trans (hmem20 a)
  have hro2c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s2c :=
    fun a ha => (hmem2c0 a).trans (hro0 a ha)
  have hw2c := writerState_of_mem_eq hw0 hmem2c0
    ((hreg2c .x25 (by simp)).trans ((hreg2 .x25 (by simp)).trans (hreg1 .x25 (by simp))))
    ((hreg2c .x12 (by simp)).trans ((hreg2 .x12 (by simp)).trans (hreg1 .x12 (by simp))))
  obtain ⟨s3, hr3, hpc3, hreg3, hp3, hw3⟩ := openRuns_sub_copy32x3 (r := r0) (retPc := 4676)
    (d0 := tdNode trapdoor 0 (l0Sib1Idx i)) (d1 := tdNode trapdoor 0 (l0Sib2Idx i)) (d2 := tdNode trapdoor 1 (g ^^^ 1))
    hpc2c hs2c_1
    ((hreg2c .x10 (by simp)).trans ((hreg2 .x10 (by simp)).trans hs1_10))
    ((hreg2c .x28 (by simp)).trans ((hreg2 .x28 (by simp)).trans hs1_28))
    ((hreg2c .x8 (by simp)).trans hs2_8)
    (by have h1 := levelBase_align8' 0 (by omega); have h2 := nodeOffset_align8' 0 (l0Sib1Idx i); omega)
    (by have h1 := levelBase_align8' 0 (by omega); have h2 := nodeOffset_align8' 0 (l0Sib2Idx i); omega)
    (by have h1 := levelBase_align8' 1 (by omega); have h2 := nodeOffset_align8' 1 (g ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 0 (l0Sib1Idx i) (by omega) hl0a_lt; omega)
    (by have := nodeOffset_lt_treeBytes' 0 (l0Sib2Idx i) (by omega) hl0b_lt; omega)
    (by have := nodeOffset_lt_treeBytes' 1 (g ^^^ 1) (by omega) hl1_lt; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro2c 0 (l0Sib1Idx i) k (by omega) hl0a_lt hk)
    (fun _ k hk => readOnly_getMem_tdNode hro2c 0 (l0Sib2Idx i) k (by omega) hl0b_lt hk)
    (fun _ k hk => readOnly_getMem_tdNode hro2c 1 (g ^^^ 1) k (by omega) hl1_lt hk)
    (by omega) hw2c
  have hro3 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s3 :=
    ReadOnlyPreserved.of_proofWrite hro2c hp3
  have hbt3 : BaseTableReady s3 := baseTableReady_of_lowEq hbt0 (fun a ha => (hp3 a (by omega)).trans (hmem2c0 a))
  have htbl3 : SlowTablesState s3 true := slowTablesState_of_eq htbl0 (fun a _ _ => (hp3 a (by omega)).trans (hmem2c0 a))
  have hcm3 : CapMarks15State s3 positions ordinal := capMarks15State_of_lowEq hcm0 (fun a _ _ => (hp3 a (by omega)).trans (hmem2c0 a))
  have hreg3_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x22, .x25, .x28] s s3 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg3 reg (by simp [h5', h6', h12', h25'])).trans
      ((hreg2c reg (by simp [h1', h6'])).trans
       ((hreg2 reg (by simp [h5', h22', h8'])).trans (hreg1 reg (by simp [h10', h28']))))
  have hs3_22 : s3.getReg .x22 = BitVec.ofNat 64 (g >>> 1) := by
    have h := (hreg3 .x22 (by simp)).trans ((hreg2c .x22 (by simp)).trans hs2_22)
    simpa only [show g / 2 = g >>> 1 by simp [Nat.shiftRight_eq_div_pow]] using h
  obtain ⟨s4a, hr4a, hpc4a, hs4a_22, hs4a_10, hreg4a, hmem4a⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4676 (lvlAddrInRegCode .x10 .x2) (by decide) rfl)
      hpc3 (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs3_22 ((hreg3_base .x2 (by simp)).trans hrx2)
  rw [div2_ushr_eq g 1 2] at hs4a_22
  obtain ⟨s4b, hr4b, hpc4b, hs4b_22, hs4b_28, hreg4b, hmem4b⟩ :=
    openRuns_lvl_addr_inmem (codeAt_of_list_eq 4681 (lvlAddrInMemCode .x28 3) (by decide) rfl)
      hpc4a (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide)
      hs4a_22 (baseTableReady_of_lowEq hbt3 (fun a _ => hmem4a a))
  rw [div2_ushr_eq g 2 3] at hs4b_22
  obtain ⟨s4c, hr4c, hpc4c, hs4c_22, hs4c_8, hreg4c, hmem4c⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4687 (lvlAddrInRegCode .x8 .x21) (by decide) rfl)
      hpc4b (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs4b_22 ((hreg4b .x21 (by simp)).trans ((hreg4a .x21 (by simp)).trans ((hreg3_base .x21 (by simp)).trans hrx21)))
  rw [div2_ushr_eq g 3 4] at hs4c_22
  obtain ⟨s4d, hr4d, hpc4d, hs4d_22, hs4d_19, hreg4d, hmem4d⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4692 (lvlAddrInRegCode .x19 .x26) (by decide) rfl)
      hpc4c (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs4c_22 ((hreg4c .x26 (by simp)).trans ((hreg4b .x26 (by simp)).trans ((hreg4a .x26 (by simp)).trans ((hreg3_base .x26 (by simp)).trans hrx26))))
  rw [div2_ushr_eq g 4 5] at hs4d_22
  have hmem4d3 : ∀ a, s4d.getMem a = s3.getMem a := fun a => (hmem4d a).trans ((hmem4c a).trans ((hmem4b a).trans (hmem4a a)))
  obtain ⟨s4e, hr4e, hpc4e, hs4e_1, hreg4e, hmem4e⟩ :=
    call_ld_jalr (r := r0) (tblOff := 1664) (tgt := pcCopy30x4 r0)
      (rfl : openInstr 4697 = .base (.LD .x6 .x14 (1664#12)))
      (rfl : openInstr 4698 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc4d
      ((hreg4d .x14 (by simp)).trans ((hreg4c .x14 (by simp)).trans ((hreg4b .x14 (by simp)).trans ((hreg4a .x14 (by simp)).trans ((hreg3_base .x14 (by simp)).trans hrx14)))))
      (by rw [hmem4d3]; exact (slowTbl_get' htbl3 r0).2.2.2.2.2.1)
  have hmem4e3 : ∀ a, s4e.getMem a = s3.getMem a := fun a => (hmem4e a).trans (hmem4d3 a)
  have hro4e : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s4e :=
    fun a ha => (hmem4e3 a).trans (hro3 a ha)
  have hw4e := writerState_of_mem_eq hw3 hmem4e3
    ((hreg4e .x25 (by simp)).trans ((hreg4d .x25 (by simp)).trans ((hreg4c .x25 (by simp)).trans ((hreg4b .x25 (by simp)).trans (hreg4a .x25 (by simp))))))
    ((hreg4e .x12 (by simp)).trans ((hreg4d .x12 (by simp)).trans ((hreg4c .x12 (by simp)).trans ((hreg4b .x12 (by simp)).trans (hreg4a .x12 (by simp))))))
  obtain ⟨s5, hr5, hpc5, hreg5, hp5, hw5⟩ := openRuns_sub_copy30x4 (r := r0) (retPc := 4699)
    (d0 := tdNode trapdoor 2 ((g >>> 1) ^^^ 1)) (d1 := tdNode trapdoor 3 ((g >>> 2) ^^^ 1))
    (d2 := tdNode trapdoor 4 ((g >>> 3) ^^^ 1)) (d3 := tdNode trapdoor 5 ((g >>> 4) ^^^ 1))
    hpc4e hs4e_1
    ((hreg4e .x10 (by simp)).trans ((hreg4d .x10 (by simp)).trans ((hreg4c .x10 (by simp)).trans ((hreg4b .x10 (by simp)).trans hs4a_10))))
    ((hreg4e .x28 (by simp)).trans ((hreg4d .x28 (by simp)).trans ((hreg4c .x28 (by simp)).trans hs4b_28)))
    ((hreg4e .x8 (by simp)).trans ((hreg4d .x8 (by simp)).trans hs4c_8))
    ((hreg4e .x19 (by simp)).trans hs4d_19)
    (by have h1 := levelBase_align8' 2 (by omega); have h2 := nodeOffset_align8' 2 ((g >>> 1) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 3 (by omega); have h2 := nodeOffset_align8' 3 ((g >>> 2) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 4 (by omega); have h2 := nodeOffset_align8' 4 ((g >>> 3) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 5 (by omega); have h2 := nodeOffset_align8' 5 ((g >>> 4) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 2 _ (by omega) hsm.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 3 _ (by omega) hsm.2.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 4 _ (by omega) hsm.2.2.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 5 _ (by omega) hsm.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro4e 2 _ k (by omega) hsm.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro4e 3 _ k (by omega) hsm.2.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro4e 4 _ k (by omega) hsm.2.2.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro4e 5 _ k (by omega) hsm.2.2.2.2.1 hk)
    (fun hcl => hcl.1 2 (by omega) (by omega) _ hsm.2.1)
    (fun hcl => hcl.1 3 (by omega) (by omega) _ hsm.2.2.1)
    (fun hcl => hcl.1 4 (by omega) (by omega) _ hsm.2.2.2.1)
    (fun hcl => hcl.1 5 (by omega) (by omega) _ hsm.2.2.2.2.1)
    (by omega) hw4e
  have hro5 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s5 :=
    ReadOnlyPreserved.of_proofWrite hro4e hp5
  have hbt5 : BaseTableReady s5 := baseTableReady_of_lowEq hbt3 (fun a ha => (hp5 a (by omega)).trans (hmem4e3 a))
  have htbl5 : SlowTablesState s5 true := slowTablesState_of_eq htbl3 (fun a _ _ => (hp5 a (by omega)).trans (hmem4e3 a))
  have hcm5 : CapMarks15State s5 positions ordinal := capMarks15State_of_lowEq hcm3 (fun a _ _ => (hp5 a (by omega)).trans (hmem4e3 a))
  have hreg5_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x19, .x22, .x25, .x28] s s5 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg5 reg (by simp [h5', h6', h12', h25'])).trans
      ((hreg4e reg (by simp [h1', h6'])).trans
       ((hreg4d reg (by simp [h22', h19'])).trans
        ((hreg4c reg (by simp [h22', h8'])).trans
         ((hreg4b reg (by simp [h5', h22', h28'])).trans
          ((hreg4a reg (by simp [h22', h10'])).trans
           (hreg3_base reg (by simp [h1', h5', h6', h8', h10', h12', h22', h25', h28'])))))))
  have hs5_22 : s5.getReg .x22 = BitVec.ofNat 64 (g >>> 5) :=
    (hreg5 .x22 (by simp)).trans ((hreg4e .x22 (by simp)).trans hs4d_22)
  obtain ⟨s6a, hr6a, hpc6a, hs6a_22, hs6a_10, hreg6a, hmem6a⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4699 (lvlAddrInRegCode .x10 .x29) (by decide) rfl)
      hpc5 (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs5_22 ((hreg5_base .x29 (by simp)).trans hrx29)
  rw [div2_ushr_eq g 5 6] at hs6a_22
  obtain ⟨s6b, hr6b, hpc6b, hs6b_22, hs6b_28, hreg6b, hmem6b⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4704 (lvlAddrInRegCode .x28 .x30) (by decide) rfl)
      hpc6a (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs6a_22 ((hreg6a .x30 (by simp)).trans ((hreg5_base .x30 (by simp)).trans hrx30))
  rw [div2_ushr_eq g 6 7] at hs6b_22
  have hmem6b5 : ∀ a, s6b.getMem a = s5.getMem a := fun a => (hmem6b a).trans (hmem6a a)
  obtain ⟨s6c, hr6c, hpc6c, hs6c_1, hreg6c, hmem6c⟩ :=
    call_ld_jalr (r := r0) (tblOff := 1728) (tgt := pcCopy29x2 r0)
      (rfl : openInstr 4709 = .base (.LD .x6 .x14 (1728#12)))
      (rfl : openInstr 4710 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc6b
      ((hreg6b .x14 (by simp)).trans ((hreg6a .x14 (by simp)).trans ((hreg5_base .x14 (by simp)).trans hrx14)))
      (by rw [hmem6b5]; exact (slowTbl_get' htbl5 r0).2.2.2.2.2.2)
  have hmem6c5 : ∀ a, s6c.getMem a = s5.getMem a := fun a => (hmem6c a).trans (hmem6b5 a)
  have hro6c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s6c :=
    fun a ha => (hmem6c5 a).trans (hro5 a ha)
  have hw6c := writerState_of_mem_eq hw5 hmem6c5
    ((hreg6c .x25 (by simp)).trans ((hreg6b .x25 (by simp)).trans (hreg6a .x25 (by simp))))
    ((hreg6c .x12 (by simp)).trans ((hreg6b .x12 (by simp)).trans (hreg6a .x12 (by simp))))
  have hd_r0 : copy29x2NextDstOff r0 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  obtain ⟨s7, hr7, hpc7, hs7_14, hs7_5, hreg7, hp7, hw7⟩ := openRuns_sub_copy29x2 (r := r0) (retPc := 4711)
    (d0 := tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) (d1 := tdNode trapdoor 7 ((g >>> 6) ^^^ 1))
    hpc6c hs6c_1
    ((hreg6c .x11 (by simp)).trans ((hreg6b .x11 (by simp)).trans ((hreg6a .x11 (by simp)).trans ((hreg5_base .x11 (by simp)).trans hrx11))))
    ((hreg6c .x10 (by simp)).trans ((hreg6b .x10 (by simp)).trans hs6a_10))
    ((hreg6c .x28 (by simp)).trans hs6b_28)
    (by have h1 := levelBase_align8' 6 (by omega); have h2 := nodeOffset_align8' 6 ((g >>> 5) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 7 (by omega); have h2 := nodeOffset_align8' 7 ((g >>> 6) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 6 _ (by omega) hsm.2.2.2.2.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 7 _ (by omega) hsm.2.2.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro6c 6 _ k (by omega) hsm.2.2.2.2.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro6c 7 _ k (by omega) hsm.2.2.2.2.2.2.1 hk)
    (fun hcl => hcl.2 6 (by omega) (by omega) _ hsm.2.2.2.2.2.1)
    (fun hcl => hcl.2 7 (by omega) (by omega) _ hsm.2.2.2.2.2.2.1)
    (by omega) hw6c
  have h4711 := step_ADDI (s := s7) (by decide) hpc7 (rfl : openInstr 4711 = .base (.ADDI .x8 .x5 (0#12)))
  set s7a := (s7.setReg .x8 (s7.getReg .x5 + signExtend12 (0#12))).setPC (pcAt 4712)
  have h4712 := step_ANDI (s := s7a) (by decide) rfl (rfl : openInstr 4712 = .base (.ANDI .x5 .x22 (2#12)))
  set s7b := (s7a.setReg .x5 (s7a.getReg .x22 &&& signExtend12 (2#12))).setPC (pcAt 4713)
  have hs7a_22 : s7a.getReg .x22 = BitVec.ofNat 64 (g >>> 7) := by
    simp [s7a, getReg_setReg_ne', (hreg7 .x22 (by simp)).trans ((hreg6c .x22 (by simp)).trans hs6b_22)]
  have hreg7b_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s7b := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    simp only [s7b, s7a, MachineState.getReg_setPC, getReg_setReg_ne' .x5 reg h5'.symm, getReg_setReg_ne' .x8 reg h8'.symm]
    exact (hreg7 reg (by simp [h5', h6', h10', h12', h14', h19', h25'])).trans
      ((hreg6c reg (by simp [h1', h6'])).trans
       ((hreg6b reg (by simp [h22', h28'])).trans
        ((hreg6a reg (by simp [h22', h10'])).trans
         (hreg5_base reg (by simp [h1', h5', h6', h8', h10', h12', h19', h22', h25', h28'])))))
  have hp_tot : ProofWritePreserves s s7b :=
    ProofWritePreserves.trans (fun a _ => hmem2c0 a) <| hp3.trans <|
      ProofWritePreserves.trans (fun a _ => hmem4e3 a) <| hp5.trans <|
      ProofWritePreserves.trans (fun a _ => hmem6c5 a) <| hp7.trans (fun _ _ => by simp [s7b, s7a])
  have hrun7b := (((((((((((hr1.trans hr2).trans hr2c).trans hr3).trans hr4a).trans hr4b).trans hr4c).trans hr4d).trans hr4e).trans hr5).trans hr6a).trans hr6b).trans ((hr6c.trans hr7).trans (h4711.trans h4712))
  refine ⟨cL0, s7b, hcL0,
    by simpa only [show cL0 + 6 + 2 + (copy32x3SubCode r0).length + 5 + 6 + 5 + 5 + 2 + (copy30x4SubCode r0).length + 5 + 5 + (2 + (copy29x2SubCode r0).length + (1 + 1)) = slowMidPreCyc r0 cL0 by unfold slowMidPreCyc; omega] using hrun7b,
    rfl,
    by simp [s7b, hs7a_22, g],
    by simp [s7b, s7a, getReg_setReg_ne', hs7_14],
    by simp [s7b, getReg_setReg_ne', hs7a_22, g],
    fun hcl => by simp [s7b, s7a, getReg_setReg_ne', hs7_5 hcl, signExtend12_nonneg 0 (by omega), g],
    hreg7b_base,
    fun a ha => (by simp [s7b, s7a] : s7b.getMem a = s7.getMem a).trans (ReadOnlyPreserved.of_proofWrite hro6c hp7 a ha),
    baseTableReady_of_lowEq hbt5 (fun a ha => (by simp [s7b, s7a] : s7b.getMem a = s7.getMem a).trans ((hp7 a (by omega)).trans (hmem6c5 a))),
    slowTablesState_of_eq htbl5 (fun a _ _ => (by simp [s7b, s7a] : s7b.getMem a = s7.getMem a).trans ((hp7 a (by omega)).trans (hmem6c5 a))),
    capMarks15State_of_lowEq hcm5 (fun a _ _ => (by simp [s7b, s7a] : s7b.getMem a = s7.getMem a).trans ((hp7 a (by omega)).trans (hmem6c5 a))),
    writerState_of_mem_eq hw7 (s' := s7b) (fun _ => by simp [s7b, s7a]) (by simp [s7b, s7a, getReg_setReg_ne']) (by simp [s7b, s7a, getReg_setReg_ne']),
    TailState.of_proofWrite ht0 hp_tot (hreg7b_base .x15 (by decide)) (hreg7b_base .x16 (by decide)) (hreg7b_base .x17 (by decide))⟩

/-- `slow_mid` L8-present branch (`4713 → 4755 → 4793 → epilogue`). -/
private theorem openRuns_slow_mid_has8 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes cL0 : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s s7b : MachineState}
    (hord : ordinal < positions.card)
    (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg1 : 5592064 ≤ ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)
    (hg2 : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592384)
    (hcL0 : cL0 ≤ 6)
    (hhas8 : ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 7) % 4 < 2)
    (hinv : SlowEntryInv trapdoor positions ordinal r0 base written tails flushes true
              ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) (s.setPC (pcAt PC_slow_body)))
    (hpc7b : s7b.pc = pcAt 4713)
    (hs7b_5 : s7b.getReg .x5 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 7) &&& signExtend12 (2#12))
    (hs7b_14 : s7b.getReg .x14 = BitVec.ofNat 64 (8 * (copy29x2NextR r0).val))
    (hs7b_22 : s7b.getReg .x22 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 7))
    (hs7b_8 : CleanTrapdoor trapdoor → s7b.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [tail6 (tdNode trapdoor 6 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 6) ^^^ 1))]))
    (hreg7b_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s7b)
    (hro7b : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7b)
    (hbt7b : BaseTableReady s7b)
    (htbl7b : SlowTablesState s7b true)
    (hcm7b : CapMarks15State s7b positions ordinal)
    (hw7b : WriterState (CleanTrapdoor trapdoor) s7b (copy29x2NextR r0) false (base + 24 + 96 + 120 + copy29x2NextDstOff r0) 0
      (written ++ bitsToBytes (tdSalt trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord]))) 24 ++
        bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])))) 32 ++
        bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])))) 32 ++
        bitsToBytes (tdNode trapdoor 1 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) ^^^ 1)) 32 ++
        bitsToBytes (tdNode trapdoor 2 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 1) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 3 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 2) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 4 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 3) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 5 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 4) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 6 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 5) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 7 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 6) ^^^ 1)) 29))
    (ht7b : TailState (CleanTrapdoor trapdoor) s7b tails flushes) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    ∃ cycRem rEnd baseEnd s',
      OpenRuns s7b (cycRem + 4 * fl) (cycRem + 4 * fl) s' ∧
      8 * (slowEntryCyc r0 + 4 + (slowMidPreCyc r0 cL0 + cycRem)) + phi8 rEnd ≤ 3453 + phi8 r0 ∧
      if ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) true s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  set r1 := copy29x2NextR r0
  have hi_lt : i.val < 16777216 := i.isLt
  have hsm := level_sib_of_slow_mid g hg1 hg2
  have hrec_eq := record_slow_mid_eq (tdNode trapdoor) (tdSalt trapdoor) i hg1 hg2
  have hd_r0 : copy29x2NextDstOff r0 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  have hx5_eq : s7b.getReg .x5 = s7b.getReg .x0 := by
    rw [hs7b_5, show s7b.getReg .x0 = 0#64 from rfl]
    exact (bv64_and2_eq_zero_iff (g >>> 7) (by simp [Nat.shiftRight_eq_div_pow]; omega)).mpr hhas8
  have h4713 := step_BNE_not_taken (s := s7b) (by decide) hpc7b (rfl : openInstr 4713 = .base (.BNE .x5 .x0 (172#13))) hx5_eq
  set s8 := s7b.setPC (pcAt 4714)
  have hl8_lt : ((g >>> 7) ^^^ 1) < levelSize 8 := hsm.2.2.2.2.2.2.2.1.mpr hhas8
  obtain ⟨s8a, hr8a, hpc8a, hs8a_22, hs8a_10, hreg8a, hmem8a⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4714 (lvlAddrInRegCode .x10 .x31) (by decide) rfl)
      (rfl : s8.pc = pcAt 4714) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs7b_22 ((by simp [s8] : s8.getReg .x31 = s7b.getReg .x31).trans ((hreg7b_base .x31 (by simp)).trans hinv.rx31))
  rw [div2_ushr_eq g 7 8] at hs8a_22
  obtain ⟨s8b, hr8b, hpc8b, hs8b_22, hs8b_28, hreg8b, hmem8b⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4719 (lvlAddrInRegCode .x28 .x23) (by decide) rfl)
      hpc8a (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide)
      hs8a_22 ((hreg8a .x23 (by simp)).trans ((by simp [s8] : s8.getReg .x23 = s7b.getReg .x23).trans ((hreg7b_base .x23 (by simp)).trans hinv.rx23)))
  rw [div2_ushr_eq g 8 9] at hs8b_22
  have hmem8b7 : ∀ a, s8b.getMem a = s7b.getMem a := fun a => (hmem8b a).trans ((hmem8a a).trans (by simp [s8]))
  obtain ⟨s8c, hr8c, hpc8c, hs8c_1, hreg8c, hmem8c⟩ :=
    call_ld_jalr (r := r1) (tblOff := 1728) (tgt := pcCopy29x2 r1)
      (rfl : openInstr 4724 = .base (.LD .x6 .x14 (1728#12)))
      (rfl : openInstr 4725 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc8b
      ((hreg8b .x14 (by simp)).trans ((hreg8a .x14 (by simp)).trans (by simpa [s8] using hs7b_14)))
      (by rw [hmem8b7]; exact (slowTbl_get' htbl7b r1).2.2.2.2.2.2)
  have hmem8c7 : ∀ a, s8c.getMem a = s7b.getMem a := fun a => (hmem8c a).trans (hmem8b7 a)
  have hro8c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s8c :=
    fun a ha => (hmem8c7 a).trans (hro7b a ha)
  have hw8c := writerState_of_mem_eq hw7b hmem8c7
    ((hreg8c .x25 (by simp)).trans ((hreg8b .x25 (by simp)).trans ((hreg8a .x25 (by simp)).trans (by simp [s8]))))
    ((hreg8c .x12 (by simp)).trans ((hreg8b .x12 (by simp)).trans ((hreg8a .x12 (by simp)).trans (by simp [s8]))))
  set r2 := copy29x2NextR r1
  have hd_r1 : copy29x2NextDstOff r1 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  obtain ⟨s9, hr9, hpc9, hs9_14, hs9_5, hreg9, hp9, hw9⟩ := openRuns_sub_copy29x2 (r := r1) (retPc := 4726)
    (d0 := tdNode trapdoor 8 ((g >>> 7) ^^^ 1)) (d1 := tdNode trapdoor 9 ((g >>> 8) ^^^ 1))
    hpc8c hs8c_1
    ((hreg8c .x11 (by simp)).trans ((hreg8b .x11 (by simp)).trans ((hreg8a .x11 (by simp)).trans ((by simp [s8] : s8.getReg .x11 = s7b.getReg .x11).trans ((hreg7b_base .x11 (by simp)).trans hinv.rx11)))))
    ((hreg8c .x10 (by simp)).trans ((hreg8b .x10 (by simp)).trans hs8a_10))
    ((hreg8c .x28 (by simp)).trans hs8b_28)
    (by have h1 := levelBase_align8' 8 (by omega); have h2 := nodeOffset_align8' 8 ((g >>> 7) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 9 (by omega); have h2 := nodeOffset_align8' 9 ((g >>> 8) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 8 _ (by omega) hl8_lt; omega)
    (by have := nodeOffset_lt_treeBytes' 9 _ (by omega) hsm.2.2.2.2.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro8c 8 _ k (by omega) hl8_lt hk)
    (fun _ k hk => readOnly_getMem_tdNode hro8c 9 _ k (by omega) hsm.2.2.2.2.2.2.2.2.1 hk)
    (fun hcl => hcl.2 8 (by omega) (by omega) _ hl8_lt)
    (fun hcl => hcl.2 9 (by omega) (by omega) _ hsm.2.2.2.2.2.2.2.2.1)
    (by omega) hw8c
  obtain ⟨s9a, hr9a, hpc9a, hs9a_8, hreg9a, hmem9a⟩ := openRuns_combine_tails
    (ts0 := [tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))])
    (ts1 := [tail6 (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1))])
    (by simp) (rfl : openInstr 4726 = .base (.SLLI .x5 .x5 (12#6)))
    (rfl : openInstr 4727 = .base (.OR .x8 .x8 .x5)) (by decide) hpc9
    (fun hcl => (hreg9 .x8 (by simp)).trans ((hreg8c .x8 (by simp)).trans ((hreg8b .x8 (by simp)).trans ((hreg8a .x8 (by simp)).trans (by simpa [s8] using hs7b_8 hcl)))))
    hs9_5
  have h4728 := step_SRLI (s := s9a) (by decide) hpc9a (rfl : openInstr 4728 = .base (.SRLI .x22 .x22 (1#6)))
  set s10 := (s9a.setReg .x22 (s9a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4729)
  have hs10_22 : s10.getReg .x22 = BitVec.ofNat 64 (g >>> 10) := by
    have h9_22 : s9a.getReg .x22 = BitVec.ofNat 64 (g >>> 9) :=
      (hreg9a .x22 (by simp)).trans ((hreg9 .x22 (by simp)).trans ((hreg8c .x22 (by simp)).trans hs8b_22))
    simp only [s10, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, h9_22,
      show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 9) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 9) >>> 1 = g >>> 10 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hbt10 : BaseTableReady s10 := baseTableReady_of_lowEq hbt7b (fun a ha => (by simp [s10, hmem9a] : s10.getMem a = s9.getMem a).trans ((hp9 a (by omega)).trans (hmem8c7 a)))
  have htbl9 : SlowTablesState s9 true := slowTablesState_of_eq htbl7b (fun a _ _ => (hp9 a (by omega)).trans (hmem8c7 a))
  have hreg9_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s9 := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg9 reg (by simp [h5', h6', h10', h12', h14', h19', h25'])).trans
      ((hreg8c reg (by simp [h1', h6'])).trans ((hreg8b reg (by simp [h22', h28'])).trans
        ((hreg8a reg (by simp [h22', h10'])).trans ((by simp [s8] : s8.getReg reg = s7b.getReg reg).trans
          (hreg7b_base reg hreg)))))
  have hs10_3 : s10.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11) :=
    (by simp [s10, getReg_setReg_ne'] : s10.getReg .x3 = s9a.getReg .x3).trans
      ((hreg9a .x3 (by simp)).trans ((hreg9_base .x3 (by decide)).trans hinv.rx3))
  obtain ⟨s10a, hr10a, hpc10a, hs10a_22, hs10a_10, hreg10a, hmem10a⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4729 (lvlAddrInRegCode .x10 .x3) (by decide) rfl)
      rfl (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide) hs10_22 hs10_3
  rw [div2_ushr_eq g 10 11] at hs10a_22
  have h4734 := step_SRLI (s := s10a) (by decide) hpc10a (rfl : openInstr 4734 = .base (.SRLI .x22 .x22 (1#6)))
  set s10b := (s10a.setReg .x22 (s10a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4735)
  have hs10b_22 : s10b.getReg .x22 = BitVec.ofNat 64 (g >>> 12) := by
    simp only [s10b, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs10a_22,
      show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 11) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 11) >>> 1 = g >>> 12 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  obtain ⟨s10c, hr10c, hpc10c, hs10c_22, hs10c_28, hreg10c, hmem10c⟩ :=
    openRuns_lvl_addr_inmem (codeAt_of_list_eq 4735 (lvlAddrInMemCode .x28 13) (by decide) rfl)
      rfl (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide)
      hs10b_22 (baseTableReady_of_lowEq hbt10 (fun a _ => by simp [s10b, hmem10a]))
  rw [div2_ushr_eq g 12 13] at hs10c_22
  have h4741 := step_SRLI (s := s10c) (by decide) hpc10c (rfl : openInstr 4741 = .base (.SRLI .x22 .x22 (1#6)))
  set s10d := (s10c.setReg .x22 (s10c.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4742)
  have hs10d_22 : s10d.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) := by
    simp only [s10d, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs10c_22,
      show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 13) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega), capLeafOf_eq_div16384]
    rw [show (g >>> 13) >>> 1 = g >>> 14 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hreg10d_9a : RegsEqExcept [.x5, .x10, .x22, .x28] s9a s10d := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    have e1 : s10d.getReg reg = s10c.getReg reg := by simp [s10d, getReg_setReg_ne' .x22 reg h22'.symm]
    have e2 : s10b.getReg reg = s10a.getReg reg := by simp [s10b, getReg_setReg_ne' .x22 reg h22'.symm]
    have e3 : s10.getReg reg = s9a.getReg reg := by simp [s10, getReg_setReg_ne' .x22 reg h22'.symm]
    exact e1.trans ((hreg10c reg (by simp [h5', h22', h28'])).trans (e2.trans ((hreg10a reg (by simp [h22', h10'])).trans e3)))
  have hreg10d_9 : RegsEqExcept [.x5, .x8, .x10, .x22, .x28] s9 s10d := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg10d_9a reg (by simp [h5', h10', h22', h28'])).trans (hreg9a reg (by simp [h5', h8']))
  have hmem10d9 : ∀ a, s10d.getMem a = s9.getMem a := fun a => by simp [s10d, hmem10c, s10b, hmem10a, s10, hmem9a]
  obtain ⟨s10e, hr10e, hpc10e, hs10e_1, hreg10e, hmem10e⟩ :=
    call_ld_jalr (r := r2) (tblOff := 1728) (tgt := pcCopy29x2 r2)
      (rfl : openInstr 4742 = .base (.LD .x6 .x14 (1728#12)))
      (rfl : openInstr 4743 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) rfl
      ((hreg10d_9 .x14 (by decide)).trans hs9_14)
      (by rw [hmem10d9]; exact (slowTbl_get' htbl9 r2).2.2.2.2.2.2)
  have hmem10e9 : ∀ a, s10e.getMem a = s9.getMem a := fun a => (hmem10e a).trans (hmem10d9 a)
  have hro10e : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s10e :=
    fun a ha => (hmem10e9 a).trans (ReadOnlyPreserved.of_proofWrite hro8c hp9 a ha)
  have hw10e := writerState_of_mem_eq hw9 hmem10e9
    ((hreg10e .x25 (by decide)).trans (hreg10d_9 .x25 (by decide)))
    ((hreg10e .x12 (by decide)).trans (hreg10d_9 .x12 (by decide)))
  set r3 := copy29x2NextR r2
  have hd_r2 : copy29x2NextDstOff r2 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  have hs10e_10 : s10e.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 11 + nodeOffset 11 ((g >>> 10) ^^^ 1)) := by
    have e1 : s10d.getReg .x10 = s10c.getReg .x10 := by simp [s10d, getReg_setReg_ne']
    have e2 : s10b.getReg .x10 = s10a.getReg .x10 := by simp [s10b, getReg_setReg_ne']
    exact (hreg10e .x10 (by decide)).trans (e1.trans ((hreg10c .x10 (by decide)).trans (e2.trans hs10a_10)))
  have hs10e_28 : s10e.getReg .x28 = BitVec.ofNat 64 (4294971424 + levelBase 13 + nodeOffset 13 ((g >>> 12) ^^^ 1)) := by
    have e1 : s10d.getReg .x28 = s10c.getReg .x28 := by simp [s10d, getReg_setReg_ne']
    exact (hreg10e .x28 (by decide)).trans (e1.trans hs10c_28)
  obtain ⟨s11, hr11, hpc11, hs11_14, hs11_5, hreg11, hp11, hw11⟩ := openRuns_sub_copy29x2 (r := r2) (retPc := 4744)
    (d0 := tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) (d1 := tdNode trapdoor 13 ((g >>> 12) ^^^ 1))
    hpc10e hs10e_1
    ((hreg10e .x11 (by decide)).trans ((hreg10d_9 .x11 (by decide)).trans ((hreg9_base .x11 (by decide)).trans hinv.rx11)))
    hs10e_10 hs10e_28
    (by have h1 := levelBase_align8' 11 (by omega); have h2 := nodeOffset_align8' 11 ((g >>> 10) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 13 (by omega); have h2 := nodeOffset_align8' 13 ((g >>> 12) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 11 _ (by omega) hsm.2.2.2.2.2.2.2.2.2.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 13 _ (by omega) hsm.2.2.2.2.2.2.2.2.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro10e 11 _ k (by omega) hsm.2.2.2.2.2.2.2.2.2.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro10e 13 _ k (by omega) hsm.2.2.2.2.2.2.2.2.2.2.2.2.1 hk)
    (fun hcl => hcl.2 11 (by omega) (by omega) _ hsm.2.2.2.2.2.2.2.2.2.2.1)
    (fun hcl => hcl.2 13 (by omega) (by omega) _ hsm.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (by omega) hw10e
  set ts6 : List (BitVec 6) :=
    ([tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))] ++
     [tail6 (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1))]) ++
     [tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)), tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))]
  have hts6_eq : ts6 = recordTails (tdNode trapdoor) i := by
    rw [hrec_eq.2]; simp only [ts6, g, decide_eq_true_iff, hhas8, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨s11a, hr11a, hpc11a, hs11a_8, hreg11a, hmem11a⟩ := openRuns_combine_tails
    (ts0 := [tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))] ++
            [tail6 (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1))])
    (ts1 := [tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)), tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))])
    (by simp) (rfl : openInstr 4744 = .base (.SLLI .x5 .x5 (24#6)))
    (rfl : openInstr 4745 = .base (.OR .x8 .x8 .x5)) (by decide) hpc11
    (fun hcl => (hreg11 .x8 (by decide)).trans ((hreg10e .x8 (by decide)).trans ((hreg10d_9a .x8 (by decide)).trans (hs9a_8 hcl))))
    hs11_5
  have hreg11a_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s11a := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg11a reg (by simp [h5', h8'])).trans ((hreg11 reg (by simp [h5', h6', h10', h12', h14', h19', h25'])).trans
      ((hreg10e reg (by simp [h1', h6'])).trans ((hreg10d_9 reg (by simp [h5', h8', h10', h22', h28'])).trans (hreg9_base reg hreg))))
  have hp11a7b : ProofWritePreserves s7b s11a :=
    ProofWritePreserves.trans (fun a _ => hmem8c7 a) <|
      hp9.trans <| ProofWritePreserves.trans (fun a _ => hmem10e9 a) <| hp11.trans (fun _ _ => hmem11a _)
  have ht11a : TailState (CleanTrapdoor trapdoor) s11a tails flushes :=
    TailState.of_proofWrite ht7b hp11a7b
      ((hreg11a_base .x15 (by decide)).trans (hreg7b_base .x15 (by decide)).symm)
      ((hreg11a_base .x16 (by decide)).trans (hreg7b_base .x16 (by decide)).symm)
      ((hreg11a_base .x17 (by decide)).trans (hreg7b_base .x17 (by decide)).symm)
  obtain ⟨s12, hr12, hpc12, hreg12, htw12, ht12⟩ := openRuns_tailMerge_neg (ts := ts6)
    (by simp [ts6]) (by simp [ts6]) (codeAt_of_list_eq 4746 (tailMergeCode 36) (by decide) rfl)
    hpc11a hs11a_8 ht11a hbd_t
  have hjal_tgt : pcAt 4755 + signExtend21 (152#21) = pcAt 4793 := by
    simpa only [show 4 * (4793 - 4755) = 152 by decide] using pcAt_add_pos21 4755 4793 (by decide) (by decide)
  have h4755 := step_JAL (s := s12) (by decide) hpc12 (rfl : openInstr 4755 = .base (.JAL .x0 (152#21))) hjal_tgt
  set s13 := (s12.setReg .x0 (pcAt 4756)).setPC (pcAt 4793)
  have hro13 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s13 :=
    fun a ha => (by simp [s13] : s13.getMem a = s12.getMem a).trans
      (readOnlyPreserved_of_tailWrite (ReadOnlyPreserved.of_proofWrite hro7b hp11a7b) htw12 a ha)
  have hbt13 : BaseTableReady s13 := baseTableReady_of_lowEq hbt7b (fun a ha =>
    (by simp [s13] : s13.getMem a = s12.getMem a).trans (((tailWrite_pres_low htw12).1 a ha).trans ((proofWrite_pres_low hp11a7b).1 a ha)))
  have htbl13 : SlowTablesState s13 true := slowTablesState_of_eq htbl7b (fun a h1 h2 =>
    (by simp [s13] : s13.getMem a = s12.getMem a).trans (((tailWrite_pres_low htw12).2.2 a h1 h2).trans ((proofWrite_pres_low hp11a7b).2.2 a h1 h2)))
  have hcm13 : CapMarks15State s13 positions ordinal := capMarks15State_of_lowEq hcm7b (fun a h1 h2 =>
    (by simp [s13] : s13.getMem a = s12.getMem a).trans (((tailWrite_pres_low htw12).2.1 a h1 h2).trans ((proofWrite_pres_low hp11a7b).2.1 a h1 h2)))
  have hfwd_eq : written ++ bitsToBytes (tdSalt trapdoor i) 24 ++ bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx i)) 32 ++
      bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx i)) 32 ++ bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32 ++
      bitsToBytes (tdNode trapdoor 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29 =
      written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i := by
    rw [hrec_eq.1]; simp only [g, decide_eq_true_iff, hhas8, ↓reduceIte, List.append_assoc]
  have hw13 : WriterState (CleanTrapdoor trapdoor) s13 r3 false
      (base + 24 + 96 + 120 + copy29x2NextDstOff r0 + copy29x2NextDstOff r1 + copy29x2NextDstOff r2) 0
      (written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i) := by
    rw [← hfwd_eq]
    have hw11a := writerState_of_mem_eq hw11 hmem11a (hreg11a .x25 (by decide)) (hreg11a .x12 (by decide))
    have hw12 := writerState_of_tailWrite hw11a htw12 (hreg12 .x25 (by decide)) (hreg12 .x12 (by decide))
    exact writerState_of_mem_eq hw12 (fun _ => by simp [s13]) (by simp [s13, setReg_x0_eq]) (by simp [s13, setReg_x0_eq])
  have ht13 : TailState (CleanTrapdoor trapdoor) s13 (tails ++ recordTails (tdNode trapdoor) i)
      (flushes + if (6 * tails.length) % 64 + 6 * ts6.length < 64 then 0 else 1) := by
    rw [← hts6_eq]
    exact TailState.of_proofWrite ht12 (fun _ _ => by simp [s13]) (by simp [s13, setReg_x0_eq]) (by simp [s13, setReg_x0_eq]) (by simp [s13, setReg_x0_eq])
  have hreg13 : ∀ reg, reg ∉ ([.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x15, .x16, .x17, .x19, .x22, .x25, .x28] : List Reg) →
      s13.getReg reg = s.getReg reg := fun reg hreg => by
    have h0 : s13.getReg reg = s12.getReg reg := by simp [s13, setReg_x0_eq]
    exact h0.trans ((hreg12 reg (reg_not_mem_sub (by decide) hreg)).trans
      (hreg11a_base reg (reg_not_mem_sub (by decide) hreg)))
  have hs13_14 : s13.getReg .x14 = BitVec.ofNat 64 (8 * r3.val) :=
    (by simp [s13, setReg_x0_eq] : s13.getReg .x14 = s12.getReg .x14).trans
      ((hreg12 .x14 (by decide)).trans ((hreg11a .x14 (by decide)).trans hs11_14))
  have hs13_22 : s13.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) :=
    (by simp [s13, setReg_x0_eq] : s13.getReg .x22 = s12.getReg .x22).trans
      ((hreg12 .x22 (by decide)).trans ((hreg11a .x22 (by decide)).trans
        ((hreg11 .x22 (by decide)).trans ((hreg10e .x22 (by decide)).trans hs10d_22))))
  obtain ⟨sEnd, hrEnd, hinvEnd⟩ := openRuns_slow_epilogue (isTail := false) hord rfl
    (fun _ => (hreg13 .x2 (by decide)).trans hinv.rx2) ((hreg13 .x3 (by decide)).trans hinv.rx3)
    ((hreg13 .x4 (by decide)).trans hinv.rx4) ((hreg13 .x7 (by decide)).trans hinv.rx7)
    ((hreg13 .x9 (by decide)).trans hinv.rx9) ((hreg13 .x11 (by decide)).trans hinv.rx11)
    ((hreg13 .x13 (by decide)).trans hinv.rx13) hs13_14 ((hreg13 .x18 (by decide)).trans hinv.rx18)
    ((hreg13 .x20 (by decide)).trans hinv.rx20) ((hreg13 .x21 (by decide)).trans hinv.rx21)
    hs13_22 ((hreg13 .x23 (by decide)).trans hinv.rx23) ((hreg13 .x24 (by decide)).trans hinv.rx24)
    ((hreg13 .x26 (by decide)).trans hinv.rx26) ((hreg13 .x27 (by decide)).trans hinv.rx27)
    ((hreg13 .x29 (by decide)).trans hinv.rx29) ((hreg13 .x30 (by decide)).trans hinv.rx30)
    ((hreg13 .x31 (by decide)).trans hinv.rx31) hro13 hbt13 hcm13 htbl13 hw13 ht13
  set cycRem := 1 + (5 + 5) + (2 + (copy29x2SubCode r1).length) + 2 + (1 + 5 + 1 + 6 + 1) +
    (2 + (copy29x2SubCode r2).length) + 2 + 5 + 1 + (if ordinal + 1 = positions.card then 4 else 8)
  have hfl_eq : (if (6 * tails.length) % 64 + 6 * ts6.length < 64 then 0 else 1) =
      (if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
    rw [hts6_eq]
  refine ⟨cycRem, r3,
    base + 24 + 96 + 120 + copy29x2NextDstOff r0 + copy29x2NextDstOff r1 + copy29x2NextDstOff r2, sEnd, ?_, ?_, ?_⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrEnd
    have htot := (((((((((((h4713.trans hr8a).trans hr8b).trans hr8c).trans hr9).trans hr9a).trans h4728).trans hr10a).trans h4734).trans hr10c).trans h4741).trans
      ((((hr10e.trans hr11).trans hr11a).trans hr12).trans (h4755.trans hrEnd)))
    have heq_c : 1 + 5 + 5 + 2 + (copy29x2SubCode r1).length + 2 + 1 + 5 + 1 + 6 + 1 +
        (2 + (copy29x2SubCode r2).length + 2 +
        (5 + 4 * (if 6 * tails.length % 64 + 6 * ts6.length < 64 then 0 else 1)) +
        (1 + if ordinal + 1 = positions.card then 4 else 8)) =
        cycRem + 4 * (if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
      rw [hfl_eq]; unfold cycRem; split_ifs <;> omega
    rw [heq_c] at htot; exact htot
  · have ha := slowMidFull_amort r0
    have hle : slowEntryCyc r0 + 4 + (slowMidPreCyc r0 cL0 + cycRem) ≤ slowMidFullCyc r0 := by
      unfold slowMidFullCyc slowMidPreCyc cycRem; dsimp only [r1, r2]; split_ifs <;> omega
    exact le_trans (by dsimp only [r3, r2, r1]; omega) ha
  · rw [← hfl_eq]; by_cases hl : ordinal + 1 = positions.card <;> simp only [hl, ↓reduceIte, ↓reduceDIte] at hinvEnd ⊢ <;> exact hinvEnd

/-- `slow_mid` L8-skipped branch (`4713 → 4756 → 4793 → epilogue`). -/
private theorem openRuns_slow_mid_skip8 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes cL0 : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s s7b : MachineState}
    (hord : ordinal < positions.card)
    (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg1 : 5592064 ≤ ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)
    (hg2 : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592384)
    (hcL0 : cL0 ≤ 6)
    (hhas8 : ¬ ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 7) % 4 < 2)
    (hinv : SlowEntryInv trapdoor positions ordinal r0 base written tails flushes true
              ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) (s.setPC (pcAt PC_slow_body)))
    (hpc7b : s7b.pc = pcAt 4713)
    (hs7b_5 : s7b.getReg .x5 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 7) &&& signExtend12 (2#12))
    (hs7b_14 : s7b.getReg .x14 = BitVec.ofNat 64 (8 * (copy29x2NextR r0).val))
    (hs7b_22 : s7b.getReg .x22 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 7))
    (hs7b_8 : CleanTrapdoor trapdoor → s7b.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [tail6 (tdNode trapdoor 6 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 6) ^^^ 1))]))
    (hreg7b_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s7b)
    (hro7b : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7b)
    (hbt7b : BaseTableReady s7b)
    (htbl7b : SlowTablesState s7b true)
    (hcm7b : CapMarks15State s7b positions ordinal)
    (hw7b : WriterState (CleanTrapdoor trapdoor) s7b (copy29x2NextR r0) false (base + 24 + 96 + 120 + copy29x2NextDstOff r0) 0
      (written ++ bitsToBytes (tdSalt trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord]))) 24 ++
        bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])))) 32 ++
        bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])))) 32 ++
        bitsToBytes (tdNode trapdoor 1 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) ^^^ 1)) 32 ++
        bitsToBytes (tdNode trapdoor 2 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 1) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 3 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 2) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 4 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 3) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 5 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 4) ^^^ 1)) 30 ++
        bitsToBytes (tdNode trapdoor 6 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 5) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 7 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 6) ^^^ 1)) 29))
    (ht7b : TailState (CleanTrapdoor trapdoor) s7b tails flushes) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    ∃ cycRem rEnd baseEnd s',
      OpenRuns s7b (cycRem + 4 * fl) (cycRem + 4 * fl) s' ∧
      8 * (slowEntryCyc r0 + 4 + (slowMidPreCyc r0 cL0 + cycRem)) + phi8 rEnd ≤ 3453 + phi8 r0 ∧
      if ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) true s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  set r1 := copy29x2NextR r0
  have hi_lt : i.val < 16777216 := i.isLt
  have hsm := level_sib_of_slow_mid g hg1 hg2
  have hrec_eq := record_slow_mid_eq (tdNode trapdoor) (tdSalt trapdoor) i hg1 hg2
  have hd_r0 : copy29x2NextDstOff r0 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  have hx5_ne : s7b.getReg .x5 ≠ s7b.getReg .x0 := by
    rw [hs7b_5, show s7b.getReg .x0 = 0#64 from rfl]
    intro h; exact hhas8 ((bv64_and2_eq_zero_iff (g >>> 7) (by simp [Nat.shiftRight_eq_div_pow]; omega)).mp h)
  have hbr_s8 : pcAt 4713 + signExtend13 (172#13) = pcAt 4756 := by
    simpa only [show 4 * (4756 - 4713) = 172 by decide] using pcAt_add_pos13 4713 4756 (by decide) (by decide)
  have h4713 := step_BNE_taken (s := s7b) (by decide) hpc7b (rfl : openInstr 4713 = .base (.BNE .x5 .x0 (172#13))) hx5_ne hbr_s8
  set s8 := s7b.setPC (pcAt 4756)
  have h4756 := step_SRLI (s := s8) (by decide) rfl (rfl : openInstr 4756 = .base (.SRLI .x22 .x22 (1#6)))
  set s8_0 := (s8.setReg .x22 (s8.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4757)
  have hs8_0_22 : s8_0.getReg .x22 = BitVec.ofNat 64 (g >>> 8) := by
    simp only [s8_0, s8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs7b_22,
      show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 7) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 7) >>> 1 = g >>> 8 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hs8_0_23 : s8_0.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9) :=
    (by simp [s8_0, s8, getReg_setReg_ne'] : s8_0.getReg .x23 = s7b.getReg .x23).trans ((hreg7b_base .x23 (by decide)).trans hinv.rx23)
  obtain ⟨s8a, hr8a, hpc8a, hs8a_22, hs8a_10, hreg8a, hmem8a⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4757 (lvlAddrInRegCode .x10 .x23) (by decide) rfl)
      rfl (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide) hs8_0_22 hs8_0_23
  rw [div2_ushr_eq g 8 9] at hs8a_22
  have h4762 := step_SRLI (s := s8a) (by decide) hpc8a (rfl : openInstr 4762 = .base (.SRLI .x22 .x22 (1#6)))
  set s8_1 := (s8a.setReg .x22 (s8a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4763)
  have hs8_1_22 : s8_1.getReg .x22 = BitVec.ofNat 64 (g >>> 10) := by
    simp only [s8_1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs8a_22,
      show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 9) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 9) >>> 1 = g >>> 10 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hs8_1_3 : s8_1.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11) :=
    (by simp [s8_1, getReg_setReg_ne'] : s8_1.getReg .x3 = s8a.getReg .x3).trans
      ((hreg8a .x3 (by decide)).trans ((by simp [s8_0, s8, getReg_setReg_ne'] : s8_0.getReg .x3 = s7b.getReg .x3).trans ((hreg7b_base .x3 (by decide)).trans hinv.rx3)))
  obtain ⟨s8b, hr8b, hpc8b, hs8b_22, hs8b_28, hreg8b, hmem8b⟩ :=
    openRuns_lvl_addr_inreg (codeAt_of_list_eq 4763 (lvlAddrInRegCode .x28 .x3) (by decide) rfl)
      rfl (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) (by decide) hs8_1_22 hs8_1_3
  rw [div2_ushr_eq g 10 11] at hs8b_22
  have hreg8b_7b : RegsEqExcept [.x10, .x22, .x28] s7b s8b := fun reg hreg => by
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    have e1 : s8_1.getReg reg = s8a.getReg reg := by simp [s8_1, getReg_setReg_ne' .x22 reg h22'.symm]
    have e2 : s8_0.getReg reg = s7b.getReg reg := by simp [s8_0, s8, getReg_setReg_ne' .x22 reg h22'.symm]
    exact (hreg8b reg (by simp [h22', h28'])).trans (e1.trans ((hreg8a reg (by simp [h22', h10'])).trans e2))
  have hmem8b7 : ∀ a, s8b.getMem a = s7b.getMem a := fun a => by simp [hmem8b, s8_1, hmem8a, s8_0, s8]
  obtain ⟨s8c, hr8c, hpc8c, hs8c_1, hreg8c, hmem8c⟩ :=
    call_ld_jalr (r := r1) (tblOff := 1728) (tgt := pcCopy29x2 r1)
      (rfl : openInstr 4768 = .base (.LD .x6 .x14 (1728#12)))
      (rfl : openInstr 4769 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) hpc8b
      ((hreg8b_7b .x14 (by decide)).trans hs7b_14)
      (by rw [hmem8b7]; exact (slowTbl_get' htbl7b r1).2.2.2.2.2.2)
  have hmem8c7 : ∀ a, s8c.getMem a = s7b.getMem a := fun a => (hmem8c a).trans (hmem8b7 a)
  have hro8c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s8c :=
    fun a ha => (hmem8c7 a).trans (hro7b a ha)
  have hw8c := writerState_of_mem_eq hw7b hmem8c7
    ((hreg8c .x25 (by decide)).trans (hreg8b_7b .x25 (by decide)))
    ((hreg8c .x12 (by decide)).trans (hreg8b_7b .x12 (by decide)))
  set r2 := copy29x2NextR r1
  have hd_r1 : copy29x2NextDstOff r1 ≤ 64 := by unfold copy29x2NextDstOff copy29NextDstOff; split_ifs <;> omega
  have hs8c_10 : s8c.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 9 + nodeOffset 9 ((g >>> 8) ^^^ 1)) := by
    have e1 : s8_1.getReg .x10 = s8a.getReg .x10 := by simp [s8_1, getReg_setReg_ne']
    exact (hreg8c .x10 (by decide)).trans ((hreg8b .x10 (by decide)).trans (e1.trans hs8a_10))
  obtain ⟨s9, hr9, hpc9, hs9_14, hs9_5, hreg9, hp9, hw9⟩ := openRuns_sub_copy29x2 (r := r1) (retPc := 4770)
    (d0 := tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) (d1 := tdNode trapdoor 11 ((g >>> 10) ^^^ 1))
    hpc8c hs8c_1
    ((hreg8c .x11 (by decide)).trans ((hreg8b_7b .x11 (by decide)).trans ((hreg7b_base .x11 (by decide)).trans hinv.rx11)))
    hs8c_10 ((hreg8c .x28 (by decide)).trans hs8b_28)
    (by have h1 := levelBase_align8' 9 (by omega); have h2 := nodeOffset_align8' 9 ((g >>> 8) ^^^ 1); omega)
    (by have h1 := levelBase_align8' 11 (by omega); have h2 := nodeOffset_align8' 11 ((g >>> 10) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 9 _ (by omega) hsm.2.2.2.2.2.2.2.2.1; omega)
    (by have := nodeOffset_lt_treeBytes' 11 _ (by omega) hsm.2.2.2.2.2.2.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro8c 9 _ k (by omega) hsm.2.2.2.2.2.2.2.2.1 hk)
    (fun _ k hk => readOnly_getMem_tdNode hro8c 11 _ k (by omega) hsm.2.2.2.2.2.2.2.2.2.2.1 hk)
    (fun hcl => hcl.2 9 (by omega) (by omega) _ hsm.2.2.2.2.2.2.2.2.1)
    (fun hcl => hcl.2 11 (by omega) (by omega) _ hsm.2.2.2.2.2.2.2.2.2.2.1)
    (by omega) hw8c
  obtain ⟨s9a, hr9a, hpc9a, hs9a_8, hreg9a, hmem9a⟩ := openRuns_combine_tails
    (ts0 := [tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))])
    (ts1 := [tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)), tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1))])
    (by simp) (rfl : openInstr 4770 = .base (.SLLI .x5 .x5 (12#6)))
    (rfl : openInstr 4771 = .base (.OR .x8 .x8 .x5)) (by decide) hpc9
    (fun hcl => (hreg9 .x8 (by decide)).trans ((hreg8c .x8 (by decide)).trans ((hreg8b_7b .x8 (by decide)).trans (hs7b_8 hcl))))
    hs9_5
  have h4772 := step_SRLI (s := s9a) (by decide) hpc9a (rfl : openInstr 4772 = .base (.SRLI .x22 .x22 (1#6)))
  set s10 := (s9a.setReg .x22 (s9a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4773)
  have hs10_22 : s10.getReg .x22 = BitVec.ofNat 64 (g >>> 12) := by
    have h9_22 : s9a.getReg .x22 = BitVec.ofNat 64 (g >>> 11) :=
      (hreg9a .x22 (by decide)).trans ((hreg9 .x22 (by decide)).trans ((hreg8c .x22 (by decide)).trans hs8b_22))
    simp only [s10, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, h9_22,
      show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 11) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    rw [show (g >>> 11) >>> 1 = g >>> 12 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hbt10 : BaseTableReady s10 := baseTableReady_of_lowEq hbt7b (fun a ha => (by simp [s10, hmem9a] : s10.getMem a = s9.getMem a).trans ((hp9 a (by omega)).trans (hmem8c7 a)))
  have htbl9 : SlowTablesState s9 true := slowTablesState_of_eq htbl7b (fun a _ _ => (hp9 a (by omega)).trans (hmem8c7 a))
  obtain ⟨s10a, hr10a, hpc10a, hs10a_22, hs10a_10, hreg10a, hmem10a⟩ :=
    openRuns_lvl_addr_inmem (codeAt_of_list_eq 4773 (lvlAddrInMemCode .x10 13) (by decide) rfl)
      rfl (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) (by decide) hs10_22 hbt10
  rw [div2_ushr_eq g 12 13] at hs10a_22
  have h4779 := step_SRLI (s := s10a) (by decide) hpc10a (rfl : openInstr 4779 = .base (.SRLI .x22 .x22 (1#6)))
  set s10b := (s10a.setReg .x22 (s10a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt 4780)
  have hs10b_22 : s10b.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) := by
    simp only [s10b, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs10a_22,
      show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 13) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega), capLeafOf_eq_div16384]
    rw [show (g >>> 13) >>> 1 = g >>> 14 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hreg10b_9a : RegsEqExcept [.x5, .x10, .x22] s9a s10b := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have e1 : s10b.getReg reg = s10a.getReg reg := by simp [s10b, getReg_setReg_ne' .x22 reg h22'.symm]
    have e2 : s10.getReg reg = s9a.getReg reg := by simp [s10, getReg_setReg_ne' .x22 reg h22'.symm]
    exact e1.trans ((hreg10a reg (by simp [h5', h22', h10'])).trans e2)
  have hreg10b_9 : RegsEqExcept [.x5, .x8, .x10, .x22] s9 s10b := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    exact (hreg10b_9a reg (by simp [h5', h10', h22'])).trans (hreg9a reg (by simp [h5', h8']))
  have hmem10b9 : ∀ a, s10b.getMem a = s9.getMem a := fun a => by simp [s10b, hmem10a, s10, hmem9a]
  obtain ⟨s10c, hr10c, hpc10c, hs10c_1, hreg10c, hmem10c⟩ :=
    call_ld_jalr (r := r2) (tblOff := 1344) (tgt := pcCopy29 r2)
      (rfl : openInstr 4780 = .base (.LD .x6 .x14 (1344#12)))
      (rfl : openInstr 4781 = .base (.JALR .x1 .x6 (0#12)))
      (by decide) (by omega) (by omega) rfl
      ((hreg10b_9 .x14 (by decide)).trans hs9_14)
      (by rw [hmem10b9]; exact (slowTbl_get' htbl9 r2).1)
  have hmem10c9 : ∀ a, s10c.getMem a = s9.getMem a := fun a => (hmem10c a).trans (hmem10b9 a)
  have hro10c : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s10c :=
    fun a ha => (hmem10c9 a).trans (ReadOnlyPreserved.of_proofWrite hro8c hp9 a ha)
  have hw10c := writerState_of_mem_eq hw9 hmem10c9
    ((hreg10c .x25 (by decide)).trans (hreg10b_9 .x25 (by decide)))
    ((hreg10c .x12 (by decide)).trans (hreg10b_9 .x12 (by decide)))
  set r3 := copy29NextR r2
  have hreg10c_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s10c := fun reg hreg => by
    have h1' : reg ≠ .x1 := fun h => hreg (by simp [h])
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h19' : reg ≠ .x19 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg10c reg (by simp [h1', h6'])).trans ((hreg10b_9 reg (by simp [h5', h8', h10', h22'])).trans
      ((hreg9 reg (by simp [h5', h6', h10', h12', h14', h19', h25'])).trans
        ((hreg8c reg (by simp [h1', h6'])).trans ((hreg8b_7b reg (by simp [h10', h22', h28'])).trans (hreg7b_base reg hreg)))))
  have hs10c_10 : s10c.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 13 + nodeOffset 13 ((g >>> 12) ^^^ 1)) :=
    (hreg10c .x10 (by decide)).trans ((by simp [s10b, getReg_setReg_ne'] : s10b.getReg .x10 = s10a.getReg .x10).trans hs10a_10)
  obtain ⟨s11, hr11, hpc11, hs11_14, hs11_5, hreg11, hp11, hw11⟩ := openRuns_sub_copy29 (r := r2) (retPc := 4782)
    (d := tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) hpc10c hs10c_1
    ((hreg10c_base .x11 (by decide)).trans hinv.rx11) hs10c_10
    (by have h1 := levelBase_align8' 13 (by omega); have h2 := nodeOffset_align8' 13 ((g >>> 12) ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 13 _ (by omega) hsm.2.2.2.2.2.2.2.2.2.2.2.2.1; omega)
    (fun _ k hk => readOnly_getMem_tdNode hro10c 13 _ k (by omega) hsm.2.2.2.2.2.2.2.2.2.2.2.2.1 hk)
    (fun hcl => hcl.2 13 (by omega) (by omega) _ hsm.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (by omega) hw10c
  set ts5 : List (BitVec 6) :=
    ([tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))] ++
     [tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)), tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1))]) ++
     [tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))]
  have hts5_eq : ts5 = recordTails (tdNode trapdoor) i := by
    rw [hrec_eq.2]; simp only [ts5, g, decide_eq_true_iff, hhas8, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  obtain ⟨s11a, hr11a, hpc11a, hs11a_8, hreg11a, hmem11a⟩ := openRuns_combine_tails
    (ts0 := [tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))] ++
            [tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)), tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1))])
    (ts1 := [tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))])
    (by simp) (rfl : openInstr 4782 = .base (.SLLI .x5 .x5 (24#6)))
    (rfl : openInstr 4783 = .base (.OR .x8 .x8 .x5)) (by decide) hpc11
    (fun hcl => (hreg11 .x8 (by decide)).trans ((hreg10c .x8 (by decide)).trans ((hreg10b_9a .x8 (by decide)).trans (hs9a_8 hcl))))
    (fun hcl => by simpa [bitsOf6] using hs11_5 hcl)
  have hreg11a_base : RegsEqExcept [.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x19, .x22, .x25, .x28] s s11a := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
    have h25' : reg ≠ .x25 := fun h => hreg (by simp [h])
    exact (hreg11a reg (by simp [h5', h8'])).trans ((hreg11 reg (by simp [h5', h6', h10', h12', h14', h25'])).trans (hreg10c_base reg hreg))
  have hp11a7b : ProofWritePreserves s7b s11a :=
    ProofWritePreserves.trans (fun a _ => hmem8c7 a) <|
      hp9.trans <| ProofWritePreserves.trans (fun a _ => hmem10c9 a) <| hp11.trans (fun _ _ => hmem11a _)
  have ht11a : TailState (CleanTrapdoor trapdoor) s11a tails flushes :=
    TailState.of_proofWrite ht7b hp11a7b
      ((hreg11a_base .x15 (by decide)).trans (hreg7b_base .x15 (by decide)).symm)
      ((hreg11a_base .x16 (by decide)).trans (hreg7b_base .x16 (by decide)).symm)
      ((hreg11a_base .x17 (by decide)).trans (hreg7b_base .x17 (by decide)).symm)
  obtain ⟨s12, hr12, hpc12, hreg12, htw12, ht12⟩ := openRuns_tailMerge_neg (ts := ts5)
    (by simp [ts5]) (by simp [ts5]) (codeAt_of_list_eq 4784 (tailMergeCode 30) (by decide) rfl)
    hpc11a hs11a_8 ht11a hbd_t
  have hro12 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s12 :=
    readOnlyPreserved_of_tailWrite (ReadOnlyPreserved.of_proofWrite hro7b hp11a7b) htw12
  have hbt12 : BaseTableReady s12 := baseTableReady_of_lowEq hbt7b (fun a ha =>
    ((tailWrite_pres_low htw12).1 a ha).trans ((proofWrite_pres_low hp11a7b).1 a ha))
  have htbl12 : SlowTablesState s12 true := slowTablesState_of_eq htbl7b (fun a h1 h2 =>
    ((tailWrite_pres_low htw12).2.2 a h1 h2).trans ((proofWrite_pres_low hp11a7b).2.2 a h1 h2))
  have hcm12 : CapMarks15State s12 positions ordinal := capMarks15State_of_lowEq hcm7b (fun a h1 h2 =>
    ((tailWrite_pres_low htw12).2.1 a h1 h2).trans ((proofWrite_pres_low hp11a7b).2.1 a h1 h2))
  have hfwd_eq : written ++ bitsToBytes (tdSalt trapdoor i) 24 ++ bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx i)) 32 ++
      bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx i)) 32 ++ bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32 ++
      bitsToBytes (tdNode trapdoor 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29 =
      written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i := by
    rw [hrec_eq.1]; simp only [g, decide_eq_true_iff, hhas8, ↓reduceIte, List.append_assoc, List.append_nil]
  have hw12 : WriterState (CleanTrapdoor trapdoor) s12 r3 false
      (base + 24 + 96 + 120 + copy29x2NextDstOff r0 + copy29x2NextDstOff r1 + copy29NextDstOff r2 0) 0
      (written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i) := by
    rw [← hfwd_eq]
    have hw11a := writerState_of_mem_eq hw11 hmem11a (hreg11a .x25 (by decide)) (hreg11a .x12 (by decide))
    exact writerState_of_tailWrite hw11a htw12 (hreg12 .x25 (by decide)) (hreg12 .x12 (by decide))
  have ht12' : TailState (CleanTrapdoor trapdoor) s12 (tails ++ recordTails (tdNode trapdoor) i)
      (flushes + if (6 * tails.length) % 64 + 6 * ts5.length < 64 then 0 else 1) := by
    rw [← hts5_eq]; exact ht12
  have hreg12_b : ∀ reg, reg ∉ ([.x1, .x5, .x6, .x8, .x10, .x12, .x14, .x15, .x16, .x17, .x19, .x22, .x25, .x28] : List Reg) →
      s12.getReg reg = s.getReg reg := fun reg hreg =>
    (hreg12 reg (reg_not_mem_sub (by decide) hreg)).trans
      (hreg11a_base reg (reg_not_mem_sub (by decide) hreg))
  have hs12_14 : s12.getReg .x14 = BitVec.ofNat 64 (8 * r3.val) :=
    (hreg12 .x14 (by decide)).trans ((hreg11a .x14 (by decide)).trans hs11_14)
  have hs12_22 : s12.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) :=
    (hreg12 .x22 (by decide)).trans ((hreg11a .x22 (by decide)).trans ((hreg11 .x22 (by decide)).trans ((hreg10c .x22 (by decide)).trans hs10b_22)))
  obtain ⟨sEnd, hrEnd, hinvEnd⟩ := openRuns_slow_epilogue (isTail := false) hord hpc12
    (fun _ => (hreg12_b .x2 (by decide)).trans hinv.rx2) ((hreg12_b .x3 (by decide)).trans hinv.rx3)
    ((hreg12_b .x4 (by decide)).trans hinv.rx4) ((hreg12_b .x7 (by decide)).trans hinv.rx7)
    ((hreg12_b .x9 (by decide)).trans hinv.rx9) ((hreg12_b .x11 (by decide)).trans hinv.rx11)
    ((hreg12_b .x13 (by decide)).trans hinv.rx13) hs12_14 ((hreg12_b .x18 (by decide)).trans hinv.rx18)
    ((hreg12_b .x20 (by decide)).trans hinv.rx20) ((hreg12_b .x21 (by decide)).trans hinv.rx21)
    hs12_22 ((hreg12_b .x23 (by decide)).trans hinv.rx23) ((hreg12_b .x24 (by decide)).trans hinv.rx24)
    ((hreg12_b .x26 (by decide)).trans hinv.rx26) ((hreg12_b .x27 (by decide)).trans hinv.rx27)
    ((hreg12_b .x29 (by decide)).trans hinv.rx29) ((hreg12_b .x30 (by decide)).trans hinv.rx30)
    ((hreg12_b .x31 (by decide)).trans hinv.rx31) hro12 hbt12 hcm12 htbl12 hw12 ht12'
  set cycRem := 1 + (1 + 5 + 1 + 5) + (2 + (copy29x2SubCode r1).length) + 2 + (1 + 6 + 1) +
    (2 + (copy29SubCode r2).length) + 2 + 5 + (if ordinal + 1 = positions.card then 4 else 8)
  have hfl_eq : (if (6 * tails.length) % 64 + 6 * ts5.length < 64 then 0 else 1) =
      (if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
    rw [hts5_eq]
  refine ⟨cycRem, r3,
    base + 24 + 96 + 120 + copy29x2NextDstOff r0 + copy29x2NextDstOff r1 + copy29NextDstOff r2 0, sEnd, ?_, ?_, ?_⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrEnd
    have htot := (((((((((((h4713.trans h4756).trans hr8a).trans h4762).trans hr8b).trans hr8c).trans hr9).trans hr9a).trans h4772).trans hr10a).trans h4779).trans
      ((((hr10c.trans hr11).trans hr11a).trans hr12).trans hrEnd))
    have heq_c : 1 + 1 + 5 + 1 + 5 + 2 + (copy29x2SubCode r1).length + 2 + 1 + 6 + 1 +
        (2 + (copy29SubCode r2).length + 2 +
        (5 + 4 * (if 6 * tails.length % 64 + 6 * ts5.length < 64 then 0 else 1)) +
        (if ordinal + 1 = positions.card then 4 else 8)) =
        cycRem + 4 * (if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
      rw [hfl_eq]; unfold cycRem; split_ifs <;> omega
    rw [heq_c] at htot; exact htot
  · have ha := slowMidSkip8_amort r0
    have hle : slowEntryCyc r0 + 4 + (slowMidPreCyc r0 cL0 + cycRem) ≤ slowMidSkip8Cyc r0 := by
      unfold slowMidSkip8Cyc slowMidPreCyc cycRem; dsimp only [r1, r2]; split_ifs <;> omega
    exact le_trans (by dsimp only [r3, r2, r1]; omega) ha
  · rw [← hfl_eq]; by_cases hl : ordinal + 1 = positions.card <;> simp only [hl, ↓reduceIte, ↓reduceDIte] at hinvEnd ⊢ <;> exact hinvEnd

/-- Execute `slow_mid` (`4660 → rec_r{rEnd}` or `cap_pass`) for `5,592,064 ≤ g < 5,592,384`. -/
theorem openRuns_slow_mid {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hord : ordinal < positions.card)
    (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg1 : 5592064 ≤ ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)
    (hg2 : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592384)
    (hpc : s.pc = pcAt 4660)
    (hinv : SlowEntryInv trapdoor positions ordinal r0 base written tails flushes true
              ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) (s.setPC (pcAt PC_slow_body))) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    ∃ cycNf rEnd baseEnd s',
      OpenRuns s (cycNf + 4 * fl) (cycNf + 4 * fl) s' ∧
      8 * (slowEntryCyc r0 + 4 + cycNf) + phi8 rEnd ≤ 3453 + phi8 r0 ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) true s' := by
  obtain ⟨cL0, s7b, hcL0, hrPre, hpc7b, hs7b_5, hs7b_14, hs7b_22, hs7b_8, hreg7b_base, hro7b, hbt7b, htbl7b, hcm7b, hw7b, ht7b⟩ :=
    openRuns_slow_mid_prefix hord hbd_w hg1 hg2 hpc hinv
  by_cases hhas8 : ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 7) % 4 < 2
  · obtain ⟨cycRem, rEnd, baseEnd, s', hrRem, ham, hpost⟩ :=
      openRuns_slow_mid_has8 hord hbd_w hbd_t hg1 hg2 hcL0 hhas8 hinv hpc7b hs7b_5 hs7b_14 hs7b_22 hs7b_8
        hreg7b_base hro7b hbt7b htbl7b hcm7b hw7b ht7b
    exact ⟨slowMidPreCyc r0 cL0 + cycRem, rEnd, baseEnd, s',
      by simpa only [Nat.add_assoc] using hrPre.trans hrRem, ham,
      by by_cases hl : ordinal + 1 = positions.card <;> simp only [hl, ↓reduceIte, ↓reduceDIte] at hpost ⊢ <;> exact hpost⟩
  · obtain ⟨cycRem, rEnd, baseEnd, s', hrRem, ham, hpost⟩ :=
      openRuns_slow_mid_skip8 hord hbd_w hbd_t hg1 hg2 hcL0 hhas8 hinv hpc7b hs7b_5 hs7b_14 hs7b_22 hs7b_8
        hreg7b_base hro7b hbt7b htbl7b hcm7b hw7b ht7b
    exact ⟨slowMidPreCyc r0 cL0 + cycRem, rEnd, baseEnd, s',
      by simpa only [Nat.add_assoc] using hrPre.trans hrRem, ham,
      by by_cases hl : ordinal + 1 = positions.card <;> simp only [hl, ↓reduceIte, ↓reduceDIte] at hpost ⊢ <;> exact hpost⟩

end CommitGolfCandidate.MoonOpen
