import CommitGolfCandidate.MoonOpenRec
import CommitGolfCandidate.MoonOpenEpilogue

/-! 8-way cyclic cap frontier pass (`L15..L23`, `PC 6793..7222`) and end-to-end opening
execution theorem `opening_exec_spec` proving `exec.cycles ≤ 65740` for `positions.card = BATCH`
and exact `referenceProof` byte equality under `CleanTrapdoor trapdoor`. -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Cap Pass PC Tables, Potential Function `cphi8`, and Pure Level Helpers -/

def pcCapPair (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_cap_pair_r0 | 1 => PC_cap_pair_r1 | 2 => PC_cap_pair_r2 | 3 => PC_cap_pair_r3
  | 4 => PC_cap_pair_r4 | 5 => PC_cap_pair_r5 | 6 => PC_cap_pair_r6 | _ => PC_cap_pair_r7

def pcCapTnf (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_cap_tnf_r0 | 1 => PC_cap_tnf_r1 | 2 => PC_cap_tnf_r2 | 3 => PC_cap_tnf_r3
  | 4 => PC_cap_tnf_r4 | 5 => PC_cap_tnf_r5 | 6 => PC_cap_tnf_r6 | _ => PC_cap_tnf_r7

def pcCapSame (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_cap_same_r0 | 1 => PC_cap_same_r1 | 2 => PC_cap_same_r2 | 3 => PC_cap_same_r3
  | 4 => PC_cap_same_r4 | 5 => PC_cap_same_r5 | 6 => PC_cap_same_r6 | _ => PC_cap_same_r7

/-- Scaled (`× 8`) cap-pass residue potential (`max = 80`), satisfying `cphi8 r ≤ phi8 r`! -/
def cphi8 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => 0 | 1 => 40 | 2 => 56 | 3 => 8 | 4 => 24 | 5 => 80 | 6 => 32 | _ => 48

def capPairNf (r : Fin 8) : Nat :=
  15 + (copy29Code r .x10 0 .x5 0 false false false).length

private theorem cap_amort (r : Fin 8) :
    8 * capPairNf r + cphi8 (copy29NextR r) = 272 + cphi8 r := by
  fin_cases r <;> decide

private theorem cphi8_le_phi8 (r : Fin 8) : cphi8 r ≤ phi8 r := by
  fin_cases r <;> decide

private theorem wbuf_sub_cphi8_le (r : Fin 8) : 8 * (2 + 5 * r.val) ≤ 248 + cphi8 r := by
  fin_cases r <;> decide

private theorem capMarkOff_props (l : Nat) (hl1 : 15 ≤ l) (hl2 : l ≤ 23) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) ∧
    capMarkOff (l + 1) + levelSize (l + 1) ≤ 832 ∧
    1 ≤ levelSize l / 2 := by
  interval_cases l <;> decide

private theorem cap_pairs_sum :
    (∑ step ∈ Finset.range 9, levelSize (15 + step) / 2) = 341 := by
  decide

private theorem cap_odd_overhead_sum :
    (∑ step ∈ Finset.range 9, (if levelSize (15 + step) % 2 = 1 then 4 else 2)) = 26 := by
  decide

/-- Active level `l` cap marks in `[512 + capMarkOff l, 512 + capMarkOff l + levelSize l)`. -/
def CapLevelMarks (s : MachineState) (positions : Positions) (l : Nat) : Prop :=
  ∀ idx < levelSize l,
    s.getByte (BitVec.ofNat 64 (512 + capMarkOff l + idx)) =
      if capMark positions l idx then 1#8 else 0#8

private theorem capLevelMarks_of_lowEq {s s' : MachineState} {positions : Positions} {l : Nat}
    (hl1 : 15 ≤ l) (hl2 : l ≤ 24)
    (hm : CapLevelMarks s positions l)
    (heq : ∀ a : Word, 512 ≤ a.toNat → a.toNat < 1344 → s'.getMem a = s.getMem a) :
    CapLevelMarks s' positions l := by
  have hmax : capMarkOff l + levelSize l ≤ 832 := by interval_cases l <;> decide
  intro idx hidx
  have hq : 512 + capMarkOff l + idx < 1344 := by omega
  have hal := alignToDword_ofNat_eq (8 * ((512 + capMarkOff l + idx) / 8))
    ((512 + capMarkOff l + idx) % 8) (by omega) (by omega)
  rw [show 8 * ((512 + capMarkOff l + idx) / 8) + (512 + capMarkOff l + idx) % 8 =
      512 + capMarkOff l + idx by omega] at hal
  have hmem : s'.getMem (alignToDword (BitVec.ofNat 64 (512 + capMarkOff l + idx))) =
      s.getMem (alignToDword (BitVec.ofNat 64 (512 + capMarkOff l + idx))) := by
    apply heq
    · rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  exact (by simp only [MachineState.getByte, hmem] : s'.getByte _ = s.getByte _).trans (hm idx hidx)

private theorem capMark15_of_state {s : MachineState} {positions : Positions}
    (hcm : CapMarks15State s positions positions.card) :
    CapLevelMarks s positions 15 := by
  intro idx hidx
  have hidx342 : idx < 342 := by rw [levelSize_15] at hidx; exact hidx
  have hoff15 : capMarkOff 15 = 0 := by decide
  rw [hoff15, Nat.add_zero, hcm.l15 idx hidx342]
  have heq : capMark15Prefix positions positions.card idx = capMark positions 15 idx := by
    unfold capMark15Prefix
    rw [capMark_15, List.take_of_length_le (by simp)]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq, Finset.mem_sort]
  rw [heq]

private theorem setByte_cap_mem_pres {s : MachineState} {dst : Nat} {b : Byte}
    (hlo : 512 ≤ dst) (hhi : dst < 1344) :
    (∀ a : Word, a.toNat < 512 → (s.setByte (BitVec.ofNat 64 dst) b).getMem a = s.getMem a) ∧
    (∀ a : Word, 4294971424 ≤ a.toNat → (s.setByte (BitVec.ofNat 64 dst) b).getMem a = s.getMem a) := by
  have hal : alignToDword (BitVec.ofNat 64 dst) = BitVec.ofNat 64 (8 * (dst / 8)) := by
    simpa only [show 8 * (dst / 8) + dst % 8 = dst by omega] using
      alignToDword_ofNat_eq (8 * (dst / 8)) (dst % 8) (by omega) (by omega)
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · simp only [MachineState.setByte]
    apply MachineState.getMem_setMem_ne
    rw [hal]; intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha; omega
  · simp only [MachineState.setByte]
    apply MachineState.getMem_setMem_ne
    rw [hal]; intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha; omega

private theorem setByte_cap_getByte_ne {s : MachineState} {dst query : Nat} {b : Byte}
    (hdst : dst < 2 ^ 64) (hq : query < 2 ^ 64) (hne : query ≠ dst) :
    (s.setByte (BitVec.ofNat 64 dst) b).getByte (BitVec.ofNat 64 query) =
      s.getByte (BitVec.ofNat 64 query) := by
  rw [set_byte_read]
  have hne' : BitVec.ofNat 64 query ≠ BitVec.ofNat 64 dst := by
    intro h; have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hdst] at hn; omega
  simp only [hne', ↓reduceIte]

/-! ### 2. Residue Dispatch (`PC 6809..6823`, `≤ 7` cycles) -/

private theorem openRuns_cap_dispatch {s : MachineState} (r : Fin 8)
    (hpc : s.pc = pcAt 6809)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r.val)) :
    ∃ cyc s',
      OpenRuns s cyc cyc s' ∧
      cyc ≤ 7 ∧
      s'.pc = pcAt (pcCapPair r) ∧
      RegsEqExcept [.x6] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have h0 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 6809 = .base (.ADDI .x6 .x0 (32#12)))
  set s1 := (s.setReg .x6 (s.getReg .x0 + signExtend12 (32#12))).setPC (pcAt 6810)
  have hs1_6 : s1.getReg .x6 = BitVec.ofNat 64 32 := by
    simp [s1, show s.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 32 (by omega)]
  have hs1_14 : s1.getReg .x14 = BitVec.ofNat 64 (8 * r.val) := by simp [s1, getReg_setReg_ne', hx14]
  fin_cases r
  · -- r = 0 (6 cyc): 6809, 6810(nt), 6811, 6812(nt), 6813(nt), 6814(JAL -> 6824)
    have h1 := step_BGEU_not_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13))) (by rw [hs1_14, hs1_6]; decide)
    set s2 := s1.setPC (pcAt 6811)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6811 = .base (.ADDI .x6 .x0 (16#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (16#12))).setPC (pcAt 6812)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 16 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega)]
    have hs3_14 : s3.getReg .x14 = 0#64 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_not_taken (s := s3) (by decide) rfl (rfl : openInstr 6812 = .base (.BGEU .x14 .x6 (12#13))) (by rw [hs3_14, hs3_6]; decide)
    set s4 := s3.setPC (pcAt 6813)
    have h4 := step_BNE_not_taken (s := s4) (by decide) rfl (rfl : openInstr 6813 = .base (.BNE .x14 .x0 (1004#13))) (by simp [s4, hs3_14]; rfl)
    set s5 := s4.setPC (pcAt 6814)
    have h5 := step_JAL (s := s5) (by decide) rfl (rfl : openInstr 6814 = .base (.JAL .x0 (40#21)))
      (by simpa only [show 4 * (6824 - 6814) = 40 by decide] using pcAt_add_pos21 6814 6824 (by omega) (by omega))
    set s6 := (s5.setReg .x0 (pcAt 6815)).setPC (pcAt 6824)
    exact ⟨6, s6, ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s6, s5, s4, s3, s2, s1, setReg_x0_eq]⟩
  · -- r = 1 (5 cyc): 6809, 6810(nt), 6811, 6812(nt), 6813(BNE -> 7064)
    have h1 := step_BGEU_not_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13))) (by rw [hs1_14, hs1_6]; decide)
    set s2 := s1.setPC (pcAt 6811)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6811 = .base (.ADDI .x6 .x0 (16#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (16#12))).setPC (pcAt 6812)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 16 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega)]
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 8 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_not_taken (s := s3) (by decide) rfl (rfl : openInstr 6812 = .base (.BGEU .x14 .x6 (12#13))) (by rw [hs3_14, hs3_6]; decide)
    set s4 := s3.setPC (pcAt 6813)
    have h4 := step_BNE_taken (s := s4) (by decide) rfl (rfl : openInstr 6813 = .base (.BNE .x14 .x0 (1004#13)))
      (by rw [show s4.getReg .x14 = BitVec.ofNat 64 8 by simp [s4, hs3_14], show s4.getReg .x0 = 0#64 from rfl]; decide)
      (by simpa only [show 4 * (7064 - 6813) = 1004 by decide] using pcAt_add_pos13 6813 7064 (by omega) (by omega))
    set s5 := s4.setPC (pcAt 7064)
    exact ⟨5, s5, (((h0.trans h1).trans h2).trans h3).trans h4, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s5, s4, s3, s2, s1, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s5, s4, s3, s2, s1]⟩
  · -- r = 2 (5 cyc): 6809, 6810(nt), 6811, 6812(t->6815), 6815(BEQ->6915)
    have h1 := step_BGEU_not_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13))) (by rw [hs1_14, hs1_6]; decide)
    set s2 := s1.setPC (pcAt 6811)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6811 = .base (.ADDI .x6 .x0 (16#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (16#12))).setPC (pcAt 6812)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 16 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega)]
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 16 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_taken (s := s3) (by decide) rfl (rfl : openInstr 6812 = .base (.BGEU .x14 .x6 (12#13)))
      (by rw [hs3_14, hs3_6])
      (by simpa only [show 4 * (6815 - 6812) = 12 by decide] using pcAt_add_pos13 6812 6815 (by omega) (by omega))
    set s4 := s3.setPC (pcAt 6815)
    have h4 := step_BEQ_taken (s := s4) (by decide) rfl (rfl : openInstr 6815 = .base (.BEQ .x14 .x6 (400#13)))
      (by simp [s4, hs3_14, hs3_6])
      (by simpa only [show 4 * (6915 - 6815) = 400 by decide] using pcAt_add_pos13 6815 6915 (by omega) (by omega))
    set s5 := s4.setPC (pcAt 6915)
    exact ⟨5, s5, (((h0.trans h1).trans h2).trans h3).trans h4, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s5, s4, s3, s2, s1, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s5, s4, s3, s2, s1]⟩
  · -- r = 3 (6 cyc): 6809, 6810(nt), 6811, 6812(t->6815), 6815(nt), 6816(JAL->7166)
    have h1 := step_BGEU_not_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13))) (by rw [hs1_14, hs1_6]; decide)
    set s2 := s1.setPC (pcAt 6811)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6811 = .base (.ADDI .x6 .x0 (16#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (16#12))).setPC (pcAt 6812)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 16 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega)]
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 24 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_taken (s := s3) (by decide) rfl (rfl : openInstr 6812 = .base (.BGEU .x14 .x6 (12#13)))
      (by rw [hs3_14, hs3_6]; decide)
      (by simpa only [show 4 * (6815 - 6812) = 12 by decide] using pcAt_add_pos13 6812 6815 (by omega) (by omega))
    set s4 := s3.setPC (pcAt 6815)
    have h4 := step_BEQ_not_taken (s := s4) (by decide) rfl (rfl : openInstr 6815 = .base (.BEQ .x14 .x6 (400#13)))
      (by simp [s4, hs3_14, hs3_6])
    set s5 := s4.setPC (pcAt 6816)
    have h5 := step_JAL (s := s5) (by decide) rfl (rfl : openInstr 6816 = .base (.JAL .x0 (1400#21)))
      (by simpa only [show 4 * (7166 - 6816) = 1400 by decide] using pcAt_add_pos21 6816 7166 (by omega) (by omega))
    set s6 := (s5.setReg .x0 (pcAt 6817)).setPC (pcAt 7166)
    exact ⟨6, s6, ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s6, s5, s4, s3, s2, s1, setReg_x0_eq]⟩
  · -- r = 4 (6 cyc): 6809, 6810(t->6817), 6817, 6818(nt), 6819, 6820(BEQ->7017)
    have h1 := step_BGEU_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13)))
      (by rw [hs1_14, hs1_6]; decide)
      (by simpa only [show 4 * (6817 - 6810) = 28 by decide] using pcAt_add_pos13 6810 6817 (by omega) (by omega))
    set s2 := s1.setPC (pcAt 6817)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6817 = .base (.ADDI .x6 .x0 (48#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (48#12))).setPC (pcAt 6818)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 48 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 48 (by omega)]
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 32 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_not_taken (s := s3) (by decide) rfl (rfl : openInstr 6818 = .base (.BGEU .x14 .x6 (16#13))) (by rw [hs3_14, hs3_6]; decide)
    set s4 := s3.setPC (pcAt 6819)
    have h4 := step_ADDI (s := s4) (by decide) rfl (rfl : openInstr 6819 = .base (.ADDI .x6 .x0 (32#12)))
    set s5 := (s4.setReg .x6 (s4.getReg .x0 + signExtend12 (32#12))).setPC (pcAt 6820)
    have hs5_6 : s5.getReg .x6 = BitVec.ofNat 64 32 := by simp [s5, show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 32 (by omega)]
    have hs5_14 : s5.getReg .x14 = BitVec.ofNat 64 32 := by simp [s5, s4, getReg_setReg_ne', hs3_14]
    have h5 := step_BEQ_taken (s := s5) (by decide) rfl (rfl : openInstr 6820 = .base (.BEQ .x14 .x6 (788#13)))
      (by rw [hs5_14, hs5_6])
      (by simpa only [show 4 * (7017 - 6820) = 788 by decide] using pcAt_add_pos13 6820 7017 (by omega) (by omega))
    set s6 := s5.setPC (pcAt 7017)
    exact ⟨6, s6, ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s6, s5, s4, s3, s2, s1]⟩
  · -- r = 5 (7 cyc): 6809, 6810(t->6817), 6817, 6818(nt), 6819, 6820(nt), 6821(JAL->6863)
    have h1 := step_BGEU_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13)))
      (by rw [hs1_14, hs1_6]; decide)
      (by simpa only [show 4 * (6817 - 6810) = 28 by decide] using pcAt_add_pos13 6810 6817 (by omega) (by omega))
    set s2 := s1.setPC (pcAt 6817)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6817 = .base (.ADDI .x6 .x0 (48#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (48#12))).setPC (pcAt 6818)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 48 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 48 (by omega)]
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 40 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_not_taken (s := s3) (by decide) rfl (rfl : openInstr 6818 = .base (.BGEU .x14 .x6 (16#13))) (by rw [hs3_14, hs3_6]; decide)
    set s4 := s3.setPC (pcAt 6819)
    have h4 := step_ADDI (s := s4) (by decide) rfl (rfl : openInstr 6819 = .base (.ADDI .x6 .x0 (32#12)))
    set s5 := (s4.setReg .x6 (s4.getReg .x0 + signExtend12 (32#12))).setPC (pcAt 6820)
    have hs5_6 : s5.getReg .x6 = BitVec.ofNat 64 32 := by simp [s5, show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 32 (by omega)]
    have hs5_14 : s5.getReg .x14 = BitVec.ofNat 64 40 := by simp [s5, s4, getReg_setReg_ne', hs3_14]
    have h5 := step_BEQ_not_taken (s := s5) (by decide) rfl (rfl : openInstr 6820 = .base (.BEQ .x14 .x6 (788#13)))
      (by rw [hs5_14, hs5_6]; decide)
    set s6 := s5.setPC (pcAt 6821)
    have h6 := step_JAL (s := s6) (by decide) rfl (rfl : openInstr 6821 = .base (.JAL .x0 (168#21)))
      (by simpa only [show 4 * (6863 - 6821) = 168 by decide] using pcAt_add_pos21 6821 6863 (by omega) (by omega))
    set s7 := (s6.setReg .x0 (pcAt 6822)).setPC (pcAt 6863)
    exact ⟨7, s7, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq]⟩
  · -- r = 6 (5 cyc): 6809, 6810(t->6817), 6817, 6818(t->6822), 6822(BEQ->7114)
    have h1 := step_BGEU_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13)))
      (by rw [hs1_14, hs1_6]; decide)
      (by simpa only [show 4 * (6817 - 6810) = 28 by decide] using pcAt_add_pos13 6810 6817 (by omega) (by omega))
    set s2 := s1.setPC (pcAt 6817)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6817 = .base (.ADDI .x6 .x0 (48#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (48#12))).setPC (pcAt 6818)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 48 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 48 (by omega)]
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 48 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_taken (s := s3) (by decide) rfl (rfl : openInstr 6818 = .base (.BGEU .x14 .x6 (16#13)))
      (by rw [hs3_14, hs3_6])
      (by simpa only [show 4 * (6822 - 6818) = 16 by decide] using pcAt_add_pos13 6818 6822 (by omega) (by omega))
    set s4 := s3.setPC (pcAt 6822)
    have h4 := step_BEQ_taken (s := s4) (by decide) rfl (rfl : openInstr 6822 = .base (.BEQ .x14 .x6 (1168#13)))
      (by simp [s4, hs3_14, hs3_6])
      (by simpa only [show 4 * (7114 - 6822) = 1168 by decide] using pcAt_add_pos13 6822 7114 (by omega) (by omega))
    set s5 := s4.setPC (pcAt 7114)
    exact ⟨5, s5, (((h0.trans h1).trans h2).trans h3).trans h4, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s5, s4, s3, s2, s1, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s5, s4, s3, s2, s1]⟩
  · -- r = 7 (6 cyc): 6809, 6810(t->6817), 6817, 6818(t->6822), 6822(nt), 6823(JAL->6965)
    have h1 := step_BGEU_taken (s := s1) (by decide) rfl (rfl : openInstr 6810 = .base (.BGEU .x14 .x6 (28#13)))
      (by rw [hs1_14, hs1_6]; decide)
      (by simpa only [show 4 * (6817 - 6810) = 28 by decide] using pcAt_add_pos13 6810 6817 (by omega) (by omega))
    set s2 := s1.setPC (pcAt 6817)
    have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6817 = .base (.ADDI .x6 .x0 (48#12)))
    set s3 := (s2.setReg .x6 (s2.getReg .x0 + signExtend12 (48#12))).setPC (pcAt 6818)
    have hs3_6 : s3.getReg .x6 = BitVec.ofNat 64 48 := by simp [s3, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 48 (by omega)]
    have hs3_14 : s3.getReg .x14 = BitVec.ofNat 64 56 := by simp [s3, s2, getReg_setReg_ne', hs1_14]
    have h3 := step_BGEU_taken (s := s3) (by decide) rfl (rfl : openInstr 6818 = .base (.BGEU .x14 .x6 (16#13)))
      (by rw [hs3_14, hs3_6]; decide)
      (by simpa only [show 4 * (6822 - 6818) = 16 by decide] using pcAt_add_pos13 6818 6822 (by omega) (by omega))
    set s4 := s3.setPC (pcAt 6822)
    have h4 := step_BEQ_not_taken (s := s4) (by decide) rfl (rfl : openInstr 6822 = .base (.BEQ .x14 .x6 (1168#13)))
      (by simp [s4, hs3_14, hs3_6])
    set s5 := s4.setPC (pcAt 6823)
    have h5 := step_JAL (s := s5) (by decide) rfl (rfl : openInstr 6823 = .base (.JAL .x0 (568#21)))
      (by simpa only [show 4 * (6965 - 6823) = 568 by decide] using pcAt_add_pos21 6823 6965 (by omega) (by omega))
    set s6 := (s5.setReg .x0 (pcAt 6824)).setPC (pcAt 6965)
    exact ⟨6, s6, ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5, by omega, rfl,
      fun reg h => by have h6' : reg ≠ .x6 := fun hm => h (by simp [hm]); simp [s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setReg_ne' .x6 reg h6'.symm],
      fun _ => by simp [s6, s5, s4, s3, s2, s1, setReg_x0_eq]⟩

/-! ### 3. Parameterized Cap Pair Block (`cap_pair_r0..r7`, `PC 6824..7215`) -/

def brOff13 (src tgt : Nat) : BitVec 13 :=
  if src ≤ tgt then BitVec.ofNat 13 (4 * (tgt - src))
  else BitVec.ofNat 13 (8192 - 4 * (src - tgt))

private theorem pcAt_add_brOff13 (src tgt : Nat)
    (h1 : src ≤ tgt → 4 * (tgt - src) < 4096)
    (h2 : tgt < src → 4 * (src - tgt) ≤ 4096) :
    pcAt src + signExtend13 (brOff13 src tgt) = pcAt tgt := by
  unfold brOff13; split_ifs with h
  · exact pcAt_add_pos13 src tgt h (h1 h)
  · exact pcAt_add_neg13 src tgt (by omega) (h2 (by omega))

def capPairCode (r : Fin 8) : List Instruction :=
  let rNext := copy29NextR r
  let doff := copy29NextDstOff r 0
  let pc0 := pcCapPair r
  let pcTnf := pcCapTnf r
  let pcSame := pcCapSame r
  [.base (.LBU .x7 .x20 (0#12)),
   .base (.LBU .x8 .x20 (1#12)),
   .base (.BEQ .x7 .x8 (BitVec.ofNat 13 (4 * (pcSame - (pc0 + 2))))),
   .base (.SB .x22 .x4 (0#12)),
   .base (.SLLI .x10 .x7 (5#6)),
   .base (.ADD .x10 .x18 .x10)] ++
  copy29Code r .x10 0 .x5 0 false false false ++
  [.base (.ADDI .x25 .x25 (BitVec.ofNat 12 doff))] ++
  tailPush6Code ++
  [.base (.ADDI .x20 .x20 (2#12)),
   .base (.ADDI .x22 .x22 (1#12)),
   .base (.ADDI .x18 .x18 (96#12)),
   .base (.BNE .x22 .x23 (brOff13 (pcTnf + 3) (pcCapPair rNext))),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rNext.val))),
   .base (.JAL .x0 (jalOff (pcTnf + 5) PC_cap_lvl_end)),
   .base (.SB .x22 .x7 (0#12)),
   .base (.ADDI .x20 .x20 (2#12)),
   .base (.ADDI .x22 .x22 (1#12)),
   .base (.ADDI .x18 .x18 (96#12)),
   .base (.BNE .x22 .x23 (brOff13 (pcSame + 4) pc0)),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r.val))),
   .base (.JAL .x0 (jalOff (pcSame + 6) PC_cap_lvl_end))]

private theorem codeAt_cap_pair (r : Fin 8) : CodeAt (pcCapPair r) (capPairCode r) := by
  fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl

private theorem cap_pair_layout_ok (r : Fin 8) :
    pcCapPair r + 6 + (copy29Code r .x10 0 .x5 0 false false false).length + 1 + tailPush6Code.length = pcCapTnf r ∧
    pcCapTnf r + 6 = pcCapSame r ∧
    pcCapSame r + 7 ≤ OPEN_CODE_LEN ∧
    4 * (pcCapSame r - (pcCapPair r + 2)) < 4096 ∧
    (pcCapTnf r + 3 ≤ pcCapPair (copy29NextR r) → 4 * (pcCapPair (copy29NextR r) - (pcCapTnf r + 3)) < 4096) ∧
    (pcCapPair (copy29NextR r) < pcCapTnf r + 3 → 4 * ((pcCapTnf r + 3) - pcCapPair (copy29NextR r)) ≤ 4096) ∧
    4 * ((pcCapSame r + 4) - pcCapPair r) ≤ 4096 := by
  fin_cases r <;> decide

/-- Cap pair-loop invariant at `pcCapPair r` before processing pair `q` (`q < levelSize l / 2`) of level `l ∈ 15..23`. -/
private structure CapPairInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l q : Nat) (r : Fin 8) (base flushes : Nat)
    (written : List Byte) (tails : List (BitVec 6)) (s : MachineState) : Prop where
  hpc : s.pc = pcAt (pcCapPair r)
  rx4 : s.getReg .x4 = 1#64
  rx11 : s.getReg .x11 = mask40Word
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q)
  rx19 : s.getReg .x19 = BitVec.ofNat 64 (levelSize l)
  rx20 : s.getReg .x20 = BitVec.ofNat 64 (512 + capMarkOff l + 2 * q)
  rx22 : s.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q)
  rx23 : s.getReg .x23 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 (68719475936 + 32 * l + 8)
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (8 * l)
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (8 * 24)
  hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s
  hbt : BaseTableReady s
  hsrcM : CapLevelMarks s positions l
  hdstM : ∀ p < q, s.getByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + p)) =
      if capMark positions (l + 1) p then 1#8 else 0#8
  hw : WriterState (CleanTrapdoor trapdoor) s r false base 0 written
  ht : TailState (CleanTrapdoor trapdoor) s tails flushes

/-- Post-pair-loop state at `PC_cap_lvl_end = 7216` after all `levelSize l / 2` pairs of level `l` complete. -/
private structure CapLvlEndInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l : Nat) (r : Fin 8) (base flushes : Nat)
    (written : List Byte) (tails : List (BitVec 6)) (s : MachineState) : Prop where
  hpc : s.pc = pcAt PC_cap_lvl_end
  rx4 : s.getReg .x4 = 1#64
  rx11 : s.getReg .x11 = mask40Word
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r.val)
  rx19 : s.getReg .x19 = BitVec.ofNat 64 (levelSize l)
  rx20 : s.getReg .x20 = BitVec.ofNat 64 (512 + capMarkOff l + 2 * (levelSize l / 2))
  rx22 : s.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 (68719475936 + 32 * l + 8)
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (8 * l)
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (8 * 24)
  hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s
  hbt : BaseTableReady s
  hsrcM : CapLevelMarks s positions l
  hdstM : ∀ p < levelSize l / 2, s.getByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + p)) =
      if capMark positions (l + 1) p then 1#8 else 0#8
  hw : WriterState (CleanTrapdoor trapdoor) s r false base 0 written
  ht : TailState (CleanTrapdoor trapdoor) s tails flushes

/-- Single pair step of `cap_pair_r` at level `l ∈ 15..23`, pair `q < levelSize l / 2`. -/
private theorem openRuns_cap_pair_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {l q base flushes : Nat} {r : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hl1 : 15 ≤ l) (hl2 : l ≤ 23) (hq : q < levelSize l / 2)
    (hbd_w : base + 40 ≤ 8556390424) (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hinv : CapPairInv trapdoor positions l q r base flushes written tails s) :
    let mL := capMark positions l (2 * q)
    let mR := capMark positions l (2 * q + 1)
    let addFwd := if mL = mR then [] else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29 else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29
    let addTails := if mL = mR then [] else if !mL then [tail6 (tdNode trapdoor l (2 * q))] else [tail6 (tdNode trapdoor l (2 * q + 1))]
    let fl := if mL = mR then 0 else if (6 * tails.length) % 64 + 6 < 64 then 0 else 1
    let r' := if mL = mR then r else copy29NextR r
    let base' := if mL = mR then base else base + copy29NextDstOff r 0
    let isLast := q + 1 = levelSize l / 2
    let cycNf := (if mL = mR then 8 else capPairNf r) + (if isLast then 2 else 0)
    ∃ s' : MachineState,
      OpenRuns s (cycNf + 6 * fl) (cycNf + 6 * fl) s' ∧
      (if _hlast : q + 1 = levelSize l / 2 then
        CapLvlEndInv trapdoor positions l r' base' (flushes + fl) (written ++ addFwd) (tails ++ addTails) s'
      else
        CapPairInv trapdoor positions l (q + 1) r' base' (flushes + fl) (written ++ addFwd) (tails ++ addTails) s') := by
  have hcode := codeAt_cap_pair r
  have hlay := cap_pair_layout_ok r
  obtain ⟨hmo1, hmo2, _⟩ := capMarkOff_props l hl1 hl2
  have hsz1 : levelSize l / 2 ≤ levelSize (l + 1) := by rw [levelSize_step l (by omega)]; omega
  set pc0 := pcCapPair r
  set pcTnf := pcCapTnf r
  set pcSame := pcCapSame r
  set rNext := copy29NextR r
  set doff := copy29NextDstOff r 0
  set mL := capMark positions l (2 * q)
  set mR := capMark positions l (2 * q + 1)
  have hpair_lt : 2 * q + 1 < levelSize l := by omega
  have hm_next : capMark positions (l + 1) q = (mL || mR) := by
    rw [capMark_succ positions l q hl1]; simp only [hpair_lt, ↓reduceIte]; rfl
  -- Extract instructions from capPairCode r
  have hsplit : CodeAt pc0 ([.base (.LBU .x7 .x20 (0#12)), .base (.LBU .x8 .x20 (1#12)),
      .base (.BEQ .x7 .x8 (BitVec.ofNat 13 (4 * (pcSame - (pc0 + 2))))),
      .base (.SB .x22 .x4 (0#12)), .base (.SLLI .x10 .x7 (5#6)), .base (.ADD .x10 .x18 .x10)] ++
      (copy29Code r .x10 0 .x5 0 false false false ++
      ([.base (.ADDI .x25 .x25 (BitVec.ofNat 12 doff))] ++
      (tailPush6Code ++
      [.base (.ADDI .x20 .x20 (2#12)), .base (.ADDI .x22 .x22 (1#12)), .base (.ADDI .x18 .x18 (96#12)),
       .base (.BNE .x22 .x23 (brOff13 (pcTnf + 3) (pcCapPair rNext))),
       .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rNext.val))),
       .base (.JAL .x0 (jalOff (pcTnf + 5) PC_cap_lvl_end)),
       .base (.SB .x22 .x7 (0#12)), .base (.ADDI .x20 .x20 (2#12)), .base (.ADDI .x22 .x22 (1#12)),
       .base (.ADDI .x18 .x18 (96#12)), .base (.BNE .x22 .x23 (brOff13 (pcSame + 4) pc0)),
       .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r.val))),
       .base (.JAL .x0 (jalOff (pcSame + 6) PC_cap_lvl_end))])))) := by
    simpa only [capPairCode, List.append_assoc] using hcode
  have hcPre := hsplit.left
  have hcRest1 := hsplit.right
  have hcC29 := hcRest1.left
  have hcRest2 := hcRest1.right
  have hcAdd25 := hcRest2.left
  have hcRest3 := hcRest2.right
  have hcTP6 := hcRest3.left
  have hcTail := hcRest3.right
  have hpc_tnf_eq : pc0 + 6 + (copy29Code r .x10 0 .x5 0 false false false).length + 1 + tailPush6Code.length = pcTnf := hlay.1
  have hcTail' : CodeAt pcTnf [.base (.ADDI .x20 .x20 (2#12)), .base (.ADDI .x22 .x22 (1#12)), .base (.ADDI .x18 .x18 (96#12)),
      .base (.BNE .x22 .x23 (brOff13 (pcTnf + 3) (pcCapPair rNext))),
      .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rNext.val))),
      .base (.JAL .x0 (jalOff (pcTnf + 5) PC_cap_lvl_end)),
      .base (.SB .x22 .x7 (0#12)), .base (.ADDI .x20 .x20 (2#12)), .base (.ADDI .x22 .x22 (1#12)),
      .base (.ADDI .x18 .x18 (96#12)), .base (.BNE .x22 .x23 (brOff13 (pcSame + 4) pc0)),
      .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r.val))),
      .base (.JAL .x0 (jalOff (pcSame + 6) PC_cap_lvl_end))] := by
    have hpc_eq : pc0 + ([.base (.LBU .x7 .x20 (0#12)), .base (.LBU .x8 .x20 (1#12)),
        .base (.BEQ .x7 .x8 (BitVec.ofNat 13 (4 * (pcSame - (pc0 + 2))))),
        .base (.SB .x22 .x4 (0#12)), .base (.SLLI .x10 .x7 (5#6)), .base (.ADD .x10 .x18 .x10)] : List Instruction).length +
        (copy29Code r .x10 0 .x5 0 false false false).length +
        ([.base (.ADDI .x25 .x25 (BitVec.ofNat 12 doff))] : List Instruction).length +
        tailPush6Code.length = pcTnf := by
      simp only [List.length_cons, List.length_nil]; exact hpc_tnf_eq
    rw [hpc_eq] at hcTail; exact hcTail
  -- Step 0..1: LBU x7 x20 0; LBU x8 x20 1
  have hi0 : openInstr pc0 = .base (.LBU .x7 .x20 (0#12)) := by have h := hcPre.2 0 (by simp); simpa using h
  have hi1 : openInstr (pc0 + 1) = .base (.LBU .x8 .x20 (1#12)) := by have h := hcPre.2 1 (by simp); simpa using h
  have hi2 : openInstr (pc0 + 2) = .base (.BEQ .x7 .x8 (BitVec.ofNat 13 (4 * (pcSame - (pc0 + 2))))) := by
    have h := hcPre.2 2 (by simp); simpa using h
  have ha0_addr : s.getReg .x20 + signExtend12 (0#12) = BitVec.ofNat 64 (512 + capMarkOff l + 2 * q) := by
    rw [hinv.rx20, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have ha0_val : accessValid (s.getReg .x20 + signExtend12 (0#12)) 1 = true := by
    rw [ha0_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
  have h0 := step_LBU (s := s) (by omega) hinv.hpc hi0 ha0_val
  set s1 := (s.setReg .x7 ((s.getByte (s.getReg .x20 + signExtend12 (0#12))).zeroExtend 64)).setPC (pcAt (pc0 + 1))
  have hs1_20 : s1.getReg .x20 = BitVec.ofNat 64 (512 + capMarkOff l + 2 * q) := by simp [s1, getReg_setReg_ne', hinv.rx20]
  have ha1_addr : s1.getReg .x20 + signExtend12 (1#12) = BitVec.ofNat 64 (512 + capMarkOff l + (2 * q + 1)) := by
    rw [hs1_20, signExtend12_nonneg 1 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
  have ha1_val : accessValid (s1.getReg .x20 + signExtend12 (1#12)) 1 = true := by
    rw [ha1_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
  have h1 := step_LBU (s := s1) (by omega) rfl hi1 ha1_val
  set s2 := (s1.setReg .x8 ((s1.getByte (s1.getReg .x20 + signExtend12 (1#12))).zeroExtend 64)).setPC (pcAt (pc0 + 1 + 1))
  have hs2_7 : s2.getReg .x7 = if mL then 1#64 else 0#64 := by
    have e : s2.getReg .x7 = (s.getByte (s.getReg .x20 + signExtend12 (0#12))).zeroExtend 64 := by
      simp [s2, s1, getReg_setReg_ne']
    have hm := hinv.hsrcM (2 * q) (by omega)
    change s.getByte (BitVec.ofNat 64 (512 + capMarkOff l + 2 * q)) = if mL then 1#8 else 0#8 at hm
    rw [e, ha0_addr, hm]; cases mL <;> decide
  have hs2_8 : s2.getReg .x8 = if mR then 1#64 else 0#64 := by
    have e : s2.getReg .x8 = (s1.getByte (s1.getReg .x20 + signExtend12 (1#12))).zeroExtend 64 := by
      simp [s2]
    have hm := hinv.hsrcM (2 * q + 1) hpair_lt
    change s.getByte (BitVec.ofNat 64 (512 + capMarkOff l + (2 * q + 1))) = if mR then 1#8 else 0#8 at hm
    have hgb1 : s1.getByte (BitVec.ofNat 64 (512 + capMarkOff l + (2 * q + 1))) =
        s.getByte (BitVec.ofNat 64 (512 + capMarkOff l + (2 * q + 1))) := by
      simp [s1, getByte_setPC, getByte_setReg]
    rw [e, ha1_addr, hgb1, hm]
    cases mR <;> decide
  have hs2_pc : s2.pc = pcAt (pc0 + 2) := rfl
  by_cases hsame : mL = mR
  · -- Equal pair (`cap_same_r`): 8 cyc (+2 if last), no forward bytes, no tails
    have heq78 : s2.getReg .x7 = s2.getReg .x8 := by rw [hs2_7, hs2_8, hsame]
    have hbr_same : pcAt (pc0 + 2) + signExtend13 (BitVec.ofNat 13 (4 * (pcSame - (pc0 + 2)))) = pcAt pcSame :=
      pcAt_add_pos13 (pc0 + 2) pcSame (by omega) hlay.2.2.2.1
    have h2 := step_BEQ_taken (s := s2) (by omega) hs2_pc hi2 heq78 hbr_same
    set s3 := s2.setPC (pcAt pcSame)
    have hsb_ins : openInstr pcSame = .base (.SB .x22 .x7 (0#12)) := by
      have h := hcTail'.2 6 (by simp); rw [show pcTnf + 6 = pcSame by omega] at h; exact h
    have ha20_ins : openInstr (pcSame + 1) = .base (.ADDI .x20 .x20 (2#12)) := by
      have h := hcTail'.2 7 (by simp); rw [show pcTnf + 7 = pcSame + 1 by omega] at h; exact h
    have ha22_ins : openInstr (pcSame + 2) = .base (.ADDI .x22 .x22 (1#12)) := by
      have h := hcTail'.2 8 (by simp); rw [show pcTnf + 8 = pcSame + 2 by omega] at h; exact h
    have ha18_ins : openInstr (pcSame + 3) = .base (.ADDI .x18 .x18 (96#12)) := by
      have h := hcTail'.2 9 (by simp); rw [show pcTnf + 9 = pcSame + 3 by omega] at h; exact h
    have hbne_ins : openInstr (pcSame + 4) = .base (.BNE .x22 .x23 (brOff13 (pcSame + 4) pc0)) := by
      have h := hcTail'.2 10 (by simp); rw [show pcTnf + 10 = pcSame + 4 by omega] at h; exact h
    have hs3_22 : s3.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q) := by
      simp [s3, s2, s1, getReg_setReg_ne', hinv.rx22]
    have hsb_addr : s3.getReg .x22 + signExtend12 (0#12) = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q) := by
      rw [hs3_22, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsb_val : accessValid (s3.getReg .x22 + signExtend12 (0#12)) 1 = true := by
      rw [hsb_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
    have h3 := step_SB (s := s3) (by omega) rfl hsb_ins hsb_val
    set s4 := (s3.setByte (s3.getReg .x22 + signExtend12 (0#12)) ((s3.getReg .x7).truncate 8)).setPC (pcAt (pcSame + 1))
    have h4 := step_ADDI (s := s4) (by omega) rfl ha20_ins
    set s5 := (s4.setReg .x20 (s4.getReg .x20 + signExtend12 (2#12))).setPC (pcAt (pcSame + 1 + 1))
    have h5 := step_ADDI (s := s5) (by omega) rfl ha22_ins
    set s6 := (s5.setReg .x22 (s5.getReg .x22 + signExtend12 (1#12))).setPC (pcAt (pcSame + 2 + 1))
    have h6 := step_ADDI (s := s6) (by omega) rfl ha18_ins
    set s7 := (s6.setReg .x18 (s6.getReg .x18 + signExtend12 (96#12))).setPC (pcAt (pcSame + 3 + 1))
    have hs7_pc : s7.pc = pcAt (pcSame + 4) := rfl
    have hs7_22 : s7.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + (q + 1)) := by
      simp only [s7, s6, s5, s4, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs3_22,
        signExtend12_nonneg 1 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have hs7_23 : s7.getReg .x23 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2) := by
      simp [s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx23]
    have hs7_20 : s7.getReg .x20 = BitVec.ofNat 64 (512 + capMarkOff l + 2 * (q + 1)) := by
      simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hinv.rx20,
        signExtend12_nonneg 2 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have hs7_18 : s7.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l + 96 * (q + 1)) := by
      simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hinv.rx18,
        signExtend12_nonneg 96 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have hmem_cap := setByte_cap_mem_pres (s := s3) (dst := 512 + capMarkOff (l + 1) + q)
      (b := (s3.getReg .x7).truncate 8) (by omega) (by omega)
    have hmem7_eq : ∀ a : Word, s7.getMem a = (s3.setByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q)) ((s3.getReg .x7).truncate 8)).getMem a := fun a => by
      simp [s7, s6, s5, s4, hsb_addr]
    have hro7 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7 := fun a ha => by
      rw [hmem7_eq, hmem_cap.2 a (by omega)]; exact (by simp [s3, s2, s1] : s3.getMem a = s.getMem a).trans (hinv.hro a ha)
    have hbt7 : BaseTableReady s7 := baseTableReady_of_lowEq hinv.hbt (fun a ha => by
      rw [hmem7_eq, hmem_cap.1 a ha]; simp [s3, s2, s1])
    have hsrcM7 : CapLevelMarks s7 positions l := fun idx hidx => by
      simp only [s7, s6, s5, s4, getByte_setPC, getByte_setReg, hsb_addr]
      rw [setByte_cap_getByte_ne (by omega) (by omega) (by omega)]
      simp only [s3, s2, s1, getByte_setPC, getByte_setReg]; exact hinv.hsrcM idx hidx
    have hdstM7 : ∀ p < q + 1, s7.getByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + p)) =
        if capMark positions (l + 1) p then 1#8 else 0#8 := fun p hp => by
      simp only [s7, s6, s5, s4, getByte_setPC, getByte_setReg, hsb_addr]
      by_cases hpq : p = q
      · subst hpq; rw [set_byte_read]; simp only [↓reduceIte, hm_next, ← hsame, Bool.or_self]
        simp only [s3, MachineState.getReg_setPC, hs2_7]; cases mL <;> decide
      · rw [setByte_cap_getByte_ne (by omega) (by omega) (by omega)]
        simp only [s3, s2, s1, getByte_setPC, getByte_setReg]; exact hinv.hdstM p (by omega)
    have hw7 : WriterState (CleanTrapdoor trapdoor) s7 r false base 0 written := by
      have hbyte_p : ∀ a : Word, 11341403200 ≤ a.toNat → s7.getMem a = s.getMem a := fun a ha => by
        rw [hmem7_eq, hmem_cap.2 a (by omega)]; simp [s3, s2, s1]
      refine ⟨hinv.hw.hbase8, hinv.hw.hdst8, hinv.hw.hlen, hinv.hw.hbound,
        by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.hw.rx25],
        hinv.hw.hflushed_ok, fun hcl j hj => ?_, fun hcl => ?_⟩
      · have hlen := hinv.hw.hlen; have hbd := hinv.hw.hbound
        have hal := alignToDword_ofNat_eq (8 * ((11341403200 + j) / 8)) ((11341403200 + j) % 8) (by omega) (by omega)
        rw [show 8 * ((11341403200 + j) / 8) + (11341403200 + j) % 8 = 11341403200 + j by omega] at hal
        have hm := hbyte_p (alignToDword (BitVec.ofNat 64 (11341403200 + j))) (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
        exact (by simp only [MachineState.getByte, hm] : s7.getByte _ = s.getByte _).trans (hinv.hw.hbytes hcl j hj)
      · have h12 : s7.getReg .x12 = s.getReg .x12 := by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne']
        have hrem := hinv.hw.hrem hcl; simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
        by_cases hr0 : r.val = 0
        · simp [hr0]
        · simp only [hr0, ↓reduceIte] at hrem ⊢
          exact ⟨fun j hj => by rw [h12]; exact hrem.1 j hj, fun j h1 h2 => by rw [h12]; exact hrem.2 j h1 h2⟩
    have ht7 : TailState (CleanTrapdoor trapdoor) s7 tails flushes := by
      refine ⟨hinv.ht.hbits, hinv.ht.hbound,
        (by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne'] : s7.getReg .x15 = s.getReg .x15).trans hinv.ht.rx15,
        (by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne'] : s7.getReg .x17 = s.getReg .x17).trans hinv.ht.rx17,
        fun hcl => ?_⟩
      obtain ⟨tBuf, hlt, hx16, hsum⟩ := hinv.ht.hdata hcl
      refine ⟨tBuf, hlt, (by simp [s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne'] : s7.getReg .x16 = s.getReg .x16).trans hx16, ?_⟩
      have hmap : ((List.range (8 * flushes)).map fun j => s7.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
          ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) := by
        apply List.map_congr_left; intro j hj; have hj' := List.mem_range.mp hj
        have hbd := hinv.ht.hbound
        have hal := alignToDword_ofNat_eq (8 * ((tailBufBase + j) / 8)) ((tailBufBase + j) % 8) (by omega) (by unfold tailBufBase; omega)
        rw [show 8 * ((tailBufBase + j) / 8) + (tailBufBase + j) % 8 = tailBufBase + j by omega] at hal
        simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
        rw [hmem7_eq, hmem_cap.2 _ (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; unfold tailBufBase; omega)]
        simp [s3, s2, s1]
      rw [hmap]; exact hsum
    have hrun7 := ((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6)
    by_cases hlast : q + 1 = levelSize l / 2
    · have h7 := step_BNE_not_taken (s := s7) (by omega) hs7_pc hbne_ins (by rw [hs7_22, hs7_23, hlast])
      set s8 := s7.setPC (pcAt (pcSame + 4 + 1))
      have hi_14 : openInstr (pcSame + 5) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r.val))) := by
        have h := hcTail'.2 11 (by simp); rw [show pcTnf + 11 = pcSame + 5 by omega] at h; exact h
      have hi_jal : openInstr (pcSame + 6) = .base (.JAL .x0 (jalOff (pcSame + 6) PC_cap_lvl_end)) := by
        have h := hcTail'.2 12 (by simp); rw [show pcTnf + 12 = pcSame + 6 by omega] at h; exact h
      have h8 := step_ADDI (s := s8) (by omega) rfl hi_14
      set s9 := (s8.setReg .x14 (s8.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * r.val)))).setPC (pcAt (pcSame + 5 + 1))
      have h9 := step_JAL (s := s9) (by omega) rfl hi_jal
        (pcAt_add_jalOff (pcSame + 6) PC_cap_lvl_end (by omega) (by decide))
      set s10 := (s9.setReg .x0 (pcAt (pcSame + 6 + 1))).setPC (pcAt PC_cap_lvl_end)
      have hmem10 : ∀ a, s10.getMem a = s7.getMem a := fun _ => by simp [s10, s9, s8, setReg_x0_eq]
      refine ⟨s10, by simp only [hsame, ↓reduceIte, hlast, Nat.mul_zero, Nat.add_zero]; exact ((hrun7.trans h7).trans h8).trans h9, ?_⟩
      simp only [hlast, ↓reduceDIte, hsame, ↓reduceIte, Nat.add_zero, List.append_nil]
      refine ⟨rfl,
        by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setByte, getReg_setReg_ne', hinv.rx4],
        by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setByte, getReg_setReg_ne', hinv.rx11],
        by have := r.isLt; simp [s10, s9, setReg_x0_eq, show s8.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * r.val) (by omega)],
        by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setByte, getReg_setReg_ne', hinv.rx19],
        by rw [show s10.getReg .x20 = s7.getReg .x20 by simp [s10, s9, s8, setReg_x0_eq, getReg_setReg_ne'], hs7_20, hlast],
        by rw [show s10.getReg .x22 = s7.getReg .x22 by simp [s10, s9, s8, setReg_x0_eq, getReg_setReg_ne'], hs7_22, hlast],
        by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setByte, getReg_setReg_ne', hinv.rx26],
        by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setByte, getReg_setReg_ne', hinv.rx29],
        by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setReg_x0_eq, getReg_setByte, getReg_setReg_ne', hinv.rx30],
        fun a ha => (hmem10 a).trans (hro7 a ha),
        baseTableReady_of_lowEq hbt7 (fun a _ => hmem10 a),
        fun idx hidx => by simp only [MachineState.getByte, hmem10]; exact hsrcM7 idx hidx,
        fun p hp => by simp only [MachineState.getByte, hmem10]; exact hdstM7 p (by omega),
        writerState_of_mem_eq hw7 hmem10 (by simp [s10, s9, s8, setReg_x0_eq, getReg_setReg_ne']) (by simp [s10, s9, s8, setReg_x0_eq, getReg_setReg_ne']),
        TailState.of_proofWrite ht7 (fun a _ => hmem10 a) (by simp [s10, s9, s8, setReg_x0_eq, getReg_setReg_ne'])
          (by simp [s10, s9, s8, setReg_x0_eq, getReg_setReg_ne']) (by simp [s10, s9, s8, setReg_x0_eq, getReg_setReg_ne'])⟩
    · have hne22 : s7.getReg .x22 ≠ s7.getReg .x23 := by
        rw [hs7_22, hs7_23]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 512 + capMarkOff (l + 1) + (q + 1) < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 512 + capMarkOff (l + 1) + levelSize l / 2 < 2 ^ 64)] at hn; omega
      have hbr_back := pcAt_add_brOff13 (pcSame + 4) pc0 (by omega) (fun _ => hlay.2.2.2.2.2.2)
      have h7 := step_BNE_taken (s := s7) (by omega) hs7_pc hbne_ins hne22 hbr_back
      set s8 := s7.setPC (pcAt pc0)
      refine ⟨s8, by simp only [hsame, ↓reduceIte, hlast, Nat.mul_zero, Nat.add_zero]; exact hrun7.trans h7, ?_⟩
      simp only [hlast, ↓reduceDIte, hsame, ↓reduceIte, Nat.add_zero, List.append_nil]
      refine ⟨rfl,
        by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx4],
        by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx11],
        by simp [s8, hs7_18],
        by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx19],
        by simp [s8, hs7_20], by simp [s8, hs7_22], by simp [s8, hs7_23],
        by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx26],
        by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx29],
        by simp [s8, s7, s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx30],
        fun a ha => (by simp [s8] : s8.getMem a = s7.getMem a).trans (hro7 a ha),
        baseTableReady_of_lowEq hbt7 (fun _ _ => by simp [s8]),
        fun idx hidx => by simp only [s8, getByte_setPC]; exact hsrcM7 idx hidx,
        fun p hp => by simp only [s8, getByte_setPC]; exact hdstM7 p hp,
        writerState_of_mem_eq hw7 (fun _ => by simp [s8]) (by simp [s8]) (by simp [s8]),
        TailState.of_proofWrite ht7 (fun _ _ => by simp [s8]) (by simp [s8]) (by simp [s8]) (by simp [s8])⟩
  · -- Frontier pair (`mL ≠ mR`): emit sibling node `sibIdx = if !mL then 2*q else 2*q+1`!
    have hne78 : s2.getReg .x7 ≠ s2.getReg .x8 := by
      rw [hs2_7, hs2_8]; cases hmL : mL <;> cases hmR : mR <;> simp [hmL, hmR] at hsame ⊢
    have h2 := step_BEQ_not_taken (s := s2) (by omega) hs2_pc hi2 hne78
    set s3 := s2.setPC (pcAt (pc0 + 2 + 1))
    have hi3 : openInstr (pc0 + 3) = .base (.SB .x22 .x4 (0#12)) := by have h := hcPre.2 3 (by simp); simpa using h
    have hi4 : openInstr (pc0 + 4) = .base (.SLLI .x10 .x7 (5#6)) := by have h := hcPre.2 4 (by simp); simpa using h
    have hi5 : openInstr (pc0 + 5) = .base (.ADD .x10 .x18 .x10) := by have h := hcPre.2 5 (by simp); simpa using h
    have hs3_22 : s3.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q) := by
      simp [s3, s2, s1, getReg_setReg_ne', hinv.rx22]
    have hsb_addr : s3.getReg .x22 + signExtend12 (0#12) = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q) := by
      rw [hs3_22, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsb_val : accessValid (s3.getReg .x22 + signExtend12 (0#12)) 1 = true := by
      rw [hsb_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
    have h3 := step_SB (s := s3) (by omega) rfl hi3 hsb_val
    set s4 := (s3.setByte (s3.getReg .x22 + signExtend12 (0#12)) ((s3.getReg .x4).truncate 8)).setPC (pcAt (pc0 + 3 + 1))
    have h4 := step_SLLI (s := s4) (by omega) rfl hi4
    set s5 := (s4.setReg .x10 (s4.getReg .x7 <<< (5#6).toNat)).setPC (pcAt (pc0 + 4 + 1))
    have h5 := step_ADD (s := s5) (by omega) rfl hi5
    set s6 := (s5.setReg .x10 (s5.getReg .x18 + s5.getReg .x10)).setPC (pcAt (pc0 + 5 + 1))
    set sibIdx := if !mL then 2 * q else 2 * q + 1
    have hsib_lt : sibIdx < levelSize l := by unfold sibIdx; split_ifs <;> omega
    have hnodeOff : nodeOffset l sibIdx = 96 * q + (if mL then 32 else 0) := by
      unfold sibIdx nodeOffset gapOffset
      simp only [show l ≠ 0 by omega, ↓reduceIte]
      cases mL <;> simp <;> omega
    have hs6_10 : s6.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase l + nodeOffset l sibIdx) := by
      have hs4_7 : s4.getReg .x7 = if mL then 1#64 else 0#64 := by simp [s4, s3, getReg_setByte, hs2_7]
      have hs5_10 : s5.getReg .x10 = BitVec.ofNat 64 (if mL then 32 else 0) := by
        simp only [s5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs4_7]
        cases mL <;> decide
      have hs5_18 : s5.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) := by
        simp [s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx18]
      simp only [s6, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        hs5_18, hs5_10, ← BitVec.ofNat_add, hnodeOff]
      apply congrArg (BitVec.ofNat 64); omega
    have hmem_cap := setByte_cap_mem_pres (s := s3) (dst := 512 + capMarkOff (l + 1) + q)
      (b := (s3.getReg .x4).truncate 8) (by omega) (by omega)
    have hmem6_eq : ∀ a : Word, s6.getMem a = (s3.setByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q)) ((s3.getReg .x4).truncate 8)).getMem a := fun a => by
      simp [s6, s5, s4, hsb_addr]
    have hro6 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s6 := fun a ha => by
      rw [hmem6_eq, hmem_cap.2 a (by omega)]; exact (by simp [s3, s2, s1] : s3.getMem a = s.getMem a).trans (hinv.hro a ha)
    have hbt6 : BaseTableReady s6 := baseTableReady_of_lowEq hinv.hbt (fun a ha => by
      rw [hmem6_eq, hmem_cap.1 a ha]; simp [s3, s2, s1])
    have hsrcM6 : CapLevelMarks s6 positions l := fun idx hidx => by
      simp only [s6, s5, s4, getByte_setPC, getByte_setReg, hsb_addr]
      rw [setByte_cap_getByte_ne (by omega) (by omega) (by omega)]
      simp only [s3, s2, s1, getByte_setPC, getByte_setReg]; exact hinv.hsrcM idx hidx
    have hdstM6 : ∀ p < q + 1, s6.getByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + p)) =
        if capMark positions (l + 1) p then 1#8 else 0#8 := fun p hp => by
      simp only [s6, s5, s4, getByte_setPC, getByte_setReg, hsb_addr]
      by_cases hpq : p = q
      · subst hpq; rw [set_byte_read]; simp only [↓reduceIte, hm_next]
        have hor : (mL || mR) = true := by cases hmL : mL <;> cases hmR : mR <;> simp [hmL, hmR] at hsame ⊢
        rw [hor]; simp [s3, s2, s1, getReg_setReg_ne', hinv.rx4]
      · rw [setByte_cap_getByte_ne (by omega) (by omega) (by omega)]
        simp only [s3, s2, s1, getByte_setPC, getByte_setReg]; exact hinv.hdstM p (by omega)
    have hw6 : WriterState (CleanTrapdoor trapdoor) s6 r false base 0 written := by
      refine ⟨hinv.hw.hbase8, hinv.hw.hdst8, hinv.hw.hlen, hinv.hw.hbound,
        by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.hw.rx25],
        hinv.hw.hflushed_ok, fun hcl j hj => ?_, fun hcl => ?_⟩
      · have hlen := hinv.hw.hlen; have hbd := hinv.hw.hbound
        have hal := alignToDword_ofNat_eq (8 * ((11341403200 + j) / 8)) ((11341403200 + j) % 8) (by omega) (by omega)
        rw [show 8 * ((11341403200 + j) / 8) + (11341403200 + j) % 8 = 11341403200 + j by omega] at hal
        have hm : s6.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + j))) =
            s.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + j))) := by
          rw [hmem6_eq, hmem_cap.2 _ (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)]; simp [s3, s2, s1]
        exact (by simp only [MachineState.getByte, hm] : s6.getByte _ = s.getByte _).trans (hinv.hw.hbytes hcl j hj)
      · have h12 : s6.getReg .x12 = s.getReg .x12 := by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne']
        have hrem := hinv.hw.hrem hcl; simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
        by_cases hr0 : r.val = 0
        · simp [hr0]
        · simp only [hr0, ↓reduceIte] at hrem ⊢
          exact ⟨fun j hj => by rw [h12]; exact hrem.1 j hj, fun j h1 h2 => by rw [h12]; exact hrem.2 j h1 h2⟩
    have ht6 : TailState (CleanTrapdoor trapdoor) s6 tails flushes := by
      refine ⟨hinv.ht.hbits, hinv.ht.hbound,
        (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne'] : s6.getReg .x15 = s.getReg .x15).trans hinv.ht.rx15,
        (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne'] : s6.getReg .x17 = s.getReg .x17).trans hinv.ht.rx17,
        fun hcl => ?_⟩
      obtain ⟨tBuf, hlt, hx16, hsum⟩ := hinv.ht.hdata hcl
      refine ⟨tBuf, hlt, (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne'] : s6.getReg .x16 = s.getReg .x16).trans hx16, ?_⟩
      have hmap : ((List.range (8 * flushes)).map fun j => s6.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
          ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) := by
        apply List.map_congr_left; intro j hj; have hj' := List.mem_range.mp hj
        have hbd := hinv.ht.hbound
        have hal := alignToDword_ofNat_eq (8 * ((tailBufBase + j) / 8)) ((tailBufBase + j) % 8) (by omega) (by unfold tailBufBase; omega)
        rw [show 8 * ((tailBufBase + j) / 8) + (tailBufBase + j) % 8 = tailBufBase + j by omega] at hal
        simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
        rw [hmem6_eq, hmem_cap.2 _ (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; unfold tailBufBase; omega)]
        simp [s3, s2, s1]
      rw [hmap]; exact hsum
    -- Step 6: copy29Code r .x10 0 .x5 0 false false false
    have hnbd := nodeOffset_lt_treeBytes' l sibIdx (by omega) hsib_lt
    have hsrc_al : (4294971424 + levelBase l + nodeOffset l sibIdx) % 8 = 0 := by
      have h1 := levelBase_align8' l (by omega); have h2 := nodeOffset_align8' l sibIdx; omega
    obtain ⟨s7, hr7, hpc7, hreg7, hp7, hw7, hpost7⟩ := openRuns_copy29 (clean := CleanTrapdoor trapdoor)
      (d := tdNode trapdoor l sibIdx) (prevVal := 0) hcC29 (by dsimp only [s6, MachineState.setPC]; congr 1)
      (by decide) (by decide) (fun _ h => absurd rfl h) (by omega)
      (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx11])
      hs6_10 hsrc_al (by omega)
      (fun _ k hk => by simpa only [Nat.add_assoc] using readOnly_getMem_tdNode hro6 l sibIdx k (by omega) hsib_lt hk)
      (fun hcl => hcl.2 l (by omega) hl2 sibIdx hsib_lt)
      (by omega) (by omega) hw6 (fun _ => by simp)
    -- Step 7: ADDI x25 x25 doff
    have hi_add25 : openInstr (pc0 + 6 + (copy29Code r .x10 0 .x5 0 false false false).length) =
        .base (.ADDI .x25 .x25 (BitVec.ofNat 12 doff)) := by
      have h := hcAdd25.2 0 (by simp); simpa using h
    have hadd25_lt : doff < 2048 := by unfold doff copy29NextDstOff; split_ifs <;> omega
    have h7 := step_ADDI (s := s7) (by omega) (by simpa only [List.length_cons, List.length_nil] using hpc7) hi_add25
    set s8 := (s7.setReg .x25 (s7.getReg .x25 + signExtend12 (BitVec.ofNat 12 doff))).setPC
      (pcAt (pc0 + 6 + (copy29Code r .x10 0 .x5 0 false false false).length + 1))
    have hw8 : WriterState (CleanTrapdoor trapdoor) s8 rNext false (base + doff) 0
        (written ++ bitsToBytes (tdNode trapdoor l sibIdx) 29) := by
      have hw7' : WriterState (CleanTrapdoor trapdoor) s7 rNext false base doff
          (written ++ bitsToBytes (tdNode trapdoor l sibIdx) 29) := by
        simpa only [copy29NextFlushedR4, Bool.and_false] using hw7
      exact writerState_advance_base hw7' hadd25_lt (pcAt (pc0 + 6 + (copy29Code r .x10 0 .x5 0 false false false).length + 1))
    have ht8 : TailState (CleanTrapdoor trapdoor) s8 tails flushes :=
      TailState.of_proofWrite ht6 (ProofWritePreserves.trans hp7 (fun _ _ => by simp [s8]))
        ((by simp [s8, getReg_setReg_ne'] : s8.getReg .x15 = s7.getReg .x15).trans (hreg7 .x15 (by decide)))
        ((by simp [s8, getReg_setReg_ne'] : s8.getReg .x16 = s7.getReg .x16).trans (hreg7 .x16 (by decide)))
        ((by simp [s8, getReg_setReg_ne'] : s8.getReg .x17 = s7.getReg .x17).trans (hreg7 .x17 (by decide)))
    have hs8_5 : CleanTrapdoor trapdoor → s8.getReg .x5 = BitVec.ofNat 64 (tail6 (tdNode trapdoor l sibIdx)).toNat := fun hcl => by
      have hp := hpost7 hcl; simp only [Bool.false_eq_true, ↓reduceIte] at hp
      exact (by simp [s8, getReg_setReg_ne'] : s8.getReg .x5 = s7.getReg .x5).trans hp
    -- Step 8: tailPush6Code
    have hcTP6' : CodeAt (pc0 + 6 + (copy29Code r .x10 0 .x5 0 false false false).length + 1) tailPush6Code := by
      have hpc_tp : pc0 + ([.base (.LBU .x7 .x20 (0#12)), .base (.LBU .x8 .x20 (1#12)),
          .base (.BEQ .x7 .x8 (BitVec.ofNat 13 (4 * (pcSame - (pc0 + 2))))),
          .base (.SB .x22 .x4 (0#12)), .base (.SLLI .x10 .x7 (5#6)), .base (.ADD .x10 .x18 .x10)] : List Instruction).length +
          (copy29Code r .x10 0 .x5 0 false false false).length +
          ([.base (.ADDI .x25 .x25 (BitVec.ofNat 12 doff))] : List Instruction).length =
          pc0 + 6 + (copy29Code r .x10 0 .x5 0 false false false).length + 1 := by
        simp only [List.length_cons, List.length_nil]
      rw [hpc_tp] at hcTP6; exact hcTP6
    obtain ⟨s9, hr9, hpc9, hreg9, htw9, ht9⟩ := openRuns_tailPush6_neg (t6 := tail6 (tdNode trapdoor l sibIdx))
      hcTP6' rfl hs8_5 ht8 hbd_t
    have hpc9_eq : s9.pc = pcAt pcTnf := by rw [hpc9, show (10 : Nat) = tailPush6Code.length from rfl, hpc_tnf_eq]
    have hw9 : WriterState (CleanTrapdoor trapdoor) s9 rNext false (base + doff) 0
        (written ++ bitsToBytes (tdNode trapdoor l sibIdx) 29) :=
      writerState_of_tailWrite hw8 htw9 (hreg9 .x25 (by decide)) (hreg9 .x12 (by decide))
    -- Step 9..11: ADDI x20 2; ADDI x22 1; ADDI x18 96
    have ha20_ins : openInstr pcTnf = .base (.ADDI .x20 .x20 (2#12)) := by have h := hcTail'.2 0 (by simp); simpa using h
    have ha22_ins : openInstr (pcTnf + 1) = .base (.ADDI .x22 .x22 (1#12)) := by have h := hcTail'.2 1 (by simp); simpa using h
    have ha18_ins : openInstr (pcTnf + 2) = .base (.ADDI .x18 .x18 (96#12)) := by have h := hcTail'.2 2 (by simp); simpa using h
    have hbne_ins : openInstr (pcTnf + 3) = .base (.BNE .x22 .x23 (brOff13 (pcTnf + 3) (pcCapPair rNext))) := by
      have h := hcTail'.2 3 (by simp); simpa using h
    have h9a := step_ADDI (s := s9) (by omega) hpc9_eq ha20_ins
    set s10 := (s9.setReg .x20 (s9.getReg .x20 + signExtend12 (2#12))).setPC (pcAt (pcTnf + 1))
    have h9b := step_ADDI (s := s10) (by omega) rfl ha22_ins
    set s11 := (s10.setReg .x22 (s10.getReg .x22 + signExtend12 (1#12))).setPC (pcAt (pcTnf + 1 + 1))
    have h9c := step_ADDI (s := s11) (by omega) rfl ha18_ins
    set s12 := (s11.setReg .x18 (s11.getReg .x18 + signExtend12 (96#12))).setPC (pcAt (pcTnf + 2 + 1))
    have hs12_pc : s12.pc = pcAt (pcTnf + 3) := rfl
    have hreg9_6 : ∀ reg, reg ∉ [.x5, .x6, .x7, .x10, .x12, .x15, .x16, .x17, .x25] → s9.getReg reg = s6.getReg reg := by
      intro reg h
      have h5' : reg ≠ .x5 := fun hm => h (by simp [hm])
      have h6' : reg ≠ .x6 := fun hm => h (by simp [hm])
      have h7' : reg ≠ .x7 := fun hm => h (by simp [hm])
      have h10' : reg ≠ .x10 := fun hm => h (by simp [hm])
      have h12' : reg ≠ .x12 := fun hm => h (by simp [hm])
      have h15' : reg ≠ .x15 := fun hm => h (by simp [hm])
      have h16' : reg ≠ .x16 := fun hm => h (by simp [hm])
      have h17' : reg ≠ .x17 := fun hm => h (by simp [hm])
      have h25' : reg ≠ .x25 := fun hm => h (by simp [hm])
      exact (hreg9 reg (by simp [h6', h7', h15', h16', h17'])).trans
        ((by simp [s8, getReg_setReg_ne' .x25 reg h25'.symm] : s8.getReg reg = s7.getReg reg).trans
         (hreg7 reg (by simp [h5', h6', h10', h12'])))
    have hs12_20 : s12.getReg .x20 = BitVec.ofNat 64 (512 + capMarkOff l + 2 * (q + 1)) := by
      have h9_20 : s9.getReg .x20 = BitVec.ofNat 64 (512 + capMarkOff l + 2 * q) :=
        (hreg9_6 .x20 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx20])
      simp only [s12, s11, s10, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq,
        ne_eq, reduceCtorEq, not_false_eq_true, h9_20, signExtend12_nonneg 2 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have hs12_22 : s12.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + (q + 1)) := by
      have h9_22 : s9.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + q) :=
        (hreg9_6 .x22 (by decide)).trans (by simp [s6, s5, s4, getReg_setByte, getReg_setReg_ne', hs3_22])
      simp only [s12, s11, s10, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq,
        ne_eq, reduceCtorEq, not_false_eq_true, h9_22, signExtend12_nonneg 1 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have hs12_18 : s12.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l + 96 * (q + 1)) := by
      have h9_18 : s9.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) :=
        (hreg9_6 .x18 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx18])
      simp only [s12, s11, s10, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq,
        ne_eq, reduceCtorEq, not_false_eq_true, h9_18, signExtend12_nonneg 96 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
    have hs12_23 : s12.getReg .x23 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2) := by
      have h9_23 : s9.getReg .x23 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2) :=
        (hreg9_6 .x23 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx23])
      simp [s12, s11, s10, getReg_setReg_ne', h9_23]
    have h9_4 : s9.getReg .x4 = 1#64 :=
      (hreg9_6 .x4 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx4])
    have h9_11 : s9.getReg .x11 = mask40Word :=
      (hreg9_6 .x11 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx11])
    have h9_19 : s9.getReg .x19 = BitVec.ofNat 64 (levelSize l) :=
      (hreg9_6 .x19 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx19])
    have h9_26 : s9.getReg .x26 = BitVec.ofNat 64 (68719475936 + 32 * l + 8) :=
      (hreg9_6 .x26 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx26])
    have h9_29 : s9.getReg .x29 = BitVec.ofNat 64 (8 * l) :=
      (hreg9_6 .x29 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx29])
    have h9_30 : s9.getReg .x30 = BitVec.ofNat 64 (8 * 24) :=
      (hreg9_6 .x30 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hinv.rx30])
    have hlow9 : ∀ a : Word, a.toNat < 1344 → s9.getMem a = s6.getMem a := fun a ha => by
      exact (htw9 a (by unfold tailBufBase; omega)).trans
        ((by simp [s8] : s8.getMem a = s7.getMem a).trans (hp7 a (by omega)))
    have hro12 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s12 := fun a ha => by
      have h12_9 : s12.getMem a = s9.getMem a := by simp [s12, s11, s10]
      exact h12_9.trans ((readOnlyPreserved_of_tailWrite (ReadOnlyPreserved.of_proofWrite hro6 (ProofWritePreserves.trans hp7 (fun _ _ => by simp [s8]))) htw9) a ha)
    have hbt12 : BaseTableReady s12 := baseTableReady_of_lowEq hbt6 (fun a ha => by
      exact (by simp [s12, s11, s10] : s12.getMem a = s9.getMem a).trans (hlow9 a (by omega)))
    have hsrcM12 : CapLevelMarks s12 positions l := capLevelMarks_of_lowEq hl1 (by omega) hsrcM6 (fun a _ h2 =>
      (by simp [s12, s11, s10] : s12.getMem a = s9.getMem a).trans (hlow9 a h2))
    have hdstM12 : ∀ p < q + 1, s12.getByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + p)) =
        if capMark positions (l + 1) p then 1#8 else 0#8 := fun p hp => by
      have hal := alignToDword_ofNat_eq (8 * ((512 + capMarkOff (l + 1) + p) / 8)) ((512 + capMarkOff (l + 1) + p) % 8) (by omega) (by omega)
      rw [show 8 * ((512 + capMarkOff (l + 1) + p) / 8) + (512 + capMarkOff (l + 1) + p) % 8 = 512 + capMarkOff (l + 1) + p by omega] at hal
      have hm : s12.getMem (alignToDword (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + p))) =
          s6.getMem (alignToDword (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + p))) :=
        (by simp [s12, s11, s10] : s12.getMem _ = s9.getMem _).trans
          (hlow9 _ (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))
      exact (by simp only [MachineState.getByte, hm] : s12.getByte _ = s6.getByte _).trans (hdstM6 p hp)
    have hw12 : WriterState (CleanTrapdoor trapdoor) s12 rNext false (base + doff) 0
        (written ++ bitsToBytes (tdNode trapdoor l sibIdx) 29) :=
      writerState_of_mem_eq hw9 (fun _ => by simp [s12, s11, s10]) (by simp [s12, s11, s10, getReg_setReg_ne'])
        (by simp [s12, s11, s10, getReg_setReg_ne'])
    have ht12 : TailState (CleanTrapdoor trapdoor) s12 (tails ++ [tail6 (tdNode trapdoor l sibIdx)])
        (flushes + if (6 * tails.length) % 64 + 6 < 64 then 0 else 1) :=
      TailState.of_proofWrite ht9 (fun _ _ => by simp [s12, s11, s10])
        (by simp [s12, s11, s10, getReg_setReg_ne']) (by simp [s12, s11, s10, getReg_setReg_ne'])
        (by simp [s12, s11, s10, getReg_setReg_ne'])
    have hrun12 := (((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans hr7).trans h7).trans hr9).trans h9a).trans h9b |>.trans h9c
    have haddFwd_eq : bitsToBytes (tdNode trapdoor l sibIdx) 29 =
        if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29 else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29 := by
      unfold sibIdx; split_ifs <;> rfl
    have haddTails_eq : [tail6 (tdNode trapdoor l sibIdx)] =
        if !mL then [tail6 (tdNode trapdoor l (2 * q))] else [tail6 (tdNode trapdoor l (2 * q + 1))] := by
      unfold sibIdx; split_ifs <;> rfl
    by_cases hlast : q + 1 = levelSize l / 2
    · have h12 := step_BNE_not_taken (s := s12) (by omega) hs12_pc hbne_ins (by rw [hs12_22, hs12_23, hlast])
      set s13 := s12.setPC (pcAt (pcTnf + 3 + 1))
      have hi_14 : openInstr (pcTnf + 4) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rNext.val))) := by
        have h := hcTail'.2 4 (by simp); simpa using h
      have hi_jal : openInstr (pcTnf + 5) = .base (.JAL .x0 (jalOff (pcTnf + 5) PC_cap_lvl_end)) := by
        have h := hcTail'.2 5 (by simp); simpa using h
      have h13 := step_ADDI (s := s13) (by omega) rfl hi_14
      set s14 := (s13.setReg .x14 (s13.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * rNext.val)))).setPC (pcAt (pcTnf + 4 + 1))
      have h14 := step_JAL (s := s14) (by omega) rfl hi_jal
        (pcAt_add_jalOff (pcTnf + 5) PC_cap_lvl_end (by omega) (by decide))
      set s15 := (s14.setReg .x0 (pcAt (pcTnf + 5 + 1))).setPC (pcAt PC_cap_lvl_end)
      have hmem15 : ∀ a, s15.getMem a = s12.getMem a := fun _ => by simp [s15, s14, s13, setReg_x0_eq]
      refine ⟨s15, ?_, ?_⟩
      · have htot := ((hrun12.trans h12).trans h13).trans h14
        have heq_c : 1 + 1 + 1 + 1 + 1 + 1 + (copy29Code r .x10 0 .x5 0 false false false).length + 1 +
            (4 + 6 * if 6 * tails.length % 64 + 6 < 64 then 0 else 1) + 1 + 1 + 1 + 1 + 1 + 1 =
            (if mL = mR then 8 else capPairNf r) + (if q + 1 = levelSize l / 2 then 2 else 0) +
            6 * (if mL = mR then 0 else if 6 * tails.length % 64 + 6 < 64 then 0 else 1) := by
          simp only [hsame, hlast, ↓reduceIte, capPairNf]; omega
        simpa only [heq_c] using htot
      · simp only [hlast, ↓reduceDIte, hsame, ↓reduceIte, ← haddFwd_eq, ← haddTails_eq]
        refine ⟨rfl,
          by simp [s15, s14, s13, s12, s11, s10, setReg_x0_eq, getReg_setReg_ne', h9_4],
          by simp [s15, s14, s13, s12, s11, s10, setReg_x0_eq, getReg_setReg_ne', h9_11],
          by have := rNext.isLt; simp [s15, s14, setReg_x0_eq, show s13.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * rNext.val) (by omega)],
          by simp [s15, s14, s13, s12, s11, s10, setReg_x0_eq, getReg_setReg_ne', h9_19],
          by rw [show s15.getReg .x20 = s12.getReg .x20 by simp [s15, s14, s13, setReg_x0_eq, getReg_setReg_ne'], hs12_20, hlast],
          by rw [show s15.getReg .x22 = s12.getReg .x22 by simp [s15, s14, s13, setReg_x0_eq, getReg_setReg_ne'], hs12_22, hlast],
          by simp [s15, s14, s13, s12, s11, s10, setReg_x0_eq, getReg_setReg_ne', h9_26],
          by simp [s15, s14, s13, s12, s11, s10, setReg_x0_eq, getReg_setReg_ne', h9_29],
          by simp [s15, s14, s13, s12, s11, s10, setReg_x0_eq, getReg_setReg_ne', h9_30],
          fun a ha => (hmem15 a).trans (hro12 a ha),
          baseTableReady_of_lowEq hbt12 (fun a _ => hmem15 a),
          fun idx hidx => by simp only [MachineState.getByte, hmem15]; exact hsrcM12 idx hidx,
          fun p hp => by simp only [MachineState.getByte, hmem15]; exact hdstM12 p (by omega),
          writerState_of_mem_eq hw12 hmem15 (by simp [s15, s14, s13, setReg_x0_eq, getReg_setReg_ne']) (by simp [s15, s14, s13, setReg_x0_eq, getReg_setReg_ne']),
          TailState.of_proofWrite ht12 (fun a _ => hmem15 a) (by simp [s15, s14, s13, setReg_x0_eq, getReg_setReg_ne'])
            (by simp [s15, s14, s13, setReg_x0_eq, getReg_setReg_ne']) (by simp [s15, s14, s13, setReg_x0_eq, getReg_setReg_ne'])⟩
    · have hne22 : s12.getReg .x22 ≠ s12.getReg .x23 := by
        rw [hs12_22, hs12_23]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 512 + capMarkOff (l + 1) + (q + 1) < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 512 + capMarkOff (l + 1) + levelSize l / 2 < 2 ^ 64)] at hn; omega
      have hbr_nxt := pcAt_add_brOff13 (pcTnf + 3) (pcCapPair rNext) hlay.2.2.2.2.1 hlay.2.2.2.2.2.1
      have h12 := step_BNE_taken (s := s12) (by omega) hs12_pc hbne_ins hne22 hbr_nxt
      set s13 := s12.setPC (pcAt (pcCapPair rNext))
      refine ⟨s13, ?_, ?_⟩
      · have htot := hrun12.trans h12
        have heq_c : 1 + 1 + 1 + 1 + 1 + 1 + (copy29Code r .x10 0 .x5 0 false false false).length + 1 +
            (4 + 6 * if 6 * tails.length % 64 + 6 < 64 then 0 else 1) + 1 + 1 + 1 + 1 =
            (if mL = mR then 8 else capPairNf r) + (if q + 1 = levelSize l / 2 then 2 else 0) +
            6 * (if mL = mR then 0 else if 6 * tails.length % 64 + 6 < 64 then 0 else 1) := by
          simp only [hsame, hlast, ↓reduceIte, capPairNf]; omega
        simpa only [heq_c] using htot
      · simp only [hlast, ↓reduceDIte, hsame, ↓reduceIte, ← haddFwd_eq, ← haddTails_eq]
        refine ⟨rfl,
          by simp [s13, s12, s11, s10, getReg_setReg_ne', h9_4],
          by simp [s13, s12, s11, s10, getReg_setReg_ne', h9_11],
          by simp [s13, hs12_18],
          by simp [s13, s12, s11, s10, getReg_setReg_ne', h9_19],
          by simp [s13, hs12_20], by simp [s13, hs12_22], by simp [s13, hs12_23],
          by simp [s13, s12, s11, s10, getReg_setReg_ne', h9_26],
          by simp [s13, s12, s11, s10, getReg_setReg_ne', h9_29],
          by simp [s13, s12, s11, s10, getReg_setReg_ne', h9_30],
          fun a ha => (by simp [s13] : s13.getMem a = s12.getMem a).trans (hro12 a ha),
          baseTableReady_of_lowEq hbt12 (fun _ _ => by simp [s13]),
          fun idx hidx => by simp only [s13, getByte_setPC]; exact hsrcM12 idx hidx,
          fun p hp => by simp only [s13, getByte_setPC]; exact hdstM12 p hp,
          writerState_of_mem_eq hw12 (fun _ => by simp [s13]) (by simp [s13]) (by simp [s13]),
          TailState.of_proofWrite ht12 (fun _ _ => by simp [s13]) (by simp [s13]) (by simp [s13]) (by simp [s13])⟩

/-- Induction over remaining pairs `q .. levelSize l / 2 - 1` of level `l ∈ 15..23`. -/
private theorem openRuns_cap_pairs {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {l : Nat} (hl1 : 15 ≤ l) (hl2 : l ≤ 23) :
    ∀ rem (_hrem : 1 ≤ rem) (q base flushes : Nat) (r : Fin 8)
      (written : List Byte) (tails : List (BitVec 6)) (s : MachineState),
      q + rem = levelSize l / 2 →
      base + 32 * rem + 40 ≤ 8556390424 →
      8 * (flushes + rem) + 16 ≤ 48719475936 →
      CapPairInv trapdoor positions l q r base flushes written tails s →
      let qs := (List.range (levelSize l / 2)).drop q
      let addFwd := qs.flatMap fun p =>
        let mL := capMark positions l (2 * p); let mR := capMark positions l (2 * p + 1)
        if mL = mR then [] else if !mL then bitsToBytes (tdNode trapdoor l (2 * p)) 29 else bitsToBytes (tdNode trapdoor l (2 * p + 1)) 29
      let addTails := qs.flatMap fun p =>
        let mL := capMark positions l (2 * p); let mR := capMark positions l (2 * p + 1)
        if mL = mR then [] else if !mL then [tail6 (tdNode trapdoor l (2 * p))] else [tail6 (tdNode trapdoor l (2 * p + 1))]
      ∃ cycNf flNew rEnd baseEnd s',
        OpenRuns s (cycNf + 6 * flNew) (cycNf + 6 * flNew) s' ∧
        8 * cycNf + cphi8 rEnd = 8 * (2 + 8 * rem) + 208 * addTails.length + cphi8 r ∧
        baseEnd ≤ base + 32 * addTails.length ∧
        flNew ≤ addTails.length ∧
        CapLvlEndInv trapdoor positions l rEnd baseEnd (flushes + flNew) (written ++ addFwd) (tails ++ addTails) s' := by
  intro rem
  induction rem with
  | zero => intro h; omega
  | succ rem ih =>
    intro _ q base flushes r written tails s hsum hbd_w hbd_t hinv
    have hq : q < levelSize l / 2 := by omega
    have hdrop : (List.range (levelSize l / 2)).drop q = q :: (List.range (levelSize l / 2)).drop (q + 1) := by
      have := List.drop_eq_getElem_cons (l := List.range (levelSize l / 2)) (i := q) (by simp [hq])
      simpa only [List.getElem_range] using this
    obtain ⟨s1, hr1, hpost1⟩ := openRuns_cap_pair_step hl1 hl2 hq (by omega) (by omega) hinv
    set mL := capMark positions l (2 * q)
    set mR := capMark positions l (2 * q + 1)
    set f1 := if mL = mR then [] else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29 else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29
    set t1 := if mL = mR then [] else if !mL then [tail6 (tdNode trapdoor l (2 * q))] else [tail6 (tdNode trapdoor l (2 * q + 1))]
    set fl1 := if mL = mR then 0 else if (6 * tails.length) % 64 + 6 < 64 then 0 else 1
    set r1 := if mL = mR then r else copy29NextR r
    set base1 := if mL = mR then base else base + copy29NextDstOff r 0
    have ht1_len : t1.length = if mL = mR then 0 else 1 := by unfold t1; split_ifs <;> rfl
    have hfl1_le : fl1 ≤ t1.length := by rw [ht1_len]; unfold fl1; split_ifs <;> omega
    have hb1_le : base1 ≤ base + 32 * t1.length := by
      rw [ht1_len]; unfold base1 copy29NextDstOff; split_ifs <;> omega
    have ham1 : 8 * (if mL = mR then 8 else capPairNf r) + cphi8 r1 = 64 + 208 * t1.length + cphi8 r := by
      rw [ht1_len]; unfold r1; by_cases hs : mL = mR
      · simp [hs]
      · simp only [hs, ↓reduceIte, Nat.mul_one]; have := cap_amort r; omega
    cases rem with
    | zero =>
      have hlast : q + 1 = levelSize l / 2 := by omega
      simp only [hlast, ↓reduceDIte] at hpost1
      have hdrop0 : (List.range (levelSize l / 2)).drop (q + 1) = [] := by
        rw [List.drop_eq_nil_iff]; simp; omega
      have hqs : (List.range (levelSize l / 2)).drop q = [q] := by rw [hdrop, hdrop0]
      refine ⟨(if mL = mR then 8 else capPairNf r) + 2, fl1, r1, base1, s1,
        by simpa only [hlast, ↓reduceIte] using hr1, ?_, ?_, ?_, ?_⟩
      · simp only [hqs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        change _ = 8 * (2 + 8 * 1) + 208 * t1.length + cphi8 r; omega
      · simp only [hqs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; exact hb1_le
      · simp only [hqs, List.flatMap_cons, List.flatMap_nil, List.append_nil]; exact hfl1_le
      · simpa only [hqs, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hpost1
    | succ rem' =>
      have hnlast : q + 1 ≠ levelSize l / 2 := by omega
      simp only [hnlast, ↓reduceDIte] at hpost1
      have ht1_le : t1.length ≤ 1 := by rw [ht1_len]; split_ifs <;> omega
      obtain ⟨cyc2, fl2, rEnd, baseEnd, sEnd, hr2, ham2, hb2_le, hfl2_le, hend⟩ :=
        ih (by omega) (q + 1) base1 (flushes + fl1) r1 (written ++ f1) (tails ++ t1) s1
          (by omega) (by omega) (by omega) hpost1
      set restT := ((List.range (levelSize l / 2)).drop (q + 1)).flatMap fun p =>
        let mL := capMark positions l (2 * p); let mR := capMark positions l (2 * p + 1)
        if mL = mR then [] else if !mL then [tail6 (tdNode trapdoor l (2 * p))] else [tail6 (tdNode trapdoor l (2 * p + 1))]
      change 8 * cyc2 + cphi8 rEnd = 8 * (2 + 8 * (rem' + 1)) + 208 * restT.length + cphi8 r1 at ham2
      change baseEnd ≤ base1 + 32 * restT.length at hb2_le
      change fl2 ≤ restT.length at hfl2_le
      have hr1' : OpenRuns s ((if mL = mR then 8 else capPairNf r) + 6 * fl1)
          ((if mL = mR then 8 else capPairNf r) + 6 * fl1) s1 := by
        simpa only [hnlast, ↓reduceIte, Nat.add_zero] using hr1
      refine ⟨(if mL = mR then 8 else capPairNf r) + cyc2, fl1 + fl2, rEnd, baseEnd, sEnd, ?_, ?_, ?_, ?_, ?_⟩
      · have htot := hr1'.trans hr2
        have heq_c : ((if mL = mR then 8 else capPairNf r) + 6 * fl1) + (cyc2 + 6 * fl2) =
            ((if mL = mR then 8 else capPairNf r) + cyc2) + 6 * (fl1 + fl2) := by omega
        simpa only [heq_c] using htot
      · simp only [hdrop, List.flatMap_cons, List.length_append]
        change _ = 8 * (2 + 8 * (rem' + 1 + 1)) + 208 * (t1.length + restT.length) + cphi8 r; omega
      · simp only [hdrop, List.flatMap_cons, List.length_append]
        change baseEnd ≤ base + 32 * (t1.length + restT.length); omega
      · simp only [hdrop, List.flatMap_cons, List.length_append]
        change fl1 + fl2 ≤ t1.length + restT.length; omega
      · simpa only [hdrop, List.flatMap_cons, List.append_assoc, Nat.add_assoc] using hend

/-! ### 4. Cap Level Loop (`L15..L23`, `PC 6803..7222`) & Full `cap_pass` (`PC 6793..7222`) -/

/-- State at `PC_cap_lvl_start = 6803` before processing cap level `l ∈ 15..23`. -/
private structure CapLvlStartInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l : Nat) (r : Fin 8) (base flushes : Nat)
    (written : List Byte) (tails : List (BitVec 6)) (s : MachineState) : Prop where
  hpc : s.pc = pcAt PC_cap_lvl_start
  rx4 : s.getReg .x4 = 1#64
  rx11 : s.getReg .x11 = mask40Word
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r.val)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 (68719475936 + 32 * l + 8)
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (8 * l)
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (8 * 24)
  hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s
  hbt : BaseTableReady s
  hsrcM : CapLevelMarks s positions l
  hw : WriterState (CleanTrapdoor trapdoor) s r false base 0 written
  ht : TailState (CleanTrapdoor trapdoor) s tails flushes

/-- Single cap level `l ∈ 15..23` from `PC_cap_lvl_start` through `PC_cap_lvl_next`. -/
private theorem openRuns_cap_level {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {l base flushes : Nat} {r : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hl1 : 15 ≤ l) (hl2 : l ≤ 23)
    (hbd_w : base + 32 * (levelSize l / 2) + 40 ≤ 8556390424)
    (hbd_t : 8 * (flushes + levelSize l / 2) + 16 ≤ 48719475936)
    (hinv : CapLvlStartInv trapdoor positions l r base flushes written tails s) :
    let addFwd := capLevelFrontierFwd (tdNode trapdoor) positions l
    let addTails := capLevelFrontierTails (tdNode trapdoor) positions l
    let oddCyc := if levelSize l % 2 = 1 then 4 else 2
    ∃ cycNf flNew rEnd baseEnd s',
      OpenRuns s (cycNf + 6 * flNew) (cycNf + 6 * flNew) s' ∧
      8 * cycNf + cphi8 rEnd ≤
        8 * (6 + 7 + 2 + oddCyc + 3 + 8 * (levelSize l / 2)) + 208 * levelFrontierCount positions l + cphi8 r ∧
      baseEnd ≤ base + 32 * levelFrontierCount positions l ∧
      flNew ≤ levelFrontierCount positions l ∧
      (if l = 23 then
        s'.pc = pcAt 7223 ∧
        s'.getReg .x14 = BitVec.ofNat 64 (8 * rEnd.val) ∧
        WriterState (CleanTrapdoor trapdoor) s' rEnd false baseEnd 0 (written ++ addFwd) ∧
        TailState (CleanTrapdoor trapdoor) s' (tails ++ addTails) (flushes + flNew)
      else
        CapLvlStartInv trapdoor positions (l + 1) rEnd baseEnd (flushes + flNew) (written ++ addFwd) (tails ++ addTails) s') := by
  have hmo := capMarkOff_props l hl1 hl2
  have hsz_le := levelSize_le_max' l (by omega)
  -- 6803..6808: LD 18, LD 19, LD 20, LD 22, SRLI 23, ADD 23
  have ha0 : s.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (8 * l) := by
    rw [hinv.rx29, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have h0 := step_LD (s := s) (by decide) hinv.hpc (rfl : openInstr 6803 = .base (.LD .x18 .x29 (0#12)))
    (by rw [ha0]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  set s1 := (s.setReg .x18 (s.getMem (s.getReg .x29 + signExtend12 (0#12)))).setPC (pcAt 6804)
  have ha1 : s1.getReg .x26 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 8) := by
    simp [s1, getReg_setReg_ne', hinv.rx26, signExtend12_nonneg 0 (by omega)]
  have h1 := step_LD (s := s1) (by decide) rfl (rfl : openInstr 6804 = .base (.LD .x19 .x26 (0#12)))
    (by rw [ha1]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  set s2 := (s1.setReg .x19 (s1.getMem (s1.getReg .x26 + signExtend12 (0#12)))).setPC (pcAt 6805)
  have ha2 : s2.getReg .x29 + signExtend12 (256#12) = BitVec.ofNat 64 (256 + 8 * l) := by
    simp only [s2, s1, MachineState.getReg_setPC, getReg_setReg_ne', ne_eq, reduceCtorEq, not_false_eq_true,
      hinv.rx29, signExtend12_nonneg 256 (by omega), ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64); omega
  have h2 := step_LD (s := s2) (by decide) rfl (rfl : openInstr 6805 = .base (.LD .x20 .x29 (256#12)))
    (by rw [ha2]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  set s3 := (s2.setReg .x20 (s2.getMem (s2.getReg .x29 + signExtend12 (256#12)))).setPC (pcAt 6806)
  have ha3 : s3.getReg .x29 + signExtend12 (264#12) = BitVec.ofNat 64 (256 + 8 * (l + 1)) := by
    simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setReg_ne', ne_eq, reduceCtorEq, not_false_eq_true,
      hinv.rx29, signExtend12_nonneg 264 (by omega), ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64); omega
  have h3 := step_LD (s := s3) (by decide) rfl (rfl : openInstr 6806 = .base (.LD .x22 .x29 (264#12)))
    (by rw [ha3]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  set s4 := (s3.setReg .x22 (s3.getMem (s3.getReg .x29 + signExtend12 (264#12)))).setPC (pcAt 6807)
  have h4 := step_SRLI (s := s4) (by decide) rfl (rfl : openInstr 6807 = .base (.SRLI .x23 .x19 (1#6)))
  set s5 := (s4.setReg .x23 (s4.getReg .x19 >>> (1#6).toNat)).setPC (pcAt 6808)
  have h5 := step_ADD (s := s5) (by decide) rfl (rfl : openInstr 6808 = .base (.ADD .x23 .x22 .x23))
  set s6 := (s5.setReg .x23 (s5.getReg .x22 + s5.getReg .x23)).setPC (pcAt 6809)
  have hrun_hdr := ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5
  have hs6_18 : s6.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
    have e : s6.getReg .x18 = s.getMem (s.getReg .x29 + signExtend12 (0#12)) := by
      simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne']
    rw [e, ha0]; exact hinv.hbt.lvlBase l (by omega) hl2
  have hs6_19 : s6.getReg .x19 = BitVec.ofNat 64 (levelSize l) := by
    have e : s6.getReg .x19 = s1.getMem (s1.getReg .x26 + signExtend12 (0#12)) := by
      simp [s6, s5, s4, s3, s2, getReg_setReg_ne']
    rw [e, ha1]; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact readOnly_getMem_data_size' hinv.hro l (by omega)
  have hs6_20 : s6.getReg .x20 = BitVec.ofNat 64 (512 + capMarkOff l) := by
    have e : s6.getReg .x20 = s2.getMem (s2.getReg .x29 + signExtend12 (256#12)) := by
      simp [s6, s5, s4, s3, getReg_setReg_ne']
    rw [e, ha2]; simp only [s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hinv.hbt.cmPtr l hl1 (by omega)
  have hs6_22 : s6.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1)) := by
    have e : s6.getReg .x22 = s3.getMem (s3.getReg .x29 + signExtend12 (264#12)) := by
      simp [s6, s5, s4, getReg_setReg_ne']
    rw [e, ha3]; simp only [s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hinv.hbt.cmPtr (l + 1) (by omega) (by omega)
  have hs6_23 : s6.getReg .x23 = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2) := by
    have h19 : s4.getReg .x19 = BitVec.ofNat 64 (levelSize l) := by
      have e : s4.getReg .x19 = s1.getMem (s1.getReg .x26 + signExtend12 (0#12)) := by
        simp [s4, s3, s2, getReg_setReg_ne']
      rw [e, ha1]; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact readOnly_getMem_data_size' hinv.hro l (by omega)
    have h22 : s5.getReg .x22 = BitVec.ofNat 64 (512 + capMarkOff (l + 1)) := by
      have e : s5.getReg .x22 = s3.getMem (s3.getReg .x29 + signExtend12 (264#12)) := by
        simp [s5, s4, getReg_setReg_ne']
      rw [e, ha3]; simp only [s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact hinv.hbt.cmPtr (l + 1) (by omega) (by omega)
    have h23a : s5.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) := by
      simp only [s5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        h19, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (levelSize l) 1 (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
    simp [s6, h22, h23a, ← BitVec.ofNat_add]
  have hs6_mem : ∀ a, s6.getMem a = s.getMem a := fun _ => by simp [s6, s5, s4, s3, s2, s1]
  -- Dispatch r (6809..6823, <= 7 cyc)
  obtain ⟨cDisp, s7, hrDisp, hcDisp, hpc7, hreg7, hmem7⟩ :=
    openRuns_cap_dispatch (s := s6) r rfl (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx14])
  have hmem7_s : ∀ a, s7.getMem a = s.getMem a := fun a => (hmem7 a).trans (hs6_mem a)
  have hpInv : CapPairInv trapdoor positions l 0 r base flushes written tails s7 :=
    ⟨hpc7,
     (hreg7 .x4 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx4]),
     (hreg7 .x11 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx11]),
     (hreg7 .x18 (by decide)).trans (by simpa only [Nat.mul_zero, Nat.add_zero] using hs6_18),
     (hreg7 .x19 (by decide)).trans hs6_19,
     (hreg7 .x20 (by decide)).trans (by simpa only [Nat.mul_zero, Nat.add_zero] using hs6_20),
     (hreg7 .x22 (by decide)).trans (by simpa only [Nat.add_zero] using hs6_22),
     (hreg7 .x23 (by decide)).trans hs6_23,
     (hreg7 .x26 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx26]),
     (hreg7 .x29 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx29]),
     (hreg7 .x30 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx30]),
     fun a ha => (hmem7_s a).trans (hinv.hro a ha),
     baseTableReady_of_lowEq hinv.hbt (fun a _ => hmem7_s a),
     fun idx hidx => by simp only [MachineState.getByte, hmem7_s]; exact hinv.hsrcM idx hidx,
     fun p hp => by omega,
     writerState_of_mem_eq hinv.hw hmem7_s
       ((hreg7 .x25 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))
       ((hreg7 .x12 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne'])),
     TailState.of_proofWrite hinv.ht (fun a _ => hmem7_s a)
       ((hreg7 .x15 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))
       ((hreg7 .x16 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))
       ((hreg7 .x17 (by decide)).trans (by simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne']))⟩
  -- Pair loop (all levelSize l / 2 pairs -> PC_cap_lvl_end = 7216)
  obtain ⟨cycP, flNew, rEnd, baseEnd, s8, hrP, hamP, hbP, hflP, hend8⟩ :=
    openRuns_cap_pairs hl1 hl2 (levelSize l / 2) hmo.2.2 0 base flushes r written tails s7
      (by omega) hbd_w hbd_t hpInv
  have haddTails_len : (capLevelFrontierTails (tdNode trapdoor) positions l).length = levelFrontierCount positions l :=
    capLevelFrontierTails_length (tdNode trapdoor) positions l
  simp only [List.drop_zero] at hamP hbP hflP hend8
  change _ = 8 * (2 + 8 * (levelSize l / 2)) + 208 * (capLevelFrontierTails (tdNode trapdoor) positions l).length + cphi8 r at hamP
  rw [haddTails_len] at hamP
  change baseEnd ≤ base + 32 * (capLevelFrontierTails (tdNode trapdoor) positions l).length at hbP
  rw [haddTails_len] at hbP
  change flNew ≤ (capLevelFrontierTails (tdNode trapdoor) positions l).length at hflP
  rw [haddTails_len] at hflP
  -- PC_cap_lvl_end (7216..7219): odd promotion (2 cyc even / 4 cyc odd) -> PC_cap_lvl_next (7220)
  have he0 := step_ANDI (s := s8) (by decide) hend8.hpc (rfl : openInstr 7216 = .base (.ANDI .x6 .x19 (1#12)))
  set s9 := (s8.setReg .x6 (s8.getReg .x19 &&& signExtend12 (1#12))).setPC (pcAt 7217)
  have hs9_6 : s9.getReg .x6 = BitVec.ofNat 64 (levelSize l % 2) := by
    simp only [s9, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hend8.rx19, signExtend12_nonneg 1 (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : levelSize l < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : levelSize l % 2 < 2 ^ 64),
      Nat.and_one_is_mod]
  have hodd_stage : ∃ s10 : MachineState,
      OpenRuns s9 (if levelSize l % 2 = 1 then 3 else 1) (if levelSize l % 2 = 1 then 3 else 1) s10 ∧
      s10.pc = pcAt PC_cap_lvl_next ∧
      RegsEqExcept [.x6, .x8] s8 s10 ∧
      ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s10 ∧
      BaseTableReady s10 ∧
      CapLevelMarks s10 positions (l + 1) ∧
      WriterState (CleanTrapdoor trapdoor) s10 rEnd false baseEnd 0 (written ++ capLevelFrontierFwd (tdNode trapdoor) positions l) ∧
      TailState (CleanTrapdoor trapdoor) s10 (tails ++ capLevelFrontierTails (tdNode trapdoor) positions l) (flushes + flNew) := by
    by_cases hodd : levelSize l % 2 = 1
    · have hne0 : s9.getReg .x6 ≠ s9.getReg .x0 := by rw [hs9_6, hodd, show s9.getReg .x0 = 0#64 from rfl]; decide
      have he1 := step_BEQ_not_taken (s := s9) (by decide) rfl (rfl : openInstr 7217 = .base (.BEQ .x6 .x0 (12#13))) hne0
      set s9a := s9.setPC (pcAt 7218)
      have ha_lbu : s9a.getReg .x20 + signExtend12 (0#12) = BitVec.ofNat 64 (512 + capMarkOff l + 2 * (levelSize l / 2)) := by
        simp [s9a, s9, getReg_setReg_ne', hend8.rx20, signExtend12_nonneg 0 (by omega)]
      have he2 := step_LBU (s := s9a) (by decide) rfl (rfl : openInstr 7218 = .base (.LBU .x8 .x20 (0#12)))
        (by rw [ha_lbu]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      set s9b := (s9a.setReg .x8 ((s9a.getByte (s9a.getReg .x20 + signExtend12 (0#12))).zeroExtend 64)).setPC (pcAt 7219)
      have ha_sb : s9b.getReg .x22 + signExtend12 (0#12) = BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2) := by
        simp [s9b, s9a, s9, getReg_setReg_ne', hend8.rx22, signExtend12_nonneg 0 (by omega)]
      have he3 := step_SB (s := s9b) (by decide) rfl (rfl : openInstr 7219 = .base (.SB .x22 .x8 (0#12)))
        (by rw [ha_sb]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      set s10 := (s9b.setByte (s9b.getReg .x22 + signExtend12 (0#12)) ((s9b.getReg .x8).truncate 8)).setPC (pcAt 7220)
      have hcap_mem := setByte_cap_mem_pres (s := s9b) (dst := 512 + capMarkOff (l + 1) + levelSize l / 2)
        (b := (s9b.getReg .x8).truncate 8) (by omega) (by have := levelSize_step l (by omega); omega)
      have hmem10_eq : ∀ a : Word, s10.getMem a = (s9b.setByte (BitVec.ofNat 64 (512 + capMarkOff (l + 1) + levelSize l / 2)) ((s9b.getReg .x8).truncate 8)).getMem a := fun _ => by
        simp [s10, ha_sb]
      have hmem9b_8 : ∀ a, s9b.getMem a = s8.getMem a := fun _ => by simp [s9b, s9a, s9]
      refine ⟨s10, by simp only [hodd, ↓reduceIte]; exact (he1.trans he2).trans he3, rfl, ?_,
        fun a ha => by rw [hmem10_eq, hcap_mem.2 a (by omega), hmem9b_8]; exact hend8.hro a ha,
        baseTableReady_of_lowEq hend8.hbt (fun a ha => by rw [hmem10_eq, hcap_mem.1 a ha, hmem9b_8]),
        ?_, ?_, ?_⟩
      · intro reg hreg
        have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
        have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
        simp [s10, s9b, s9a, s9, getReg_setByte, getReg_setReg_ne' .x8 reg h8'.symm, getReg_setReg_ne' .x6 reg h6'.symm]
      · intro idx hidx
        have hsz1 : levelSize (l + 1) = levelSize l / 2 + 1 := by rw [levelSize_step l (by omega)]; omega
        simp only [s10, getByte_setPC, ha_sb]
        by_cases hlast : idx = levelSize l / 2
        · subst hlast
          rw [set_byte_read]
          simp only [↓reduceIte, capMark_succ positions l (levelSize l / 2) hl1,
            show ¬ (2 * (levelSize l / 2) + 1 < levelSize l) by omega,
            show 2 * (levelSize l / 2) < levelSize l by omega]
          have hb_eq : (s9b.getReg .x8).truncate 8 = if capMark positions l (2 * (levelSize l / 2)) then 1#8 else 0#8 := by
            have e : s9b.getReg .x8 = (s9a.getByte (s9a.getReg .x20 + signExtend12 (0#12))).zeroExtend 64 := by
              simp [s9b]
            rw [e, ha_lbu]
            simp only [s9a, s9, getByte_setPC, getByte_setReg, hend8.hsrcM (2 * (levelSize l / 2)) (by omega)]
            cases capMark positions l (2 * (levelSize l / 2)) <;> decide
          exact hb_eq
        · rw [setByte_cap_getByte_ne (by omega) (by omega) (by omega)]
          simp only [s9b, s9a, s9, getByte_setPC, getByte_setReg]; exact hend8.hdstM idx (by omega)
      · refine ⟨hend8.hw.hbase8, hend8.hw.hdst8, hend8.hw.hlen, hend8.hw.hbound,
          by simp [s10, s9b, s9a, s9, getReg_setByte, getReg_setReg_ne', hend8.hw.rx25],
          hend8.hw.hflushed_ok, fun hcl j hj => ?_, fun hcl => ?_⟩
        · have hlen := hend8.hw.hlen; have hbd := hend8.hw.hbound
          have hal := alignToDword_ofNat_eq (8 * ((11341403200 + j) / 8)) ((11341403200 + j) % 8) (by omega) (by omega)
          rw [show 8 * ((11341403200 + j) / 8) + (11341403200 + j) % 8 = 11341403200 + j by omega] at hal
          have hm : s10.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + j))) =
              s8.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + j))) := by
            rw [hmem10_eq, hcap_mem.2 _ (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), hmem9b_8]
          exact (by simp only [MachineState.getByte, hm] : s10.getByte _ = s8.getByte _).trans (hend8.hw.hbytes hcl j hj)
        · have h12 : s10.getReg .x12 = s8.getReg .x12 := by simp [s10, s9b, s9a, s9, getReg_setByte, getReg_setReg_ne']
          have hrem := hend8.hw.hrem hcl; simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
          by_cases hr0 : rEnd.val = 0
          · simp [hr0]
          · simp only [hr0, ↓reduceIte] at hrem ⊢
            exact ⟨fun j hj => by rw [h12]; exact hrem.1 j hj, fun j h1 h2 => by rw [h12]; exact hrem.2 j h1 h2⟩
      · refine ⟨hend8.ht.hbits, hend8.ht.hbound,
          (by simp [s10, s9b, s9a, s9, getReg_setByte, getReg_setReg_ne'] : s10.getReg .x15 = s8.getReg .x15).trans hend8.ht.rx15,
          (by simp [s10, s9b, s9a, s9, getReg_setByte, getReg_setReg_ne'] : s10.getReg .x17 = s8.getReg .x17).trans hend8.ht.rx17,
          fun hcl => ?_⟩
        obtain ⟨tBuf, hlt, hx16, hsum⟩ := hend8.ht.hdata hcl
        refine ⟨tBuf, hlt, (by simp [s10, s9b, s9a, s9, getReg_setByte, getReg_setReg_ne'] : s10.getReg .x16 = s8.getReg .x16).trans hx16, ?_⟩
        have hmap : ((List.range (8 * (flushes + flNew))).map fun j => s10.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
            ((List.range (8 * (flushes + flNew))).map fun j => s8.getByte (BitVec.ofNat 64 (tailBufBase + j))) := by
          apply List.map_congr_left; intro j hj; have hj' := List.mem_range.mp hj
          have hbd := hend8.ht.hbound
          have hal := alignToDword_ofNat_eq (8 * ((tailBufBase + j) / 8)) ((tailBufBase + j) % 8) (by omega) (by unfold tailBufBase; omega)
          rw [show 8 * ((tailBufBase + j) / 8) + (tailBufBase + j) % 8 = tailBufBase + j by omega] at hal
          simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
          rw [hmem10_eq, hcap_mem.2 _ (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; unfold tailBufBase; omega), hmem9b_8]
        rw [hmap]; exact hsum
    · have heven : levelSize l % 2 = 0 := by omega
      have hbr : pcAt 7217 + signExtend13 (12#13) = pcAt 7220 := by
        simpa only [show 4 * (7220 - 7217) = 12 by decide] using pcAt_add_pos13 7217 7220 (by omega) (by omega)
      have he1 := step_BEQ_taken (s := s9) (by decide) rfl (rfl : openInstr 7217 = .base (.BEQ .x6 .x0 (12#13)))
        (by rw [hs9_6, heven]; rfl) hbr
      set s10 := s9.setPC (pcAt 7220)
      have hsz1 : levelSize (l + 1) = levelSize l / 2 := by rw [levelSize_step l (by omega)]; omega
      refine ⟨s10, by simp only [hodd, ↓reduceIte]; exact he1, rfl,
        fun reg hreg => by have h6' : reg ≠ .x6 := fun h => hreg (by simp [h]); simp [s10, s9, getReg_setReg_ne' .x6 reg h6'.symm],
        fun a ha => (by simp [s10, s9] : s10.getMem a = s8.getMem a).trans (hend8.hro a ha),
        baseTableReady_of_lowEq hend8.hbt (fun _ _ => by simp [s10, s9]),
        fun idx hidx => by simp only [s10, s9, getByte_setPC, getByte_setReg]; exact hend8.hdstM idx (by omega),
        writerState_of_mem_eq hend8.hw (fun _ => by simp [s10, s9]) (by simp [s10, s9, getReg_setReg_ne']) (by simp [s10, s9, getReg_setReg_ne']),
        TailState.of_proofWrite hend8.ht (fun _ _ => by simp [s10, s9]) (by simp [s10, s9, getReg_setReg_ne'])
          (by simp [s10, s9, getReg_setReg_ne']) (by simp [s10, s9, getReg_setReg_ne'])⟩
  obtain ⟨s10, hrOdd, hpc10, hreg10, hro10, hbt10, hM10, hw10, ht10⟩ := hodd_stage
  -- PC_cap_lvl_next (7220..7222): ADDI x29 8; ADDI x26 32; BNE x29 x30 cap_lvl_start (3 cyc)
  have hn0 := step_ADDI (s := s10) (by decide) hpc10 (rfl : openInstr 7220 = .base (.ADDI .x29 .x29 (8#12)))
  set s11 := (s10.setReg .x29 (s10.getReg .x29 + signExtend12 (8#12))).setPC (pcAt 7221)
  have hn1 := step_ADDI (s := s11) (by decide) rfl (rfl : openInstr 7221 = .base (.ADDI .x26 .x26 (32#12)))
  set s12 := (s11.setReg .x26 (s11.getReg .x26 + signExtend12 (32#12))).setPC (pcAt 7222)
  have hs12_29 : s12.getReg .x29 = BitVec.ofNat 64 (8 * (l + 1)) := by
    simp only [s12, s11, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq,
      ne_eq, reduceCtorEq, not_false_eq_true, (hreg10 .x29 (by decide)).trans hend8.rx29,
      signExtend12_nonneg 8 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
  have hs12_26 : s12.getReg .x26 = BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 8) := by
    simp only [s12, s11, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq,
      ne_eq, reduceCtorEq, not_false_eq_true, (hreg10 .x26 (by decide)).trans hend8.rx26,
      signExtend12_nonneg 32 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
  have hs12_30 : s12.getReg .x30 = BitVec.ofNat 64 (8 * 24) := by
    simp [s12, s11, getReg_setReg_ne', (hreg10 .x30 (by decide)).trans hend8.rx30]
  have hrun_pre := (((((hrun_hdr.trans hrDisp).trans hrP).trans he0).trans hrOdd).trans hn0).trans hn1
  set oddCyc := if levelSize l % 2 = 1 then 4 else 2
  set cycNf := 6 + cDisp + cycP + oddCyc + 3
  have ham_tot : 8 * cycNf + cphi8 rEnd ≤
      8 * (6 + 7 + 2 + oddCyc + 3 + 8 * (levelSize l / 2)) + 208 * levelFrontierCount positions l + cphi8 r := by
    unfold cycNf; omega
  by_cases h23 : l = 23
  · have hn2 := step_BNE_not_taken (s := s12) (by decide) rfl
      (rfl : openInstr 7222 = .base (.BNE .x29 .x30 (6516#13))) (by rw [hs12_29, hs12_30, h23])
    set s13 := s12.setPC (pcAt 7223)
    have hmem13 : ∀ a, s13.getMem a = s10.getMem a := fun _ => by simp [s13, s12, s11]
    refine ⟨cycNf, flNew, rEnd, baseEnd, s13, ?_, ham_tot, hbP, hflP, ?_⟩
    · have htot := hrun_pre.trans hn2
      have heq_c : 1 + 1 + 1 + 1 + 1 + 1 + cDisp + (cycP + 6 * flNew) + 1 +
          (if levelSize l % 2 = 1 then 3 else 1) + 1 + 1 + 1 = cycNf + 6 * flNew := by
        unfold cycNf oddCyc; split_ifs <;> omega
      simpa only [heq_c] using htot
    · simp only [eq_true h23, ↓reduceIte]
      refine ⟨rfl,
        by simp [s13, s12, s11, getReg_setReg_ne', (hreg10 .x14 (by decide)).trans hend8.rx14],
        writerState_of_mem_eq hw10 hmem13 (by simp [s13, s12, s11, getReg_setReg_ne']) (by simp [s13, s12, s11, getReg_setReg_ne']),
        TailState.of_proofWrite ht10 (fun a _ => hmem13 a) (by simp [s13, s12, s11, getReg_setReg_ne'])
          (by simp [s13, s12, s11, getReg_setReg_ne']) (by simp [s13, s12, s11, getReg_setReg_ne'])⟩
  · have hne29 : s12.getReg .x29 ≠ s12.getReg .x30 := by
      rw [hs12_29, hs12_30]; intro h; have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * (l + 1) < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 * 24 < 2 ^ 64)] at hn; omega
    have hbr : pcAt 7222 + signExtend13 (6516#13) = pcAt PC_cap_lvl_start := by
      simpa only [PC_cap_lvl_start, show 8192 - 4 * (7222 - 6803) = 6516 by decide] using pcAt_add_neg13 7222 6803 (by omega) (by omega)
    have hn2 := step_BNE_taken (s := s12) (by decide) rfl
      (rfl : openInstr 7222 = .base (.BNE .x29 .x30 (6516#13))) hne29 hbr
    set s13 := s12.setPC (pcAt PC_cap_lvl_start)
    have hmem13 : ∀ a, s13.getMem a = s10.getMem a := fun _ => by simp [s13, s12, s11]
    refine ⟨cycNf, flNew, rEnd, baseEnd, s13, ?_, ham_tot, hbP, hflP, ?_⟩
    · have htot := hrun_pre.trans hn2
      have heq_c : 1 + 1 + 1 + 1 + 1 + 1 + cDisp + (cycP + 6 * flNew) + 1 +
          (if levelSize l % 2 = 1 then 3 else 1) + 1 + 1 + 1 = cycNf + 6 * flNew := by
        unfold cycNf oddCyc; split_ifs <;> omega
      simpa only [heq_c] using htot
    · simp only [eq_false h23, ↓reduceIte]
      refine ⟨rfl,
        by simp [s13, s12, s11, getReg_setReg_ne', (hreg10 .x4 (by decide)).trans hend8.rx4],
        by simp [s13, s12, s11, getReg_setReg_ne', (hreg10 .x11 (by decide)).trans hend8.rx11],
        by simp [s13, s12, s11, getReg_setReg_ne', (hreg10 .x14 (by decide)).trans hend8.rx14],
        by simp [s13, hs12_26], by simp [s13, hs12_29], by simp [s13, hs12_30],
        fun a ha => (hmem13 a).trans (hro10 a ha),
        baseTableReady_of_lowEq hbt10 (fun a _ => hmem13 a),
        fun idx hidx => by simp only [MachineState.getByte, hmem13]; exact hM10 idx hidx,
        writerState_of_mem_eq hw10 hmem13 (by simp [s13, s12, s11, getReg_setReg_ne']) (by simp [s13, s12, s11, getReg_setReg_ne']),
        TailState.of_proofWrite ht10 (fun a _ => hmem13 a) (by simp [s13, s12, s11, getReg_setReg_ne'])
          (by simp [s13, s12, s11, getReg_setReg_ne']) (by simp [s13, s12, s11, getReg_setReg_ne'])⟩

private theorem levelSize_half_le_171 (l : Nat) (h1 : 15 ≤ l) (h2 : l ≤ 23) :
    levelSize l / 2 ≤ 171 := by
  interval_cases l <;> decide

private theorem openRuns_cap_levels {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} :
    ∀ rem (_hrem1 : 1 ≤ rem) (step0 base flushes : Nat) (r : Fin 8)
      (written : List Byte) (tails : List (BitVec 6)) (s : MachineState),
      step0 + rem = 9 →
      base + 6000 * rem + 40 ≤ 8556390424 →
      8 * (flushes + 171 * rem) + 16 ≤ 48719475936 →
      CapLvlStartInv trapdoor positions (15 + step0) r base flushes written tails s →
      let steps := (List.range 9).drop step0
      let addFwd := steps.flatMap fun k => capLevelFrontierFwd (tdNode trapdoor) positions (15 + k)
      let addTails := steps.flatMap fun k => capLevelFrontierTails (tdNode trapdoor) positions (15 + k)
      let pairSum := (steps.map fun k => levelSize (15 + k) / 2).sum
      let oddSum := (steps.map fun k => if levelSize (15 + k) % 2 = 1 then 4 else 2).sum
      let fSum := (steps.map fun k => levelFrontierCount positions (15 + k)).sum
      ∃ cycNf flNew rEnd baseEnd s',
        OpenRuns s (cycNf + 6 * flNew) (cycNf + 6 * flNew) s' ∧
        8 * cycNf + cphi8 rEnd ≤ 8 * (18 * rem + oddSum + 8 * pairSum) + 208 * fSum + cphi8 r ∧
        baseEnd ≤ base + 32 * fSum ∧
        flNew ≤ fSum ∧
        s'.pc = pcAt 7223 ∧
        s'.getReg .x14 = BitVec.ofNat 64 (8 * rEnd.val) ∧
        WriterState (CleanTrapdoor trapdoor) s' rEnd false baseEnd 0 (written ++ addFwd) ∧
        TailState (CleanTrapdoor trapdoor) s' (tails ++ addTails) (flushes + flNew) := by
  intro rem
  induction rem with
  | zero => intro h; omega
  | succ rem ih =>
    intro _ step0 base flushes r written tails s hsum hbd_w hbd_t hinv
    set l := 15 + step0
    have hl1 : 15 ≤ l := by omega
    have hl2 : l ≤ 23 := by omega
    have hsz_half_le : levelSize l / 2 ≤ 171 := levelSize_half_le_171 l hl1 hl2
    have hdrop : (List.range 9).drop step0 = step0 :: (List.range 9).drop (step0 + 1) := by
      have := List.drop_eq_getElem_cons (l := List.range 9) (i := step0) (by simp; omega)
      simpa only [List.getElem_range] using this
    have hbw1 : base + 32 * (levelSize l / 2) + 40 ≤ 8556390424 :=
      Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left
        (Nat.le_trans (Nat.mul_le_mul_left 32 hsz_half_le)
          (Nat.le_trans (by decide : 32 * 171 ≤ 6000 * 1) (Nat.mul_le_mul_left 6000 (Nat.succ_pos rem)))) base) 40) hbd_w
    have hbt1 : 8 * (flushes + levelSize l / 2) + 16 ≤ 48719475936 :=
      Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 8 (Nat.add_le_add_left
        (Nat.le_trans hsz_half_le
          (Nat.le_trans (by decide : 171 ≤ 171 * 1) (Nat.mul_le_mul_left 171 (Nat.succ_pos rem)))) flushes)) 16) hbd_t
    obtain ⟨cyc1, fl1, r1, base1, s1, hr1, ham1, hb1, hfl1, hpost1⟩ :=
      openRuns_cap_level hl1 hl2 hbw1 hbt1 hinv
    cases rem with
    | zero =>
      have h23 : l = 23 := by omega
      simp only [eq_true h23, ↓reduceIte] at hpost1
      have hdrop0 : (List.range 9).drop (step0 + 1) = [] := by rw [List.drop_eq_nil_iff]; simp; omega
      have hsteps : (List.range 9).drop step0 = [step0] := by rw [hdrop, hdrop0]
      have hl_eq : 15 + step0 = l := rfl
      refine ⟨cyc1, fl1, r1, base1, s1, hr1, ?_, ?_, ?_, hpost1.1, hpost1.2.1, ?_, ?_⟩
      · simp only [hsteps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hl_eq]; omega
      · simp only [hsteps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hl_eq]; exact hb1
      · simp only [hsteps, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, hl_eq]; exact hfl1
      · simpa only [hsteps, List.flatMap_cons, List.flatMap_nil, List.append_nil, hl_eq] using hpost1.2.2.1
      · simpa only [hsteps, List.flatMap_cons, List.flatMap_nil, List.append_nil, hl_eq] using hpost1.2.2.2
    | succ rem' =>
      have hn23 : l ≠ 23 := by omega
      simp only [eq_false hn23, ↓reduceIte] at hpost1
      have hf1_le : levelFrontierCount positions l ≤ levelSize l / 2 := by
        unfold levelFrontierCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      have hpost1' : CapLvlStartInv trapdoor positions (15 + (step0 + 1)) r1 base1 (flushes + fl1)
          (written ++ capLevelFrontierFwd (tdNode trapdoor) positions l)
          (tails ++ capLevelFrontierTails (tdNode trapdoor) positions l) s1 := by
        rw [← Nat.add_assoc]; exact hpost1
      have hbw2 : base1 + 6000 * (rem' + 1) + 40 ≤ 8556390424 := by
        have h1 : base1 ≤ base + 6000 :=
          Nat.le_trans hb1 (Nat.add_le_add_left (Nat.le_trans (Nat.mul_le_mul_left 32 (Nat.le_trans hf1_le hsz_half_le)) (by decide : 32 * 171 ≤ 6000)) base)
        exact calc base1 + 6000 * (rem' + 1) + 40
          _ ≤ (base + 6000) + 6000 * (rem' + 1) + 40 := Nat.add_le_add_right (Nat.add_le_add_right h1 _) 40
          _ = base + 6000 * (rem' + 1 + 1) + 40 := by
              rw [Nat.mul_succ 6000 (rem' + 1), Nat.add_assoc base 6000, Nat.add_comm 6000]
          _ ≤ 8556390424 := hbd_w
      have hbt2 : 8 * (flushes + fl1 + 171 * (rem' + 1)) + 16 ≤ 48719475936 := by
        have h1 : fl1 ≤ 171 := Nat.le_trans hfl1 (Nat.le_trans hf1_le hsz_half_le)
        have h2 : flushes + fl1 + 171 * (rem' + 1) ≤ flushes + 171 * (rem' + 1 + 1) :=
          calc flushes + fl1 + 171 * (rem' + 1)
            _ ≤ flushes + 171 + 171 * (rem' + 1) := Nat.add_le_add_right (Nat.add_le_add_left h1 flushes) _
            _ = flushes + 171 * (rem' + 1 + 1) := by
                rw [Nat.mul_succ 171 (rem' + 1), Nat.add_assoc flushes 171, Nat.add_comm 171]
        exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 8 h2) 16) hbd_t
      obtain ⟨cyc2, fl2, rEnd, baseEnd, sEnd, hr2, ham2, hb2, hfl2, hpcE, hx14E, hwE, htE⟩ :=
        ih (Nat.succ_pos _) (step0 + 1) base1 (flushes + fl1) r1
          (written ++ capLevelFrontierFwd (tdNode trapdoor) positions l)
          (tails ++ capLevelFrontierTails (tdNode trapdoor) positions l) s1
          (by omega) hbw2 hbt2 hpost1'
      have hl_eq : 15 + step0 = l := rfl
      refine ⟨cyc1 + cyc2, fl1 + fl2, rEnd, baseEnd, sEnd, ?_, ?_, ?_, ?_, hpcE, hx14E, ?_, ?_⟩
      · have htot := hr1.trans hr2
        have heq_c : (cyc1 + 6 * fl1) + (cyc2 + 6 * fl2) = (cyc1 + cyc2) + 6 * (fl1 + fl2) := by omega
        simpa only [heq_c] using htot
      · simp only [hdrop, List.map_cons, List.sum_cons, hl_eq]; omega
      · simp only [hdrop, List.map_cons, List.sum_cons, hl_eq]; omega
      · simp only [hdrop, List.map_cons, List.sum_cons, hl_eq]; omega
      · simpa only [hdrop, List.flatMap_cons, List.append_assoc, hl_eq] using hwE
      · simpa only [hdrop, List.flatMap_cons, List.append_assoc, Nat.add_assoc, hl_eq] using htE

/-- Full cap pass from `PC_cap_pass = 6793` to `PC 7223` (`flush_wbuf`). -/
theorem openRuns_cap_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {rMid : Fin 8} {baseMid recFlushes : Nat}
    {allRecFwd : List Byte} {allRecTails : List (BitVec 6)} {s : MachineState}
    (hbase_bd : baseMid + 60000 ≤ 8556390424)
    (hfl_bd : 8 * (recFlushes + 1600) + 16 ≤ 48719475936)
    (hinv : CapEntryInv trapdoor positions rMid baseMid allRecFwd allRecTails recFlushes s) :
    let capFwd := capFrontierFwd (tdNode trapdoor) positions
    let capTails := capFrontierTails (tdNode trapdoor) positions
    ∃ capCycNf capFlushes rEnd baseEnd s',
      OpenRuns s (capCycNf + 6 * capFlushes) (capCycNf + 6 * capFlushes) s' ∧
      8 * capCycNf + cphi8 rEnd ≤ 58976 + cphi8 rMid ∧
      64 * capFlushes ≤ 63 + 6 * capTails.length ∧
      64 * (recFlushes + capFlushes) ≤ 6 * (allRecTails ++ capTails).length ∧
      s'.pc = pcAt 7223 ∧
      s'.getReg .x14 = BitVec.ofNat 64 (8 * rEnd.val) ∧
      WriterState (CleanTrapdoor trapdoor) s' rEnd false baseEnd 0 (allRecFwd ++ capFwd) ∧
      TailState (CleanTrapdoor trapdoor) s' (allRecTails ++ capTails) (recFlushes + capFlushes) := by
  -- 6793..6802: load_const(x2, 68719475936) + ADDI x29 120; ADDI x30 192; ADDI x26 x2 488 (10 cyc)
  have h0 := step_ADDI (s := s) (by decide) hinv.hpc (rfl : openInstr 6793 = .base (.ADDI .x2 .x0 (7#12)))
  set s1 := (s.setReg .x2 (s.getReg .x0 + signExtend12 (7#12))).setPC (pcAt 6794)
  have h1 := step_SLLI (s := s1) (by decide) rfl (rfl : openInstr 6794 = .base (.SLLI .x2 .x2 (11#6)))
  set s2 := (s1.setReg .x2 (s1.getReg .x2 <<< (11#6).toNat)).setPC (pcAt 6795)
  have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 6795 = .base (.ADDI .x2 .x2 (2047#12)))
  set s3 := (s2.setReg .x2 (s2.getReg .x2 + signExtend12 (2047#12))).setPC (pcAt 6796)
  have h3 := step_SLLI (s := s3) (by decide) rfl (rfl : openInstr 6796 = .base (.SLLI .x2 .x2 (11#6)))
  set s4 := (s3.setReg .x2 (s3.getReg .x2 <<< (11#6).toNat)).setPC (pcAt 6797)
  have h4 := step_ADDI (s := s4) (by decide) rfl (rfl : openInstr 6797 = .base (.ADDI .x2 .x2 (2047#12)))
  set s5 := (s4.setReg .x2 (s4.getReg .x2 + signExtend12 (2047#12))).setPC (pcAt 6798)
  have h5 := step_SLLI (s := s5) (by decide) rfl (rfl : openInstr 6798 = .base (.SLLI .x2 .x2 (11#6)))
  set s6 := (s5.setReg .x2 (s5.getReg .x2 <<< (11#6).toNat)).setPC (pcAt 6799)
  have h6 := step_ADDI (s := s6) (by decide) rfl (rfl : openInstr 6799 = .base (.ADDI .x2 .x2 (1248#12)))
  set s7 := (s6.setReg .x2 (s6.getReg .x2 + signExtend12 (1248#12))).setPC (pcAt 6800)
  have h7 := step_ADDI (s := s7) (by decide) rfl (rfl : openInstr 6800 = .base (.ADDI .x29 .x0 (120#12)))
  set s8 := (s7.setReg .x29 (s7.getReg .x0 + signExtend12 (120#12))).setPC (pcAt 6801)
  have h8 := step_ADDI (s := s8) (by decide) rfl (rfl : openInstr 6801 = .base (.ADDI .x30 .x0 (192#12)))
  set s9 := (s8.setReg .x30 (s8.getReg .x0 + signExtend12 (192#12))).setPC (pcAt 6802)
  have h9 := step_ADDI (s := s9) (by decide) rfl (rfl : openInstr 6802 = .base (.ADDI .x26 .x2 (488#12)))
  set s10 := (s9.setReg .x26 (s9.getReg .x2 + signExtend12 (488#12))).setPC (pcAt 6803)
  have hrun_hdr := ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9
  have hs7_2 : s7.getReg .x2 = BitVec.ofNat 64 68719475936 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, reduceCtorEq, not_false_eq_true, show s.getReg .x0 = 0#64 from rfl]
    decide
  have hs10_mem : ∀ a, s10.getMem a = s.getMem a := fun _ => by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  have hstart15 : CapLvlStartInv trapdoor positions 15 rMid baseMid recFlushes allRecFwd allRecTails s10 :=
    ⟨rfl,
     by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx4],
     by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx11],
     by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hinv.rx14],
     by simp [s10, s9, s8, getReg_setReg_ne', hs7_2, signExtend12_nonneg 488 (by omega), ← BitVec.ofNat_add],
     by simp [s10, s9, s8, getReg_setReg_ne', show s7.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 120 (by omega)],
     by simp [s10, s9, getReg_setReg_ne', show s8.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 192 (by omega)],
     fun a ha => (hs10_mem a).trans (hinv.hro a ha),
     baseTableReady_of_lowEq hinv.hbt (fun a _ => hs10_mem a),
     fun idx hidx => by simp only [MachineState.getByte, hs10_mem]; exact capMark15_of_state hinv.hcm idx hidx,
     writerState_of_mem_eq hinv.hw hs10_mem
       (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne'])
       (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne']),
     TailState.of_proofWrite hinv.ht (fun a _ => hs10_mem a)
       (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne'])
       (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne'])
       (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne'])⟩
  have hbw9 : baseMid + 6000 * 9 + 40 ≤ 8556390424 :=
    Nat.le_trans (by rw [Nat.add_assoc]; exact Nat.add_le_add_left (by decide : 6000 * 9 + 40 ≤ 60000) baseMid) hbase_bd
  have hbt9 : 8 * (recFlushes + 171 * 9) + 16 ≤ 48719475936 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 8 (Nat.add_le_add_left (by decide : 171 * 9 ≤ 1600) recFlushes)) 16) hfl_bd
  obtain ⟨cycLvls, capFl, rEnd, baseEnd, sEnd, hrLvls, hamLvls, _, _, hpcEnd, hx14End, hwEnd, htEnd⟩ :=
    openRuns_cap_levels 9 (by decide) 0 baseMid recFlushes rMid allRecFwd allRecTails s10
      rfl hbw9 hbt9 hstart15
  simp only [List.drop_zero] at hamLvls hwEnd htEnd
  change WriterState (CleanTrapdoor trapdoor) sEnd rEnd false baseEnd 0
      (allRecFwd ++ capFrontierFwd (tdNode trapdoor) positions) at hwEnd
  change TailState (CleanTrapdoor trapdoor) sEnd
      (allRecTails ++ capFrontierTails (tdNode trapdoor) positions) (recFlushes + capFl) at htEnd
  have hpair_eq : ((List.range 9).map fun k => levelSize (15 + k) / 2).sum = 341 := by decide
  have hodd_eq : ((List.range 9).map fun k => if levelSize (15 + k) % 2 = 1 then 4 else 2).sum = 26 := by decide
  have hf_eq : ((List.range 9).map fun k => levelFrontierCount positions (15 + k)).sum = capFrontierCount positions := by
    unfold capFrontierCount
    have haux : ∀ n (f : Nat → Nat), ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
      intro n f; induction n with
      | zero => simp
      | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih, Finset.sum_range_succ]
    exact haux 9 (fun k => levelFrontierCount positions (15 + k))
  have hf_le := cap_frontier_le_171 positions
  have hbits_mid := hinv.ht.hbits
  have hbits_end := htEnd.hbits
  have hmod_lt : (6 * allRecTails.length) % 64 < 64 := Nat.mod_lt _ (by omega)
  refine ⟨10 + cycLvls, capFl, rEnd, baseEnd, sEnd, ?_, ?_, ?_, ?_, hpcEnd, hx14End, hwEnd, htEnd⟩
  · have htot := hrun_hdr.trans hrLvls
    have heq_c : 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (cycLvls + 6 * capFl) = (10 + cycLvls) + 6 * capFl := by omega
    simpa only [heq_c] using htot
  · rw [hpair_eq, hodd_eq, hf_eq] at hamLvls; omega
  · simp only [List.length_append] at hbits_end; omega
  · omega

/-! ### 5. End-to-End Fast Opening Specification (`≤ 65,740` cycles at `k = 128`) -/

private theorem openSub_run_opening (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    openSub.run .opening (trapdoor, positions) =
      execute (openSub.image .opening) (openSub.steps .opening)
        (openSub.initialState .opening (trapdoor, positions)) true := by
  unfold Submission.run; dsimp only; simp only [↓reduceIte]; rfl

theorem opening_exec_spec (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    ∃ exec : Execution,
      openSub.run .opening (trapdoor, positions) = pure exec ∧
      exec.exit = .success ∧
      exec.oracleCalls = 0 ∧
      (exec.state.getReg .x11).toNat =
        (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length ∧
      (CleanTrapdoor trapdoor →
        ProofPrefix exec.state (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions)) ∧
      (positions.card = BATCH → exec.cycles ≤ 65740) := by
  have hsteps : openSub.steps .opening = 274877906944 := rfl
  rw [openSub_run_opening trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨s4, hr4, hpc4, hx5, hx10, hx11⟩ := openRuns_entry_empty trapdoor positions hempty
    have hexec := OpenRuns.halt (haltIdx := 4) (totalFuel := openSub.steps .opening)
      hr4 (by decide) rfl hpc4 hx5 hx10 (by rw [hsteps]; omega)
    have href : referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions = [] := by
      unfold referenceProof; simp only [hempty, ↓reduceIte]
    refine ⟨{ exit := .success, state := s4, cycles := 5, oracleCalls := 0 }, hexec, rfl, rfl,
      by rw [href, hx11]; rfl, fun _ j hj => by rw [href] at hj; exact absurd hj (Nat.not_lt_zero _),
      fun _ => by dsimp only; omega⟩
  · have hpos : 0 < positions.card := Nat.pos_of_ne_zero hempty
    have hcard := positions_card_le' positions
    obtain ⟨sEnt, hrEnt, hpcEnt, rx1, rx2, rx3, rx4, rx7, rx9, rx11, rx13, rx14, rx18, rx19,
      rx20, rx21, rx23, rx24, rx26, rx27, rx29, rx30, rx31, hro, hbt, hcm, htbl, hw0, ht0⟩ :=
      openRuns_entry_nonzero trapdoor positions hpos
    have hrecInv : RecInv trapdoor positions 0 ⟨0, by omega⟩ 0 [] [] 0 false sEnt :=
      ⟨hpcEnt, ⟨rx1, rx2, rx3, rx4, rx7, rx9, rx11, rx13, rx14, rx18, rx19, rx20, rx21, rx23,
        by simpa only [Nat.mul_zero, Nat.add_zero] using rx24, rx26, rx27, rx29, rx30, rx31⟩,
       hro, hbt, hcm, htbl, hw0, ht0⟩
    obtain ⟨recSteps, recNf, recFl, rMid, baseMid, sCap, hrecSt_le, hrRec, hrecAmort, hrecTails_le, hrecFl_le, hcapInv⟩ :=
      openRuns_rec_all hempty hrecInv
    set allRecFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    set allRecTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    have hrecFwd_le : allRecFwd.length ≤ 501 * positions.card := by
      have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
      have haux : ∀ l : List Index, (l.flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))).length ≤ 501 * l.length := by
        intro l; induction l with
        | nil => simp
        | cons x xs ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          have := recordFwd_length_le_501 (tdNode trapdoor) (tdSalt trapdoor) x; omega
      simpa only [hlen] using haux (positions.sort (· ≤ ·))
    have hbaseMid_le : baseMid ≤ allRecFwd.length := by have := hcapInv.hw.hlen; omega
    obtain ⟨capNf, capFl, rEnd, baseEnd, sEpi, hrCap, hcapAmort, hcapFl_le, htotFl_le, hpcEpi, hx14Epi, hwEpi, htEpi⟩ :=
      openRuns_cap_all (by omega) (by omega) hcapInv
    have href_len := referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
    have href_eq : referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions =
        (allRecFwd ++ capFrontierFwd (tdNode trapdoor) positions) ++
        pack6BitsRev (allRecTails ++ capFrontierTails (tdNode trapdoor) positions) := by
      unfold referenceProof referenceProofFwd referenceProofTails
      simp only [hempty, ↓reduceIte]; rfl
    have hbd_p : (allRecFwd ++ capFrontierFwd (tdNode trapdoor) positions).length +
        (pack6Bits (allRecTails ++ capFrontierTails (tdNode trapdoor) positions)).length ≤ 8556390424 := by
      rw [href_eq, List.length_append, pack6BitsRev_length, ← pack6Bits_length] at href_len
      exact href_len
    obtain ⟨tailEpiCyc, sHalt, hrEpi, htailEpi_any, htailEpi_le, hpcH, hx5H, hx10H, hx11H, hprefH⟩ :=
      openRuns_epilogue hbd_p hpcEpi hx14Epi hwEpi htEpi
    set totSteps := 241 + recSteps + (capNf + 6 * capFl) + ((2 + 5 * rEnd.val) + tailEpiCyc)
    set totCyc := 241 + (recNf + 4 * recFl) + (capNf + 6 * capFl) + ((2 + 5 * rEnd.val) + tailEpiCyc)
    have hrunAll : OpenRuns (openSub.initialState .opening (trapdoor, positions)) totSteps totCyc sHalt := by
      have h := ((hrEnt.trans hrRec).trans hrCap).trans hrEpi
      simpa only [totSteps, totCyc, Nat.add_assoc] using h
    have hcapTails_le : (capFrontierTails (tdNode trapdoor) positions).length ≤ 171 := by
      rw [capFrontierTails_length]; exact cap_frontier_le_171 positions
    have htotTails_le : (allRecTails ++ capFrontierTails (tdNode trapdoor) positions).length ≤ 9 * positions.card + 171 := by
      simp only [List.length_append]; omega
    have hpack_len : (pack6Bits (allRecTails ++ capFrontierTails (tdNode trapdoor) positions)).length ≤
        (6 * (9 * positions.card + 171) + 7) / 8 := by
      rw [pack6Bits_length]; exact Nat.div_le_div_right (by omega)
    have hphi_mid := cphi8_le_phi8 rMid
    have hwbuf_end := wbuf_sub_cphi8_le rEnd
    have hfuel : totSteps + 1 ≤ openSub.steps .opening := by
      rw [hsteps]
      have : rEnd.val < 8 := rEnd.isLt
      omega
    have hexec := OpenRuns.halt (haltIdx := 7429) (totalFuel := openSub.steps .opening)
      hrunAll (by decide) rfl hpcH hx5H hx10H hfuel
    refine ⟨{ exit := .success, state := sHalt, cycles := totCyc + 1, oracleCalls := 0 }, hexec, rfl, rfl,
      ?_, ?_, ?_⟩
    · rw [hx11H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [href_eq, List.length_append, pack6BitsRev_length, pack6Bits_length]
    · intro hcl; rw [href_eq]; exact hprefH hcl
    · intro hbatch
      have h128 : positions.card = 128 := hbatch
      have hpack993 : (pack6Bits (allRecTails ++ capFrontierTails (tdNode trapdoor) positions)).length ≤ 993 := by
        rw [h128] at hpack_len; omega
      have hte := htailEpi_le hpack993
      rw [h128] at hrecAmort hrecTails_le htotTails_le
      dsimp only [totCyc]; omega

end CommitGolfCandidate.MoonOpen
