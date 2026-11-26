import CommitGolfCandidate.MoonOpenEntry

/-! Lazy slow-table initialization (`168` cycles once), `slow_mid` (`5,592,064 ≤ g < 5,592,384`),
`slow_tail` (`5,592,384 ≤ g ≤ 5,592,405`), and exact potential-amortized cycle bounds (`phi8`). -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Record-Loop Potential Function & Slow-Table Initialization (`4488..4658`) -/

/-- Scaled (`× 8`) residue potential `8 * Φ_rec(r)` proving `C_nf + Φ(r') - Φ(r) ≤ 431.625`. -/
def phi8 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => 0 | 1 => 289 | 2 => 298 | 3 => 139 | 4 => 148 | 5 => 445 | 6 => 158 | _ => 295

def slowEntryCyc (r : Fin 8) : Nat :=
  11 + (dwordsCode r 3 .x10 0 0 false (r.val == 4)).length + 7 + 1 + (if r.val == 4 then 6 else 3)

private theorem lui_ofNat_neg (k : Nat) (hk1 : 524288 ≤ k) (hk2 : k < 1048576) :
    ((BitVec.ofNat 20 k).zeroExtend 32 <<< 12).signExtend 64 =
      BitVec.ofNat 64 (2 ^ 64 - 4096 * (1048576 - k)) := by
  have hsh : (BitVec.ofNat 20 k).zeroExtend 32 <<< 12 = BitVec.ofNat 32 (4096 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, show (2 : Nat) ^ 12 = 4096 by decide,
      Nat.mod_eq_of_lt (by omega : k < 2 ^ 20), Nat.mod_eq_of_lt (by omega : k < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32)]
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32)]
  rw [hsh]
  have hmsb : (BitVec.ofNat 32 (4096 * k)).msb = true := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32), decide_eq_true_eq]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [hmsb, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 4096 * (1048576 - k) < 2 ^ 64)]
  omega

private def auipcAddiOk (pc tgt hi20 lo12 : Nat) : Bool :=
  hi20 < 1048576 && lo12 < 4096 &&
  (let hiS : Int := if hi20 < 524288 then (4096 * hi20 : Nat) else -((4096 * (1048576 - hi20) : Nat) : Int)
   let loS : Int := if lo12 < 2048 then (lo12 : Nat) else -((4096 - lo12 : Nat) : Int)
   ((0x1000 + 4 * pc : Nat) : Int) + hiS + loS == ((0x1000 + 4 * tgt : Nat) : Int))

private theorem pcAt_auipc_addi_of_ok (pc tgt hi20 lo12 : Nat) (h : auipcAddiOk pc tgt hi20 lo12 = true) :
    (pcAt pc + ((BitVec.ofNat 20 hi20).zeroExtend 32 <<< 12).signExtend 64) +
      signExtend12 (BitVec.ofNat 12 lo12) = pcAt tgt := by
  unfold auipcAddiOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with ⟨⟨hhi, hlo⟩, heq⟩
  unfold pcAt
  by_cases h1 : hi20 < 524288 <;> by_cases h2 : lo12 < 2048
  · rw [if_pos h1, if_pos h2] at heq
    rw [lui_ofNat_nonneg hi20 h1, signExtend12_nonneg lo12 h2, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1; omega
  · rw [if_pos h1, if_neg h2] at heq
    have hse : signExtend12 (BitVec.ofNat 12 lo12) = BitVec.ofNat 64 (2 ^ 64 - (4096 - lo12)) := by
      simpa only [show 4096 - (4096 - lo12) = lo12 by omega] using signExtend12_neg (4096 - lo12) (by omega) (by omega)
    rw [lui_ofNat_nonneg hi20 h1, hse, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
    have hsum : 0x1000 + 4 * pc + 4096 * hi20 + (2 ^ 64 - (4096 - lo12)) = (0x1000 + 4 * tgt) + 2 ^ 64 := by omega
    rw [hsum, Nat.add_mod_right]
  · rw [if_neg h1, if_pos h2] at heq
    rw [lui_ofNat_neg hi20 (by omega) hhi, signExtend12_nonneg lo12 h2, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
    have hsum : 0x1000 + 4 * pc + (2 ^ 64 - 4096 * (1048576 - hi20)) + lo12 = (0x1000 + 4 * tgt) + 2 ^ 64 := by omega
    rw [hsum, Nat.add_mod_right]
  · rw [if_neg h1, if_neg h2] at heq
    have hse : signExtend12 (BitVec.ofNat 12 lo12) = BitVec.ofNat 64 (2 ^ 64 - (4096 - lo12)) := by
      simpa only [show 4096 - (4096 - lo12) = lo12 by omega] using signExtend12_neg (4096 - lo12) (by omega) (by omega)
    rw [lui_ofNat_neg hi20 (by omega) hhi, hse, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
    have hsum : 0x1000 + 4 * pc + (2 ^ 64 - 4096 * (1048576 - hi20)) + (2 ^ 64 - (4096 - lo12)) =
        (0x1000 + 4 * tgt) + 2 * 2 ^ 64 := by omega
    rw [hsum, Nat.add_mul_mod_self_right]

/-- Exact `(hi20, lo12, tgtPc)` triples for the 56 slow-table init entries (`PC 4490..4657`). -/
private def slowTblTriples : List (Nat × Nat × Nat) :=
  [(1, 3008, 5242), (1, 3044, 5254), (1, 3124, 5277), (1, 3204, 5300),
   (1, 3284, 5323), (1, 3352, 5343), (1, 3440, 5368), (1, 3528, 5393),
   (1, 2256, 5078), (1, 2284, 5088), (1, 2356, 5109), (1, 2432, 5131),
   (1, 2512, 5154), (1, 2576, 5173), (1, 2656, 5196), (1, 2736, 5219),
   (0, 1520, 4918), (0, 1548, 4928), (0, 1624, 4950), (0, 1700, 4972),
   (0, 1776, 4994), (0, 1836, 5012), (0, 1912, 5034), (0, 1988, 5056),
   (1048572, 2468, 59), (1048574, 1084, 2788), (1048573, 2624, 1128), (1048575, 1460, 3912),
   (1048574, 2968, 2244), (1048572, 332, 564), (1048575, 3316, 3361), (1048573, 616, 1665),
   (1, 3328, 5418), (1, 3420, 5444), (1, 3656, 5506), (1, 3892, 5568),
   (1, 32, 5630), (1, 220, 5680), (1, 456, 5742), (1, 692, 5804),
   (1, 928, 5866), (1, 1172, 5930), (1, 1480, 6010), (1, 1724, 6074),
   (1, 2032, 6154), (2, 2276, 6218), (2, 2584, 6298), (2, 2828, 6362),
   (2, 3136, 6442), (2, 3272, 6479), (2, 3452, 6527), (2, 3632, 6575),
   (2, 3760, 6610), (2, 3920, 6653), (2, 4, 6701), (2, 184, 6749)]

private def slowTblCodeAt (k : Nat) : List Instruction :=
  let e := slowTblTriples.getD k (0, 0, 0)
  [.base (.AUIPC .x5 (BitVec.ofNat 20 e.1)),
   .base (.ADDI .x5 .x5 (BitVec.ofNat 12 e.2.1)),
   .base (.SD .x0 .x5 (BitVec.ofNat 12 (1344 + 8 * k)))]

private theorem slowTbl_arith_ok (k : Fin 56) :
    let e := slowTblTriples.getD k.val (0, 0, 0)
    auipcAddiOk (4490 + 3 * k.val) e.2.2 e.1 e.2.1 = true := by
  revert k; decide

private theorem slowTbl_targets_ok (r : Fin 8) :
    (slowTblTriples.getD r.val (0, 0, 0)).2.2 = pcCopy29 r ∧
    (slowTblTriples.getD (8 + r.val) (0, 0, 0)).2.2 = pcCopy30 r ∧
    (slowTblTriples.getD (16 + r.val) (0, 0, 0)).2.2 = pcCopy32 r ∧
    (slowTblTriples.getD (24 + r.val) (0, 0, 0)).2.2 = pcRec r ∧
    (slowTblTriples.getD (32 + r.val) (0, 0, 0)).2.2 = pcCopy32x3 r ∧
    (slowTblTriples.getD (40 + r.val) (0, 0, 0)).2.2 = pcCopy30x4 r ∧
    (slowTblTriples.getD (48 + r.val) (0, 0, 0)).2.2 = pcCopy29x2 r := by
  fin_cases r <;> decide

private theorem slowTbl_codeAt_one (k : Nat) (hk : k < 56) :
    CodeAt (4490 + 3 * k) (slowTblCodeAt k) := by
  interval_cases k <;> exact codeAt_of_list_eq _ _ (by decide) rfl

private theorem openRuns_init_slow_tables_loop :
    ∀ k (hk : k ≤ 56) (s : MachineState),
      s.pc = pcAt (4490 + 3 * k) →
      (∀ m < k, s.getMem (BitVec.ofNat 64 (1344 + 8 * m)) = pcAt (slowTblTriples.getD m (0, 0, 0)).2.2) →
      ∃ s' : MachineState,
        OpenRuns s (3 * (56 - k)) (3 * (56 - k)) s' ∧
        s'.pc = pcAt PC_slow_tbl_ready ∧
        RegsEqExcept [.x5] s s' ∧
        (∀ a : Word, ¬ (1344 ≤ a.toNat ∧ a.toNat < 1792) → s'.getMem a = s.getMem a) ∧
        (∀ m < 56, s'.getMem (BitVec.ofNat 64 (1344 + 8 * m)) = pcAt (slowTblTriples.getD m (0, 0, 0)).2.2) := by
  intro k hk
  generalize hrem : 56 - k = rem
  induction rem generalizing k with
  | zero =>
    intro s hpc hdone
    have hkeq : k = 56 := by omega
    subst hkeq
    exact ⟨s, OpenRuns.refl s, hpc, fun _ _ => rfl, fun _ _ => rfl, hdone⟩
  | succ rem ih =>
    intro s hpc hdone
    have hklt : k < 56 := by omega
    have hcode := slowTbl_codeAt_one k hklt
    set e := slowTblTriples.getD k (0, 0, 0)
    have hi0 : openInstr (4490 + 3 * k) = .base (.AUIPC .x5 (BitVec.ofNat 20 e.1)) := by
      have h := hcode.2 0 (by simp [slowTblCodeAt]); simpa [slowTblCodeAt, e] using h
    have hi1 : openInstr (4490 + 3 * k + 1) = .base (.ADDI .x5 .x5 (BitVec.ofNat 12 e.2.1)) := by
      have h := hcode.2 1 (by simp [slowTblCodeAt]); simpa [slowTblCodeAt, e] using h
    have hi2 : openInstr (4490 + 3 * k + 2) = .base (.SD .x0 .x5 (BitVec.ofNat 12 (1344 + 8 * k))) := by
      have h := hcode.2 2 (by simp [slowTblCodeAt]); simpa [slowTblCodeAt, e] using h
    have hbd : 4490 + 3 * k + 3 ≤ OPEN_CODE_LEN := by unfold OPEN_CODE_LEN; omega
    have hs1 := step_AUIPC (s := s) (by omega) hpc hi0
    set s1 := (s.setReg .x5 (pcAt (4490 + 3 * k) + ((BitVec.ofNat 20 e.1).zeroExtend 32 <<< 12).signExtend 64)).setPC (pcAt (4490 + 3 * k + 1))
    have hs2 := step_ADDI (s := s1) (by omega) rfl hi1
    set s2 := (s1.setReg .x5 (s1.getReg .x5 + signExtend12 (BitVec.ofNat 12 e.2.1))).setPC (pcAt (4490 + 3 * k + 1 + 1))
    have hsd_addr : s2.getReg .x0 + signExtend12 (BitVec.ofNat 12 (1344 + 8 * k)) = BitVec.ofNat 64 (1344 + 8 * k) := by
      rw [show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (1344 + 8 * k) (by omega), BitVec.zero_add]
    have hsd_val : accessValid (s2.getReg .x0 + signExtend12 (BitVec.ofNat 12 (1344 + 8 * k))) 8 = true := by
      rw [hsd_addr]; exact accessValid_ofNat (1344 + 8 * k) 8 (by omega) (by omega)
    have hs3 := step_SD (s := s2) (by omega) (by congr 1) hi2 hsd_val
    set s3 := (s2.setMem (s2.getReg .x0 + signExtend12 (BitVec.ofNat 12 (1344 + 8 * k))) (s2.getReg .x5)).setPC (pcAt (4490 + 3 * k + 2 + 1))
    have hs2_x5 : s2.getReg .x5 = pcAt e.2.2 := by
      simp only [s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true]
      exact pcAt_auipc_addi_of_ok (4490 + 3 * k) e.2.2 e.1 e.2.1 (slowTbl_arith_ok ⟨k, hklt⟩)
    have hpc3 : s3.pc = pcAt (4490 + 3 * (k + 1)) := by dsimp only [s3, MachineState.setPC]; congr 1
    have hdone3 : ∀ m < k + 1, s3.getMem (BitVec.ofNat 64 (1344 + 8 * m)) = pcAt (slowTblTriples.getD m (0, 0, 0)).2.2 := by
      intro m hm
      by_cases hmk : m = k
      · subst hmk; simp [s3, hsd_addr, hs2_x5, e]
      · have hne : BitVec.ofNat 64 (1344 + 8 * m) ≠ BitVec.ofNat 64 (1344 + 8 * k) := by
          intro h; have hn := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1344 + 8 * m < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 1344 + 8 * k < 2 ^ 64)] at hn; omega
        simp only [s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsd_addr]
        rw [MachineState.getMem_setMem_ne hne]; exact hdone m (by omega)
    obtain ⟨s', hrest, hpc', hreg', hmem', hdone'⟩ := ih (k + 1) (by omega) (by omega) s3 hpc3 hdone3
    refine ⟨s', ?_, hpc', ?_, ?_, hdone'⟩
    · have hrun := ((hs1.trans hs2).trans hs3).trans hrest
      simpa only [show 1 + 1 + 1 + 3 * rem = 3 * (rem + 1) by omega] using hrun
    · intro reg hreg
      have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
      exact (hreg' reg hreg).trans (by simp [s3, s2, s1, getReg_setReg_ne' .x5 reg hne5.symm])
    · intro a ha
      rw [hmem' a ha]
      simp only [s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsd_addr]
      exact MachineState.getMem_setMem_ne (by
        intro h; apply ha; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)

/-- Lazy table-init header at `PC_slow_body = 4488 → PC_slow_tbl_ready = 4658`:
`2` cycles when already initialized, `170 = 2 + 168` cycles on the first slow record. -/
theorem openRuns_slow_tbl_guard {s : MachineState} {tblInit : Bool}
    (hpc : s.pc = pcAt PC_slow_body)
    (htbl : SlowTablesState s tblInit) :
    let cyc := 2 + if tblInit then 0 else 168
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt PC_slow_tbl_ready ∧
      RegsEqExcept [.x5] s s' ∧
      (∀ a : Word, ¬ (1344 ≤ a.toNat ∧ a.toNat < 1792) → s'.getMem a = s.getMem a) ∧
      SlowTablesState s' true := by
  have hld_addr : s.getReg .x0 + signExtend12 (1344#12) = BitVec.ofNat 64 1344 := by
    rw [show s.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1344 (by omega), BitVec.zero_add]
  have hld_val : accessValid (s.getReg .x0 + signExtend12 (1344#12)) 8 = true := by
    rw [hld_addr]; exact accessValid_ofNat 1344 8 (by omega) (by omega)
  have h0 := step_LD (s := s) (by decide) hpc (rfl : openInstr 4488 = .base (.LD .x5 .x0 (1344#12))) hld_val
  set s1 := (s.setReg .x5 (s.getMem (s.getReg .x0 + signExtend12 (1344#12)))).setPC (pcAt 4489)
  cases tblInit with
  | true =>
    unfold SlowTablesState at htbl; simp only [↓reduceIte] at htbl
    have hx5_ne : s1.getReg .x5 ≠ s1.getReg .x0 := by
      have h0r := (htbl (0 : Fin 8)).1
      simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at h0r
      rw [show s1.getReg .x0 = 0#64 from rfl]
      simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        hld_addr, h0r]
      have hpc0 : pcCopy29 (0 : Fin 8) = 5242 := rfl
      rw [hpc0]; decide
    have hbr : pcAt 4489 + signExtend13 (676#13) = pcAt PC_slow_tbl_ready := by
      simpa only [show 4 * (PC_slow_tbl_ready - 4489) = 676 by decide] using pcAt_add_pos13 4489 PC_slow_tbl_ready (by decide) (by decide)
    have h1 := step_BNE_taken (s := s1) (by decide) rfl (rfl : openInstr 4489 = .base (.BNE .x5 .x0 (676#13))) hx5_ne hbr
    set s2 := s1.setPC (pcAt PC_slow_tbl_ready)
    refine ⟨s2, h0.trans h1, rfl, ?_, fun _ _ => by simp [s2, s1], ?_⟩
    · intro reg hreg; have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
      simp [s2, s1, getReg_setReg_ne' .x5 reg hne5.symm]
    · unfold SlowTablesState; simp only [↓reduceIte]; intro r; simpa [s2, s1] using htbl r
  | false =>
    unfold SlowTablesState at htbl; simp only [Bool.false_eq_true, ↓reduceIte] at htbl
    have hx5_eq : s1.getReg .x5 = s1.getReg .x0 := by
      rw [show s1.getReg .x0 = 0#64 from rfl]
      simp [s1, hld_addr, htbl]
    have h1 := step_BNE_not_taken (s := s1) (by decide) rfl (rfl : openInstr 4489 = .base (.BNE .x5 .x0 (676#13))) hx5_eq
    set s2 := s1.setPC (pcAt 4490)
    obtain ⟨s', hloop, hpc', hreg', hmem', hdone'⟩ := openRuns_init_slow_tables_loop 0 (by omega) s2 rfl (fun _ hm => by omega)
    refine ⟨s', (h0.trans h1).trans hloop, hpc', ?_, ?_, ?_⟩
    · intro reg hreg; have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
      exact (hreg' reg hreg).trans (by simp [s2, s1, getReg_setReg_ne' .x5 reg hne5.symm])
    · intro a ha; exact (hmem' a ha).trans (by simp [s2, s1])
    · unfold SlowTablesState; simp only [↓reduceIte]
      intro r; have hr := r.isLt; have ht := slowTbl_targets_ok r
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [ht.1] using hdone' r.val (by omega)
      · simpa only [ht.2.1, show 1344 + 8 * (8 + r.val) = 1408 + 8 * r.val by omega] using hdone' (8 + r.val) (by omega)
      · simpa only [ht.2.2.1, show 1344 + 8 * (16 + r.val) = 1472 + 8 * r.val by omega] using hdone' (16 + r.val) (by omega)
      · simpa only [ht.2.2.2.1, show 1344 + 8 * (24 + r.val) = 1536 + 8 * r.val by omega] using hdone' (24 + r.val) (by omega)
      · simpa only [ht.2.2.2.2.1, show 1344 + 8 * (32 + r.val) = 1600 + 8 * r.val by omega] using hdone' (32 + r.val) (by omega)
      · simpa only [ht.2.2.2.2.2.1, show 1344 + 8 * (40 + r.val) = 1664 + 8 * r.val by omega] using hdone' (40 + r.val) (by omega)
      · simpa only [ht.2.2.2.2.2.2, show 1344 + 8 * (48 + r.val) = 1728 + 8 * r.val by omega] using hdone' (48 + r.val) (by omega)

/-! ### 2. Slow-Path Address & Tail Helpers -/

/-- In-place binary-level sibling address using a cached `baseReg` (`5` cycles, no scratch reg!). -/
def lvlAddrInRegCode (dstReg baseReg : Reg) : List Instruction :=
  [.base (.XORI dstReg .x22 (1#12)),
   .base (.SRLI .x22 .x22 (1#6)),
   .base (.ADD dstReg dstReg .x22),
   .base (.SLLI dstReg dstReg (5#6)),
   .base (.ADD dstReg baseReg dstReg)]

/-- In-place binary-level sibling address reading `base(l)` into `.x5` from `[8*l]` (`6` cycles). -/
def lvlAddrInMemCode (dstReg : Reg) (l : Nat) : List Instruction :=
  [.base (.XORI dstReg .x22 (1#12)),
   .base (.SRLI .x22 .x22 (1#6)),
   .base (.ADD dstReg dstReg .x22),
   .base (.SLLI dstReg dstReg (5#6)),
   .base (.LD .x5 .x0 (BitVec.ofNat 12 (8 * l))),
   .base (.ADD dstReg .x5 dstReg)]

theorem openRuns_lvl_addr_inreg {s : MachineState} {pc l idx : Nat} {dstReg baseReg : Reg}
    (hcode : CodeAt pc (lvlAddrInRegCode dstReg baseReg))
    (hpc : s.pc = pcAt pc) (hl1 : 1 ≤ l) (hidx : idx < 16777216)
    (hdst_ne : dstReg ≠ .x0 ∧ dstReg ≠ .x22 ∧ dstReg ≠ baseReg)
    (hbase_ne : baseReg ≠ .x22)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hbase : s.getReg baseReg = BitVec.ofNat 64 (4294971424 + levelBase l)) :
    ∃ s' : MachineState,
      OpenRuns s 5 5 s' ∧
      s'.pc = pcAt (pc + 5) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      s'.getReg dstReg = BitVec.ofNat 64 (4294971424 + levelBase l + nodeOffset l (idx ^^^ 1)) ∧
      RegsEqExcept [.x22, dstReg] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hbd : pc + 5 ≤ OPEN_CODE_LEN := by have := hcode.1; simpa [lvlAddrInRegCode] using this
  have hi0 : openInstr pc = .base (.XORI dstReg .x22 (1#12)) := by have h := hcode.2 0 (by simp [lvlAddrInRegCode]); simpa [lvlAddrInRegCode] using h
  have hi1 : openInstr (pc + 1) = .base (.SRLI .x22 .x22 (1#6)) := by have h := hcode.2 1 (by simp [lvlAddrInRegCode]); simpa [lvlAddrInRegCode] using h
  have hi2 : openInstr (pc + 2) = .base (.ADD dstReg dstReg .x22) := by have h := hcode.2 2 (by simp [lvlAddrInRegCode]); simpa [lvlAddrInRegCode] using h
  have hi3 : openInstr (pc + 3) = .base (.SLLI dstReg dstReg (5#6)) := by have h := hcode.2 3 (by simp [lvlAddrInRegCode]); simpa [lvlAddrInRegCode] using h
  have hi4 : openInstr (pc + 4) = .base (.ADD dstReg baseReg dstReg) := by have h := hcode.2 4 (by simp [lvlAddrInRegCode]); simpa [lvlAddrInRegCode] using h
  have hs0 := step_XORI (s := s) (by omega) hpc hi0
  set s1 := (s.setReg dstReg (s.getReg .x22 ^^^ signExtend12 (1#12))).setPC (pcAt (pc + 1))
  have hs1 := step_SRLI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x22 (s1.getReg .x22 >>> (1#6).toNat)).setPC (pcAt (pc + 1 + 1))
  have hs2 := step_ADD (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg dstReg (s2.getReg dstReg + s2.getReg .x22)).setPC (pcAt (pc + 2 + 1))
  have hs3 := step_SLLI (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg dstReg (s3.getReg dstReg <<< (5#6).toNat)).setPC (pcAt (pc + 3 + 1))
  have hs4 := step_ADD (s := s4) (by omega) (by congr 1) hi4
  set s5 := (s4.setReg dstReg (s4.getReg baseReg + s4.getReg dstReg)).setPC (pcAt (pc + 4 + 1))
  have hd1 : s1.getReg dstReg = BitVec.ofNat 64 (idx ^^^ 1) := by
    simp [s1, MachineState.getReg_setReg_eq hdst_ne.1, hx22, bv64_xor1 idx (by omega)]
  have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 (idx / 2) := by
    simp only [s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      getReg_setReg_ne' dstReg .x22 hdst_ne.2.1, hx22, show (1#6 : BitVec 6).toNat = 1 from rfl,
      bv64_ushr idx 1 (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hd4 : s4.getReg dstReg = BitVec.ofNat 64 (nodeOffset l (idx ^^^ 1)) := by
    have hd2 : s2.getReg dstReg = BitVec.ofNat 64 (idx ^^^ 1) := by
      simp [s2, getReg_setReg_ne' .x22 dstReg hdst_ne.2.1.symm, hd1]
    have hd3 : s3.getReg dstReg = BitVec.ofNat 64 ((idx ^^^ 1) + idx / 2) := by
      simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hdst_ne.1,
        hd2, hx22_2, ← BitVec.ofNat_add]
    simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hdst_ne.1,
      hd3, bv64_shl, show (5#6 : BitVec 6).toNat = 5 from rfl, nodeOffset_bin l idx hl1]
    congr 1; omega
  have hb4 : s4.getReg baseReg = BitVec.ofNat 64 (4294971424 + levelBase l) := by
    simp [s4, s3, s2, s1, getReg_setReg_ne' dstReg baseReg hdst_ne.2.2,
      getReg_setReg_ne' .x22 baseReg hbase_ne.symm, hbase]
  refine ⟨s5, (((hs0.trans hs1).trans hs2).trans hs3).trans hs4, by congr 1, ?_, ?_, ?_, fun _ => by simp [s5, s4, s3, s2, s1]⟩
  · simp [s5, s4, s3, getReg_setReg_ne' dstReg .x22 hdst_ne.2.1, hx22_2]
  · simp [s5, MachineState.getReg_setReg_eq hdst_ne.1, hb4, hd4, ← BitVec.ofNat_add]
  · intro reg hreg
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have hd' : reg ≠ dstReg := fun h => hreg (by simp [h])
    simp [s5, s4, s3, s2, s1, getReg_setReg_ne' dstReg reg hd'.symm, getReg_setReg_ne' .x22 reg h22'.symm]

theorem openRuns_lvl_addr_inmem {s : MachineState} {pc l idx : Nat} {dstReg : Reg}
    (hcode : CodeAt pc (lvlAddrInMemCode dstReg l))
    (hpc : s.pc = pcAt pc) (hl1 : 1 ≤ l) (hl23 : l ≤ 23) (hidx : idx < 16777216)
    (hdst_ne : dstReg ≠ .x0 ∧ dstReg ≠ .x5 ∧ dstReg ≠ .x22)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hbt : BaseTableReady s) :
    ∃ s' : MachineState,
      OpenRuns s 6 6 s' ∧
      s'.pc = pcAt (pc + 6) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      s'.getReg dstReg = BitVec.ofNat 64 (4294971424 + levelBase l + nodeOffset l (idx ^^^ 1)) ∧
      RegsEqExcept [.x5, .x22, dstReg] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hbd : pc + 6 ≤ OPEN_CODE_LEN := by have := hcode.1; simpa [lvlAddrInMemCode] using this
  have hi0 : openInstr pc = .base (.XORI dstReg .x22 (1#12)) := by have h := hcode.2 0 (by simp [lvlAddrInMemCode]); simpa [lvlAddrInMemCode] using h
  have hi1 : openInstr (pc + 1) = .base (.SRLI .x22 .x22 (1#6)) := by have h := hcode.2 1 (by simp [lvlAddrInMemCode]); simpa [lvlAddrInMemCode] using h
  have hi2 : openInstr (pc + 2) = .base (.ADD dstReg dstReg .x22) := by have h := hcode.2 2 (by simp [lvlAddrInMemCode]); simpa [lvlAddrInMemCode] using h
  have hi3 : openInstr (pc + 3) = .base (.SLLI dstReg dstReg (5#6)) := by have h := hcode.2 3 (by simp [lvlAddrInMemCode]); simpa [lvlAddrInMemCode] using h
  have hi4 : openInstr (pc + 4) = .base (.LD .x5 .x0 (BitVec.ofNat 12 (8 * l))) := by have h := hcode.2 4 (by simp [lvlAddrInMemCode]); simpa [lvlAddrInMemCode] using h
  have hi5 : openInstr (pc + 5) = .base (.ADD dstReg .x5 dstReg) := by have h := hcode.2 5 (by simp [lvlAddrInMemCode]); simpa [lvlAddrInMemCode] using h
  have hs0 := step_XORI (s := s) (by omega) hpc hi0
  set s1 := (s.setReg dstReg (s.getReg .x22 ^^^ signExtend12 (1#12))).setPC (pcAt (pc + 1))
  have hs1 := step_SRLI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x22 (s1.getReg .x22 >>> (1#6).toNat)).setPC (pcAt (pc + 1 + 1))
  have hs2 := step_ADD (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg dstReg (s2.getReg dstReg + s2.getReg .x22)).setPC (pcAt (pc + 2 + 1))
  have hs3 := step_SLLI (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg dstReg (s3.getReg dstReg <<< (5#6).toNat)).setPC (pcAt (pc + 3 + 1))
  have hld_val : accessValid (s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * l))) 8 = true := by
    rw [show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * l) (by omega), BitVec.zero_add]
    exact accessValid_ofNat (8 * l) 8 (by omega) (by omega)
  have hs4 := step_LD (s := s4) (by omega) (by congr 1) hi4 hld_val
  set s5 := (s4.setReg .x5 (s4.getMem (s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * l))))).setPC (pcAt (pc + 4 + 1))
  have hs5 := step_ADD (s := s5) (by omega) (by congr 1) hi5
  set s6 := (s5.setReg dstReg (s5.getReg .x5 + s5.getReg dstReg)).setPC (pcAt (pc + 5 + 1))
  have hd1 : s1.getReg dstReg = BitVec.ofNat 64 (idx ^^^ 1) := by
    simp [s1, MachineState.getReg_setReg_eq hdst_ne.1, hx22, bv64_xor1 idx (by omega)]
  have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 (idx / 2) := by
    simp only [s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      getReg_setReg_ne' dstReg .x22 hdst_ne.2.2, hx22, show (1#6 : BitVec 6).toNat = 1 from rfl,
      bv64_ushr idx 1 (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hd4 : s4.getReg dstReg = BitVec.ofNat 64 (nodeOffset l (idx ^^^ 1)) := by
    have hd2 : s2.getReg dstReg = BitVec.ofNat 64 (idx ^^^ 1) := by
      simp [s2, getReg_setReg_ne' .x22 dstReg hdst_ne.2.2.symm, hd1]
    have hd3 : s3.getReg dstReg = BitVec.ofNat 64 ((idx ^^^ 1) + idx / 2) := by
      simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hdst_ne.1,
        hd2, hx22_2, ← BitVec.ofNat_add]
    simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hdst_ne.1,
      hd3, bv64_shl, show (5#6 : BitVec 6).toNat = 5 from rfl, nodeOffset_bin l idx hl1]
    congr 1; omega
  have hx5_5 : s5.getReg .x5 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
    simp only [s5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * l) (by omega), BitVec.zero_add,
      show ∀ a, s4.getMem a = s.getMem a from fun a => by simp [s4, s3, s2, s1], hbt.lvlBase l hl1 hl23]
  refine ⟨s6, ((((hs0.trans hs1).trans hs2).trans hs3).trans hs4).trans hs5, by congr 1, ?_, ?_, ?_, fun _ => by simp [s6, s5, s4, s3, s2, s1]⟩
  · simp [s6, s5, s4, s3, getReg_setReg_ne' dstReg .x22 hdst_ne.2.2, getReg_setReg_ne', hx22_2]
  · simp [s6, MachineState.getReg_setReg_eq hdst_ne.1, hx5_5,
      show s5.getReg dstReg = s4.getReg dstReg by simp [s5, getReg_setReg_ne' .x5 dstReg hdst_ne.2.1.symm],
      hd4, ← BitVec.ofNat_add]
  · intro reg hreg
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have hd' : reg ≠ dstReg := fun h => hreg (by simp [h])
    simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne' dstReg reg hd'.symm,
      getReg_setReg_ne' .x5 reg h5'.symm, getReg_setReg_ne' .x22 reg h22'.symm]

/-- Combine `x8 = bitsOf6 ts0` with `x5 = bitsOf6 ts1` via `SLLI x5 x5 (6*ts0.length); OR x8 x8 x5` (`2` cycles). -/
theorem openRuns_combine_tails {clean : Prop} {s : MachineState} {pc : Nat}
    {ts0 ts1 : List (BitVec 6)}
    (hlen : 6 * (ts0.length + ts1.length) ≤ 64)
    (hi0 : openInstr pc = .base (.SLLI .x5 .x5 (BitVec.ofNat 6 (6 * ts0.length))))
    (hi1 : openInstr (pc + 1) = .base (.OR .x8 .x8 .x5))
    (hbd : pc + 2 ≤ OPEN_CODE_LEN)
    (hpc : s.pc = pcAt pc)
    (hx8 : clean → s.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts0))
    (hx5 : clean → s.getReg .x5 = BitVec.ofNat 64 (bitsOf6 ts1)) :
    ∃ s' : MachineState,
      OpenRuns s 2 2 s' ∧
      s'.pc = pcAt (pc + 2) ∧
      (clean → s'.getReg .x8 = BitVec.ofNat 64 (bitsOf6 (ts0 ++ ts1))) ∧
      RegsEqExcept [.x5, .x8] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hs0 := step_SLLI (s := s) (by omega) hpc hi0
  set s1 := (s.setReg .x5 (s.getReg .x5 <<< (BitVec.ofNat 6 (6 * ts0.length)).toNat)).setPC (pcAt (pc + 1))
  have hs1 := step_OR (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x8 (s1.getReg .x8 ||| s1.getReg .x5)).setPC (pcAt (pc + 1 + 1))
  refine ⟨s2, hs0.trans hs1, by congr 1, fun hcl => ?_, ?_, fun _ => by simp [s2, s1]⟩
  · have hsh : (BitVec.ofNat 6 (6 * ts0.length)).toNat = 6 * ts0.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlt0 : bitsOf6 ts0 < 2 ^ (6 * ts0.length) := bitsOf6_lt ts0
    have hlt1 : bitsOf6 ts1 < 2 ^ (6 * ts1.length) := bitsOf6_lt ts1
    have hlt1_64 : bitsOf6 ts1 < 2 ^ 64 := by
      have : 2 ^ (6 * ts1.length) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega); omega
    have hlt_tot : bitsOf6 (ts0 ++ ts1) < 2 ^ 64 := by
      have h1 := bitsOf6_lt (ts0 ++ ts1)
      have h2 : 2 ^ (6 * (ts0 ++ ts1).length) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by simp; omega)
      omega
    have hsum : bitsOf6 ts0 + bitsOf6 ts1 * 2 ^ (6 * ts0.length) = bitsOf6 (ts0 ++ ts1) := by
      rw [bitsOf6_append]; ring
    simp only [s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      getReg_setReg_ne', hx8 hcl, hx5 hcl, hsh]
    apply BitVec.eq_of_toNat_eq
    rw [word_or_shl_add_low64 (bitsOf6 ts0) (6 * ts0.length) (bitsOf6 ts1) (by omega) hlt0 hlt1_64,
      hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt_tot]
  · intro reg hreg
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    simp [s2, s1, getReg_setReg_ne' .x8 reg h8'.symm, getReg_setReg_ne' .x5 reg h5'.symm]

/-! ### 3. Unfolding `recordFwd`/`recordTails` for `slow_mid` and `slow_tail` -/

theorem binPathFwd_unfold (nodes : Nat → Nat → Digest) (g : Nat) :
    binPathFwd nodes g =
      (if ((g >>> 1) ^^^ 1) < levelSize 2 then bitsToBytes (nodes 2 ((g >>> 1) ^^^ 1)) 30 else []) ++
      (if ((g >>> 2) ^^^ 1) < levelSize 3 then bitsToBytes (nodes 3 ((g >>> 2) ^^^ 1)) 30 else []) ++
      (if ((g >>> 3) ^^^ 1) < levelSize 4 then bitsToBytes (nodes 4 ((g >>> 3) ^^^ 1)) 30 else []) ++
      (if ((g >>> 4) ^^^ 1) < levelSize 5 then bitsToBytes (nodes 5 ((g >>> 4) ^^^ 1)) 30 else []) ++
      (if ((g >>> 5) ^^^ 1) < levelSize 6 then bitsToBytes (nodes 6 ((g >>> 5) ^^^ 1)) 29 else []) ++
      (if ((g >>> 6) ^^^ 1) < levelSize 7 then bitsToBytes (nodes 7 ((g >>> 6) ^^^ 1)) 29 else []) ++
      (if ((g >>> 7) ^^^ 1) < levelSize 8 then bitsToBytes (nodes 8 ((g >>> 7) ^^^ 1)) 29 else []) ++
      (if ((g >>> 8) ^^^ 1) < levelSize 9 then bitsToBytes (nodes 9 ((g >>> 8) ^^^ 1)) 29 else []) ++
      (if ((g >>> 9) ^^^ 1) < levelSize 10 then bitsToBytes (nodes 10 ((g >>> 9) ^^^ 1)) 29 else []) ++
      (if ((g >>> 10) ^^^ 1) < levelSize 11 then bitsToBytes (nodes 11 ((g >>> 10) ^^^ 1)) 29 else []) ++
      (if ((g >>> 11) ^^^ 1) < levelSize 12 then bitsToBytes (nodes 12 ((g >>> 11) ^^^ 1)) 29 else []) ++
      (if ((g >>> 12) ^^^ 1) < levelSize 13 then bitsToBytes (nodes 13 ((g >>> 12) ^^^ 1)) 29 else []) ++
      (if ((g >>> 13) ^^^ 1) < levelSize 14 then bitsToBytes (nodes 14 ((g >>> 13) ^^^ 1)) 29 else []) := by
  unfold binPathFwd
  rw [show List.range 13 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] by decide]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  rfl

theorem binPathTails_unfold (nodes : Nat → Nat → Digest) (g : Nat) :
    binPathTails nodes g =
      (if ((g >>> 5) ^^^ 1) < levelSize 6 then [tail6 (nodes 6 ((g >>> 5) ^^^ 1))] else []) ++
      (if ((g >>> 6) ^^^ 1) < levelSize 7 then [tail6 (nodes 7 ((g >>> 6) ^^^ 1))] else []) ++
      (if ((g >>> 7) ^^^ 1) < levelSize 8 then [tail6 (nodes 8 ((g >>> 7) ^^^ 1))] else []) ++
      (if ((g >>> 8) ^^^ 1) < levelSize 9 then [tail6 (nodes 9 ((g >>> 8) ^^^ 1))] else []) ++
      (if ((g >>> 9) ^^^ 1) < levelSize 10 then [tail6 (nodes 10 ((g >>> 9) ^^^ 1))] else []) ++
      (if ((g >>> 10) ^^^ 1) < levelSize 11 then [tail6 (nodes 11 ((g >>> 10) ^^^ 1))] else []) ++
      (if ((g >>> 11) ^^^ 1) < levelSize 12 then [tail6 (nodes 12 ((g >>> 11) ^^^ 1))] else []) ++
      (if ((g >>> 12) ^^^ 1) < levelSize 13 then [tail6 (nodes 13 ((g >>> 12) ^^^ 1))] else []) ++
      (if ((g >>> 13) ^^^ 1) < levelSize 14 then [tail6 (nodes 14 ((g >>> 13) ^^^ 1))] else []) := by
  unfold binPathTails
  rw [show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] by decide]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem record_slow_mid_eq (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (i : Index) (hg1 : 5592064 ≤ i.val / 3) (hg2 : i.val / 3 < 5592384) :
    let g := i.val / 3
    let has8 : Bool := decide ((g >>> 7) % 4 < 2)
    recordFwd nodes salts i =
      bitsToBytes (salts i) 24 ++
      bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32 ++
      bitsToBytes (nodes 1 (g ^^^ 1)) 32 ++
      bitsToBytes (nodes 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (nodes 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (nodes 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (nodes 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (nodes 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (nodes 7 ((g >>> 6) ^^^ 1)) 29 ++
      (if has8 then bitsToBytes (nodes 8 ((g >>> 7) ^^^ 1)) 29 else []) ++
      bitsToBytes (nodes 9 ((g >>> 8) ^^^ 1)) 29 ++ bitsToBytes (nodes 11 ((g >>> 10) ^^^ 1)) 29 ++
      bitsToBytes (nodes 13 ((g >>> 12) ^^^ 1)) 29 ∧
    recordTails nodes i =
      [tail6 (nodes 6 ((g >>> 5) ^^^ 1)), tail6 (nodes 7 ((g >>> 6) ^^^ 1))] ++
      (if has8 then [tail6 (nodes 8 ((g >>> 7) ^^^ 1))] else []) ++
      [tail6 (nodes 9 ((g >>> 8) ^^^ 1)), tail6 (nodes 11 ((g >>> 10) ^^^ 1)),
       tail6 (nodes 13 ((g >>> 12) ^^^ 1))] := by
  set g := i.val / 3
  have hsm := level_sib_of_slow_mid g hg1 hg2
  have hl0 : l0SiblingsProof nodes i =
      bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32 := by
    unfold l0SiblingsProof l0Sib1Idx l0Sib2Idx
    rw [if_neg (by omega : g ≠ FULL_TRIPLETS)]
    have hr : i.val % 3 < 3 := Nat.mod_lt _ (by omega)
    generalize i.val % 3 = r at hr
    interval_cases r <;> simp
  have h8iff : (((g >>> 7) ^^^ 1) < levelSize 8) ↔ decide ((g >>> 7) % 4 < 2) = true := by
    rw [decide_eq_true_eq]; exact hsm.2.2.2.2.2.2.2.1
  constructor
  · unfold recordFwd; dsimp only
    rw [show i.val / 3 = g from rfl, hl0, binPathFwd_unfold]
    simp only [hsm.2.1, hsm.2.2.1, hsm.2.2.2.1, hsm.2.2.2.2.1, hsm.2.2.2.2.2.1, hsm.2.2.2.2.2.2.1,
      hsm.2.2.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.2.2.1,
      hsm.2.2.2.2.2.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.2.2.2.2.2,
      ↓reduceIte, List.append_nil, List.nil_append]
    by_cases h8 : ((g >>> 7) ^^^ 1) < levelSize 8
    · rw [if_pos h8, if_pos (h8iff.mp h8)]; simp [List.append_assoc]
    · rw [if_neg h8, if_neg (by intro h; exact h8 (h8iff.mpr h))]; simp [List.append_assoc]
  · unfold recordTails
    rw [show i.val / 3 = g from rfl, binPathTails_unfold]
    simp only [hsm.2.2.2.2.2.1, hsm.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.2.1,
      hsm.2.2.2.2.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.2.2.2.1, hsm.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hsm.2.2.2.2.2.2.2.2.2.2.2.2.2, ↓reduceIte, List.append_nil, List.nil_append]
    by_cases h8 : ((g >>> 7) ^^^ 1) < levelSize 8
    · rw [if_pos h8, if_pos (h8iff.mp h8)]; simp
    · rw [if_neg h8, if_neg (by intro h; exact h8 (h8iff.mpr h))]; simp

theorem record_slow_tail_eq (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (i : Index) (hg1 : 5592384 ≤ i.val / 3) (hg2 : i.val / 3 ≤ 5592405) :
    let g := i.val / 3
    recordFwd nodes salts i =
      bitsToBytes (salts i) 24 ++
      (if g = 5592405 then [] else bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32) ++
      bitsToBytes (nodes 1 (g ^^^ 1)) 32 ++
      (if ((g >>> 1) ^^^ 1) < levelSize 2 then bitsToBytes (nodes 2 ((g >>> 1) ^^^ 1)) 30 else []) ++
      bitsToBytes (nodes 3 ((g >>> 2) ^^^ 1)) 30 ++
      (if ((g >>> 3) ^^^ 1) < levelSize 4 then bitsToBytes (nodes 4 ((g >>> 3) ^^^ 1)) 30 else []) ++
      bitsToBytes (nodes 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (nodes 7 ((g >>> 6) ^^^ 1)) 29 ++ bitsToBytes (nodes 9 ((g >>> 8) ^^^ 1)) 29 ++
      bitsToBytes (nodes 11 ((g >>> 10) ^^^ 1)) 29 ++ bitsToBytes (nodes 13 ((g >>> 12) ^^^ 1)) 29 ∧
    recordTails nodes i =
      [tail6 (nodes 7 ((g >>> 6) ^^^ 1)), tail6 (nodes 9 ((g >>> 8) ^^^ 1)),
       tail6 (nodes 11 ((g >>> 10) ^^^ 1)), tail6 (nodes 13 ((g >>> 12) ^^^ 1))] := by
  set g := i.val / 3
  have hst := level_sib_of_slow_tail g hg1 hg2
  have hl0 : l0SiblingsProof nodes i =
      if g = 5592405 then [] else bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32 := by
    unfold l0SiblingsProof l0Sib1Idx l0Sib2Idx
    rw [full_triplets_eq]
    by_cases heq : g = 5592405
    · rw [if_pos heq, if_pos heq]
    · rw [if_neg heq, if_neg heq]
      have hr : i.val % 3 < 3 := Nat.mod_lt _ (by omega)
      generalize i.val % 3 = r at hr
      interval_cases r <;> simp
  constructor
  · unfold recordFwd; dsimp only
    rw [show i.val / 3 = g from rfl, hl0, binPathFwd_unfold]
    simp only [hst.1, hst.2.1, hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1,
      hst.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.1,
      hst.2.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.2, ↓reduceIte, List.append_nil, List.nil_append, List.append_assoc]
  · unfold recordTails
    rw [show i.val / 3 = g from rfl, binPathTails_unfold]
    simp only [hst.2.2.1, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1,
      hst.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.1,
      hst.2.2.2.2.2.2.2.2.2.2, ↓reduceIte, List.append_nil, List.nil_append, List.singleton_append]
    rfl

/-! ### 4. Amortized Slow-Path Potential Bounds (All 8 Residues Verified by `decide`) -/

def slowMidFullCyc (r : Fin 8) : Nat :=
  let r1 := copy29x2NextR r
  let r2 := copy29x2NextR r1
  slowEntryCyc r + 2 + 2 + 6 + 6 + 2 + (copy32x3SubCode r).length +
    (5 + 6 + 5 + 5) + 2 + (copy30x4SubCode r).length +
    (5 + 5) + 2 + (copy29x2SubCode r).length + 1 + 2 +
    (5 + 5) + 2 + (copy29x2SubCode r1).length + 2 +
    (1 + 5 + 1 + 6 + 1) + 2 + (copy29x2SubCode r2).length + 2 + 5 + 1 + 3 + 5

def slowMidSkip8Cyc (r : Fin 8) : Nat :=
  let r1 := copy29x2NextR r
  let r2 := copy29x2NextR r1
  slowEntryCyc r + 2 + 2 + 6 + 6 + 2 + (copy32x3SubCode r).length +
    (5 + 6 + 5 + 5) + 2 + (copy30x4SubCode r).length +
    (5 + 5) + 2 + (copy29x2SubCode r).length + 1 + 2 +
    (1 + 5 + 1 + 5) + 2 + (copy29x2SubCode r1).length + 2 +
    (1 + 6 + 1) + 2 + (copy29SubCode r2).length + 2 + 5 + 3 + 5

theorem slowMidFull_amort (r : Fin 8) :
    8 * slowMidFullCyc r + phi8 (copy29x2NextR (copy29x2NextR (copy29x2NextR r))) ≤ 3453 + phi8 r := by
  fin_cases r <;> decide

theorem slowMidSkip8_amort (r : Fin 8) :
    8 * slowMidSkip8Cyc r + phi8 (copy29NextR (copy29x2NextR (copy29x2NextR r))) ≤ 3453 + phi8 r := by
  fin_cases r <;> decide

/-- Exact worst-case `slow_tail` cycles parameterized by `(hasL0, hasL2, hasL4 : Bool)` and residue `r`. -/
def slowTailCyc (r : Fin 8) (hasL0 hasL2 hasL4 : Bool) : Nat :=
  let cL0 := if hasL0 then 6 + 2 + (copy32SubCode r).length + 1 + 2 + (copy32SubCode r).length else 0
  let cL1 := 6 + 2 + (copy32SubCode r).length
  let r2 := if hasL2 then copy30NextR r else r
  let cL2 := if hasL2 then 4 + 4 + 2 + (copy30SubCode r).length else 4
  let r3 := copy30NextR r2
  let cL3 := 6 + 2 + (copy30SubCode r2).length
  let r4 := if hasL4 then copy30NextR r3 else r3
  let cL4 := if hasL4 then 4 + 3 + 2 + (copy30SubCode r3).length else 4
  let r5 := copy30NextR r4
  let cL5 := 5 + 2 + (copy30SubCode r4).length
  let r79 := copy29x2NextR r5
  let cTail := (1 + 5 + 1 + 5) + 2 + (copy29x2SubCode r5).length + 1 +
    (1 + 5 + 1 + 6 + 1) + 2 + (copy29x2SubCode r79).length + 2 + 5 + 3 + 6
  slowEntryCyc r + 2 + 2 + 7 + 2 + cL0 + cL1 + cL2 + cL3 + cL4 + cL5 + cTail

def slowTailEndR (r : Fin 8) (hasL2 hasL4 : Bool) : Fin 8 :=
  let r2 := if hasL2 then copy30NextR r else r
  let r3 := copy30NextR r2
  let r4 := if hasL4 then copy30NextR r3 else r3
  let r5 := copy30NextR r4
  copy29x2NextR (copy29x2NextR r5)

theorem slowTail_amort (r : Fin 8) (hasL0 hasL2 hasL4 : Bool) :
    8 * slowTailCyc r hasL0 hasL2 hasL4 + phi8 (slowTailEndR r hasL2 hasL4) ≤ 3453 + phi8 r := by
  fin_cases r <;> cases hasL0 <;> cases hasL2 <;> cases hasL4 <;> decide

end CommitGolfCandidate.MoonOpen
