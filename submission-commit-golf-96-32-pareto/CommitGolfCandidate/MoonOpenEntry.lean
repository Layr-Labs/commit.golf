import CommitGolfCandidate.MoonOpenSubs

/-! Read-only input accessors, low-memory scratch invariants (`BaseTableReady`, `CapMarks15State`,
`SlowTablesState`), empty/non-empty entry execution (`5` / `241` cycles), shared address-computation
sub-blocks, and exact `binPathFwd`/`binPathTails` case-split arithmetic. -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. LUI / AUIPC Constant Helpers & Record PC Table -/

def pcRec (r : Fin 8) : Nat :=
  match r.val with
  | 0 => PC_rec_r0 | 1 => PC_rec_r1 | 2 => PC_rec_r2 | 3 => PC_rec_r3
  | 4 => PC_rec_r4 | 5 => PC_rec_r5 | 6 => PC_rec_r6 | _ => PC_rec_r7

theorem lui_ofNat_nonneg (k : Nat) (hk : k < 524288) :
    ((BitVec.ofNat 20 k).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (4096 * k) := by
  have hsh : (BitVec.ofNat 20 k).zeroExtend 32 <<< 12 = BitVec.ofNat 32 (4096 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.zeroExtend, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, show (2 : Nat) ^ 12 = 4096 by decide,
      Nat.mod_eq_of_lt (by omega : k < 2 ^ 20), Nat.mod_eq_of_lt (by omega : k < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32)]
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32)]
  rw [hsh]
  have hmsb : (BitVec.ofNat 32 (4096 * k)).msb = false := by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32), decide_eq_false_iff_not]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [hmsb, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 4096 * k < 2 ^ 64), Nat.add_zero]

theorem pcAt_auipc_addi (idx tgt hi20 : Nat) (lo12 : BitVec 12)
    (hhi : hi20 < 524288)
    (heq : BitVec.ofNat 64 (0x1000 + 4 * idx + 4096 * hi20) + signExtend12 lo12 = pcAt tgt) :
    (pcAt idx + ((BitVec.ofNat 20 hi20).zeroExtend 32 <<< 12).signExtend 64) + signExtend12 lo12 =
      pcAt tgt := by
  rw [lui_ofNat_nonneg hi20 hhi]
  unfold pcAt at heq ⊢
  rw [← BitVec.ofNat_add]
  exact heq

/-! ### 2. Read-Only Input & Trapdoor Accessors -/

theorem positions_card_le' (positions : Positions) : positions.card ≤ 16777216 := by
  have h : positions.card ≤ LENGTH := by
    simpa only [Index, Fintype.card_fin] using Finset.card_le_univ positions
  have hl : LENGTH = 16777216 := by decide
  omega

theorem levelSize_le_max' (l : Nat) (hl : l ≤ 24) : levelSize l ≤ 16777216 := by
  interval_cases l <;> decide

theorem nodeOffset_align8' (l idx : Nat) : nodeOffset l idx % 8 = 0 := by
  unfold nodeOffset gapOffset; split_ifs <;> omega

theorem levelBase_align8' (l : Nat) (hl : l ≤ 24) : levelBase l % 8 = 0 := by
  interval_cases l <;> decide

theorem saltOff_formula' (i : Index) :
    saltOff i = 1073742952 + 184 * (i.val / 2) + 16 * (i.val % 2) := by
  unfold saltOff PAIR_STRIDE
  rw [rowOff_eq]
  split_ifs <;> omega

theorem saltOff_align8' (i : Index) : saltOff i % 8 = 0 := by
  rw [saltOff_formula']; omega

theorem nodeOffset_lt_treeBytes' (l idx : Nat) (hl : l ≤ 24) (hidx : idx < levelSize l) :
    levelBase l + nodeOffset l idx + 32 ≤ 2617246752 := by
  have hlb := levelBase_bound l hl
  have htb := treeBytes_eq
  by_cases hl0 : l = 0
  · subst hl0; unfold nodeOffset levelBytes at *; simp at hlb ⊢; omega
  · by_cases hl24 : l = 24
    · subst hl24; unfold nodeOffset gapOffset levelBytes at *; rw [levelSize_24] at hidx; simp at hlb ⊢; omega
    · have hg := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
      unfold nodeOffset; simp only [hl0, ↓reduceIte]; omega

private theorem openSub_init_eq (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    openSub.initialState .opening (trapdoor, positions) =
      submission.initialState .opening (trapdoor, positions) :=
  openSub_initialState_eq (trapdoor, positions)

theorem readOnly_getMem_index' {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (ordinal : Nat) (hord : ordinal < positions.card) :
    s.getMem (BitVec.ofNat 64 (6912218176 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le' positions
  have haddr : (BitVec.ofNat 64 (6912218176 + 8 * ordinal)).toNat = 6912218176 + 8 * ordinal := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inl (by omega)), openSub_init_eq]
  exact opening_initial_index trapdoor positions ordinal hord

theorem readOnly_getMem_data_base' {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475936 + 32 * l)) = BitVec.ofNat 64 (levelBase l) := by
  have haddr : (BitVec.ofNat 64 (68719475936 + 32 * l)).toNat = 68719475936 + 32 * l := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), openSub_init_eq,
    opening_initial_data_dword trapdoor positions (32 * l) (by omega)]
  exact openingData_dword_0 ⟨l, hl⟩

theorem readOnly_getMem_data_size' {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) := by
  have haddr : (BitVec.ofNat 64 (68719475936 + 32 * l + 8)).toNat = 68719475936 + 32 * l + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), openSub_init_eq,
    show 68719475936 + 32 * l + 8 = 68719475936 + (32 * l + 8) by omega,
    opening_initial_data_dword trapdoor positions (32 * l + 8) (by omega)]
  exact openingData_dword_1 ⟨l, hl⟩

theorem readOnly_getMem_data_markOff' {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) := by
  have haddr : (BitVec.ofNat 64 (68719475936 + 32 * l + 16)).toNat = 68719475936 + 32 * l + 16 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), openSub_init_eq,
    show 68719475936 + 32 * l + 16 = 68719475936 + (32 * l + 16) by omega,
    opening_initial_data_dword trapdoor positions (32 * l + 16) (by omega)]
  exact openingData_dword_2 ⟨l, hl⟩

theorem readOnly_getByte_trapdoor' {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (off : Nat) (hoff : off < 2617246752) :
    s.getByte (BitVec.ofNat 64 (4294971424 + off)) = trapdoor.extractLsb' (8 * off) 8 := by
  set a := 4294971424 + off
  have hdec : alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (8 * (a / 8)) := by
    have h := alignToDword_ofNat_eq (8 * (a / 8)) (a % 8) (by omega) (by omega)
    simpa only [show 8 * (a / 8) + a % 8 = a by omega] using h
  have hmem : s.getMem (alignToDword (BitVec.ofNat 64 a)) =
      (submission.initialState .opening (trapdoor, positions)).getMem
        (alignToDword (BitVec.ofNat 64 a)) := by
    rw [← openSub_init_eq, hdec]
    apply hro; left
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  change extractByte (s.getMem (alignToDword (BitVec.ofNat 64 a))) (byteOffset (BitVec.ofNat 64 a)) = _
  rw [hmem]
  exact opening_initial_trapdoor_byte trapdoor positions off hoff

theorem readOnly_getMem_tdNode {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (l idx k : Nat) (hl : l ≤ 24) (hidx : idx < levelSize l) (hk : k < 4) :
    s.getMem (BitVec.ofNat 64 (4294971424 + levelBase l + nodeOffset l idx + 8 * k)) =
      (tdNode trapdoor l idx).extractLsb' (64 * k) 64 := by
  have hbd := nodeOffset_lt_treeBytes' l idx hl hidx
  have hal1 := levelBase_align8' l hl
  have hal2 := nodeOffset_align8' l idx
  apply getMem_of_bytes_eq (addr := 4294971424 + levelBase l + nodeOffset l idx) (by omega)
  intro j hj
  rw [show 4294971424 + levelBase l + nodeOffset l idx + 8 * k + j =
      4294971424 + (levelBase l + nodeOffset l idx + (8 * k + j)) by omega]
  rw [readOnly_getByte_trapdoor' hro _ (by omega)]
  unfold tdNode
  rw [extractLsb'_extractLsb' trapdoor _ 256 (8 * (8 * k + j)) 8 (by omega)]
  congr 1; omega

theorem readOnly_getMem_tdSalt {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (i : Index) (k : Nat) (hk : k < 3) :
    s.getMem (BitVec.ofNat 64 (4294971424 + saltOff i + 8 * k)) =
      (tdSalt trapdoor i).extractLsb' (64 * k) 64 := by
  have hi : i.val < 16777216 := i.isLt
  have hsf := saltOff_formula' i
  have hal := saltOff_align8' i
  apply getMem_of_bytes_eq (addr := 4294971424 + saltOff i) (by omega)
  intro j hj
  rw [show 4294971424 + saltOff i + 8 * k + j = 4294971424 + (saltOff i + (8 * k + j)) by omega]
  rw [readOnly_getByte_trapdoor' hro _ (by omega)]
  unfold tdSalt
  rw [extractLsb'_extractLsb' trapdoor _ 192 (8 * (8 * k + j)) 8 (by omega)]
  congr 1; omega

private theorem opening_initial_zero_dword (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (a : Word) (hal : a.toNat % 8 = 0) (hlt : a.toNat < 4096) :
    (openSub.initialState .opening (trapdoor, positions)).getMem a = 0#64 := by
  rw [openSub_init_eq]
  have ha : a = BitVec.ofNat 64 (a.toNat + 8 * 0) := by simp
  rw [ha]
  have h0 : ((0#64 : Word)).extractLsb' (64 * 0) 64 = 0#64 := by decide
  rw [← h0]
  apply getMem_of_bytes_eq (addr := a.toNat) (k := 0) hal
  intro j hj
  have hz := opening_initial_zero_low trapdoor positions (a.toNat + j) (by omega)
  have hex : (0#64 : Word).extractLsb' (8 * (0 + j)) 8 = 0 := by
    apply BitVec.eq_of_getLsbD_eq; simp
  simpa only [Nat.mul_zero, Nat.add_zero, hex] using hz

/-! ### 3. Low-Memory Scratch Invariants (`[8, 456)`, `[512, 1344)`, `[1344, 1792)`) -/

/-- Scratch `[8, 192)` holds `trapdoor + levelBase l` (`l = 1..23`) and `[376, 456)` holds `512 + capMarkOff l` (`l = 15..24`). -/
structure BaseTableReady (s : MachineState) : Prop where
  lvlBase : ∀ l, 1 ≤ l → l ≤ 23 →
    s.getMem (BitVec.ofNat 64 (8 * l)) = BitVec.ofNat 64 (4294971424 + levelBase l)
  cmPtr : ∀ l, 15 ≤ l → l ≤ 24 →
    s.getMem (BitVec.ofNat 64 (256 + 8 * l)) = BitVec.ofNat 64 (512 + capMarkOff l)

/-- Cap-mark array at `[512, 1344)` after processing the first `ordinal` sorted positions. -/
def capMark15Prefix (positions : Positions) (ordinal c : Nat) : Bool :=
  ((positions.sort (· ≤ ·)).take ordinal).any fun i => capLeafOf i == c

structure CapMarks15State (s : MachineState) (positions : Positions) (ordinal : Nat) : Prop where
  l15 : ∀ c < 342, s.getByte (BitVec.ofNat 64 (512 + c)) =
    if capMark15Prefix positions ordinal c then 1#8 else 0#8
  hiZero : ∀ q, 512 + 342 ≤ q → q < 1344 → s.getByte (BitVec.ofNat 64 q) = 0#8

/-- Lazy slow-path jump tables in `[1344, 1792)`: zeroed when `tblInit = false`, populated when `true`. -/
def SlowTablesState (s : MachineState) (tblInit : Bool) : Prop :=
  if tblInit then
    ∀ r : Fin 8,
      s.getMem (BitVec.ofNat 64 (1344 + 8 * r.val)) = pcAt (pcCopy29 r) ∧
      s.getMem (BitVec.ofNat 64 (1408 + 8 * r.val)) = pcAt (pcCopy30 r) ∧
      s.getMem (BitVec.ofNat 64 (1472 + 8 * r.val)) = pcAt (pcCopy32 r) ∧
      s.getMem (BitVec.ofNat 64 (1536 + 8 * r.val)) = pcAt (pcRec r) ∧
      s.getMem (BitVec.ofNat 64 (1600 + 8 * r.val)) = pcAt (pcCopy32x3 r) ∧
      s.getMem (BitVec.ofNat 64 (1664 + 8 * r.val)) = pcAt (pcCopy30x4 r) ∧
      s.getMem (BitVec.ofNat 64 (1728 + 8 * r.val)) = pcAt (pcCopy29x2 r)
  else
    s.getMem (BitVec.ofNat 64 1344) = 0#64

theorem baseTableReady_of_lowEq {s s' : MachineState} (hb : BaseTableReady s)
    (heq : ∀ a : Word, a.toNat < 512 → s'.getMem a = s.getMem a) : BaseTableReady s' :=
  ⟨fun l h1 h2 => (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans (hb.lvlBase l h1 h2),
   fun l h1 h2 => (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans (hb.cmPtr l h1 h2)⟩

theorem capMarks15State_of_lowEq {s s' : MachineState} {positions : Positions} {ordinal : Nat}
    (hc : CapMarks15State s positions ordinal)
    (heq : ∀ a : Word, 512 ≤ a.toNat → a.toNat < 1344 → s'.getMem a = s.getMem a) :
    CapMarks15State s' positions ordinal := by
  have hbyte : ∀ q, 512 ≤ q → q < 1344 → s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q) := by
    intro q h1 h2
    simp only [MachineState.getByte]; congr 1
    have hal := alignToDword_ofNat_eq (8 * (q / 8)) (q % 8) (by omega) (by omega)
    rw [show 8 * (q / 8) + q % 8 = q by omega] at hal
    apply heq; rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  exact ⟨fun c h => (hbyte (512 + c) (by omega) (by omega)).trans (hc.l15 c h),
         fun q h1 h2 => (hbyte q (by omega) h2).trans (hc.hiZero q h1 h2)⟩

theorem slowTablesState_of_eq {s s' : MachineState} {tblInit : Bool}
    (ht : SlowTablesState s tblInit)
    (heq : ∀ a : Word, 1344 ≤ a.toNat → a.toNat < 1792 → s'.getMem a = s.getMem a) :
    SlowTablesState s' tblInit := by
  unfold SlowTablesState at ht ⊢
  cases tblInit with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at ht ⊢
    exact (heq _ (by decide) (by decide)).trans ht
  | true =>
    simp only [↓reduceIte] at ht ⊢
    intro r; have hr := r.isLt; have h := ht r
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans h.1
    · exact (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans h.2.1
    · exact (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans h.2.2.1
    · exact (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans h.2.2.2.1
    · exact (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans h.2.2.2.2.1
    · exact (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans h.2.2.2.2.2.1
    · exact (heq _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)).trans h.2.2.2.2.2.2

theorem capMarks15_set_mark {s : MachineState} {positions : Positions} {ordinal : Nat}
    (hord : ordinal < positions.card)
    (hc : CapMarks15State s positions ordinal) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    CapMarks15State (s.setByte (BitVec.ofNat 64 (512 + capLeafOf i)) 1#8) positions (ordinal + 1) := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  have hcl_lt : capLeafOf i < 342 := by
    unfold capLeafOf; have hi : i.val < 16777216 := i.isLt
    simp only [Nat.shiftRight_eq_div_pow]; omega
  refine ⟨fun c hc_lt => ?_, fun q hq1 hq2 => ?_⟩
  · rw [set_byte_read]
    have htake : capMark15Prefix positions (ordinal + 1) c =
        (capMark15Prefix positions ordinal c || (capLeafOf i == c)) := by
      unfold capMark15Prefix
      rw [List.take_succ_eq_append_getElem (by simp [hord]), List.any_append, List.any_cons,
        List.any_nil, Bool.or_false]
    rw [htake]
    by_cases hceq : c = capLeafOf i
    · subst hceq; simp
    · have hne : BitVec.ofNat 64 (512 + c) ≠ BitVec.ofNat 64 (512 + capLeafOf i) := by
        intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 512 + c < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 512 + capLeafOf i < 2 ^ 64)] at hn; omega
      rw [if_neg hne, show (capLeafOf i == c) = false from beq_false_of_ne (Ne.symm hceq), Bool.or_false]
      exact hc.l15 c hc_lt
  · rw [set_byte_read]
    have hne : BitVec.ofNat 64 q ≠ BitVec.ofNat 64 (512 + capLeafOf i) := by
      intro h; have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 512 + capLeafOf i < 2 ^ 64)] at hn; omega
    rw [if_neg hne]; exact hc.hiZero q hq1 hq2

/-! ### 4. Entry Execution (`positions.card = 0` and `positions.card > 0`) -/

private theorem opening_initial_regs (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    s0.pc = pcAt 0 ∧
    s0.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
    s0.getReg .x12 = BitVec.ofNat 64 4294971424 ∧
    s0.getReg .x13 = BitVec.ofNat 64 6912218176 ∧
    s0.getReg .x15 = BitVec.ofNat 64 11341403200 ∧
    s0.getReg .x16 = BitVec.ofNat 64 positions.card := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  change BitVec.ofNat 64 (dataBase (submission.image .opening)) = _
  rw [opening_dataBase]

/-- Empty batch (`positions.card = 0`): `4` steps (`4` cycles) to `ECALL` at `PC = 4` (`5` cycles total). -/
theorem openRuns_entry_empty (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hempty : positions.card = 0) :
    let s0 := openSub.initialState .opening (trapdoor, positions)
    ∃ s4 : MachineState,
      OpenRuns s0 4 4 s4 ∧
      s4.pc = pcAt 4 ∧
      s4.getReg .x5 = 1#64 ∧
      s4.getReg .x10 = 0#64 ∧
      s4.getReg .x11 = 0#64 := by
  set s0 := openSub.initialState .opening (trapdoor, positions)
  have hs0_eq : s0 = submission.initialState .opening (trapdoor, positions) := openSub_init_eq trapdoor positions
  obtain ⟨hpc0', _, _, _, _, hx16'⟩ := opening_initial_regs trapdoor positions
  have hpc0 : s0.pc = pcAt 0 := by rw [hs0_eq]; exact hpc0'
  have hx16 : s0.getReg .x16 = 0#64 := by rw [hs0_eq, hx16', hempty]
  have h0 := step_BNE_not_taken (s := s0) (by decide) hpc0 (rfl : openInstr 0 = .base (.BNE .x16 .x0 (20#13)))
    (by rw [hx16]; rfl)
  set s1 := s0.setPC (pcAt 1)
  have h1 := step_ADDI (s := s1) (by decide) rfl (rfl : openInstr 1 = .base (.ADDI .x11 .x0 (0#12)))
  set s2 := (s1.setReg .x11 (s1.getReg .x0 + signExtend12 (0#12))).setPC (pcAt 2)
  have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 2 = .base (.ADDI .x5 .x0 (1#12)))
  set s3 := (s2.setReg .x5 (s2.getReg .x0 + signExtend12 (1#12))).setPC (pcAt 3)
  have h3 := step_ADDI (s := s3) (by decide) rfl (rfl : openInstr 3 = .base (.ADDI .x10 .x0 (0#12)))
  set s4 := (s3.setReg .x10 (s3.getReg .x0 + signExtend12 (0#12))).setPC (pcAt 4)
  refine ⟨s4, ((h0.trans h1).trans h2).trans h3, rfl, ?_, ?_, ?_⟩
  · simp [s4, s3, getReg_setReg_ne', show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1 (by omega)]
  · simp [s4, show s3.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 0 (by omega)]
  · simp [s4, s3, s2, getReg_setReg_ne', show s1.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 0 (by omega)]

private theorem openRuns_init_base_loop {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} :
    ∀ k (hk : k ≤ 23) (sk : MachineState),
      sk.pc = pcAt 13 →
      sk.getReg .x9 = BitVec.ofNat 64 4294971424 →
      sk.getReg .x5 = BitVec.ofNat 64 (68719475936 + 32 * (24 - k)) →
      sk.getReg .x6 = BitVec.ofNat 64 (8 * (24 - k)) →
      sk.getReg .x7 = BitVec.ofNat 64 192 →
      ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) sk →
      (∀ l, 1 ≤ l → l < 24 - k → sk.getMem (BitVec.ofNat 64 (8 * l)) = BitVec.ofNat 64 (4294971424 + levelBase l)) →
      (∀ a : Word, a.toNat % 8 = 0 → 192 ≤ a.toNat → a.toNat < 4096 → sk.getMem a = 0#64) →
      1 ≤ k →
      ∃ s' : MachineState,
        OpenRuns sk (6 * k) (6 * k) s' ∧
        s'.pc = pcAt 19 ∧
        RegsEqExcept [.x5, .x6, .x10] sk s' ∧
        ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s' ∧
        (∀ l, 1 ≤ l → l ≤ 23 → s'.getMem (BitVec.ofNat 64 (8 * l)) = BitVec.ofNat 64 (4294971424 + levelBase l)) ∧
        (∀ a : Word, a.toNat % 8 = 0 → 192 ≤ a.toNat → a.toNat < 4096 → s'.getMem a = 0#64) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h1; omega
  | succ k ih =>
    intro hk sk hpc hx9 hx5 hx6 hx7 hrok hdone hzerok _
    set l := 24 - (k + 1)
    have hl1 : 1 ≤ l := by omega
    have hl23 : l ≤ 23 := by omega
    have hld_addr : sk.getReg .x5 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
      rw [hx5, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hld_val : accessValid (sk.getReg .x5 + signExtend12 (0#12)) 8 = true := by
      rw [hld_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
    have h1 := step_LD (s := sk) (by decide) hpc (rfl : openInstr 13 = .base (.LD .x10 .x5 (0#12))) hld_val
    set t1 := (sk.setReg .x10 (sk.getMem (sk.getReg .x5 + signExtend12 (0#12)))).setPC (pcAt 14)
    have h2 := step_ADD (s := t1) (by decide) rfl (rfl : openInstr 14 = .base (.ADD .x10 .x9 .x10))
    set t2 := (t1.setReg .x10 (t1.getReg .x9 + t1.getReg .x10)).setPC (pcAt 15)
    have ht2_x6 : t2.getReg .x6 = BitVec.ofNat 64 (8 * l) := by simp [t2, t1, getReg_setReg_ne', hx6]
    have hsd_addr : t2.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (8 * l) := by
      rw [ht2_x6, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsd_val : accessValid (t2.getReg .x6 + signExtend12 (0#12)) 8 = true := by
      rw [hsd_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
    have h3 := step_SD (s := t2) (by decide) rfl (rfl : openInstr 15 = .base (.SD .x6 .x10 (0#12))) hsd_val
    set t3 := (t2.setMem (t2.getReg .x6 + signExtend12 (0#12)) (t2.getReg .x10)).setPC (pcAt 16)
    have h4 := step_ADDI (s := t3) (by decide) rfl (rfl : openInstr 16 = .base (.ADDI .x5 .x5 (32#12)))
    set t4 := (t3.setReg .x5 (t3.getReg .x5 + signExtend12 (32#12))).setPC (pcAt 17)
    have h5 := step_ADDI (s := t4) (by decide) rfl (rfl : openInstr 17 = .base (.ADDI .x6 .x6 (8#12)))
    set t5 := (t4.setReg .x6 (t4.getReg .x6 + signExtend12 (8#12))).setPC (pcAt 18)
    have ht2_x10 : t2.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
      simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        getReg_setReg_ne', hx9, hld_addr, readOnly_getMem_data_base' hrok l (by omega), ← BitVec.ofNat_add]
    have ht5_x5 : t5.getReg .x5 = BitVec.ofNat 64 (68719475936 + 32 * (l + 1)) := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, getReg_setMem, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx5, signExtend12_nonneg 32 (by omega), ← BitVec.ofNat_add]
      congr 1
    have ht5_x6 : t5.getReg .x6 = BitVec.ofNat 64 (8 * (l + 1)) := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, getReg_setMem, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx6, signExtend12_nonneg 8 (by omega), ← BitVec.ofNat_add]
      congr 1
    have ht5_x7 : t5.getReg .x7 = BitVec.ofNat 64 192 := by
      simp [t5, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hx7]
    have hmem_pres : ∀ a : Word, a ≠ BitVec.ofNat 64 (8 * l) → t5.getMem a = sk.getMem a := by
      intro a ha
      simp only [t5, t4, t3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsd_addr]
      exact MachineState.getMem_setMem_ne ha
    have hrot5 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) t5 := by
      intro a ha; rw [hmem_pres a (by intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha; omega)]
      exact hrok a ha
    have hzerot5 : ∀ a : Word, a.toNat % 8 = 0 → 192 ≤ a.toNat → a.toNat < 4096 → t5.getMem a = 0#64 := by
      intro a hal h1 h2; rw [hmem_pres a (by intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; omega)]
      exact hzerok a hal h1 h2
    have hdonet5 : ∀ l', 1 ≤ l' → l' < l + 1 →
        t5.getMem (BitVec.ofNat 64 (8 * l')) = BitVec.ofNat 64 (4294971424 + levelBase l') := by
      intro l' hl'1 hl'2
      by_cases heq : l' = l
      · subst heq; simp [t5, t4, t3, hsd_addr, ht2_x10]
      · have hne : BitVec.ofNat 64 (8 * l') ≠ BitVec.ofNat 64 (8 * l) := by
          intro h; have hn := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * l' < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 8 * l < 2 ^ 64)] at hn; omega
        rw [hmem_pres _ hne]
        exact hdone l' hl'1 (by omega)
    have hregs5 : RegsEqExcept [.x5, .x6, .x10] sk t5 := by
      intro reg hreg
      have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
      have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
      have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
      simp [t5, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne' .x6 reg h6'.symm,
        getReg_setReg_ne' .x5 reg h5'.symm, getReg_setReg_ne' .x10 reg h10'.symm]
    cases k with
    | zero =>
      have hl_eq : l = 23 := by omega
      have heq67 : t5.getReg .x6 = t5.getReg .x7 := by rw [ht5_x6, ht5_x7, hl_eq]
      have h6 := step_BNE_not_taken (s := t5) (by decide) rfl
        (rfl : openInstr 18 = .base (.BNE .x6 .x7 (8172#13))) heq67
      set t6 := t5.setPC (pcAt 19)
      refine ⟨t6, ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6, rfl,
        fun r hr => (by simp [t6] : t6.getReg r = t5.getReg r).trans (hregs5 r hr),
        fun a ha => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hrot5 a ha),
        fun l' h1 h2 => (by simp [t6] : t6.getMem _ = t5.getMem _).trans (hdonet5 l' h1 (by omega)),
        fun a hal h1 h2 => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hzerot5 a hal h1 h2)⟩
    | succ k' =>
      have hne67 : t5.getReg .x6 ≠ t5.getReg .x7 := by
        rw [ht5_x6, ht5_x7]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * (l + 1) < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 192 < 2 ^ 64)] at hn; omega
      have hbr : pcAt 18 + signExtend13 (8172#13) = pcAt 13 := by
        simpa only [show 8192 - 4 * (18 - 13) = 8172 by decide] using pcAt_add_neg13 18 13 (by omega) (by omega)
      have h6 := step_BNE_taken (s := t5) (by decide) rfl
        (rfl : openInstr 18 = .base (.BNE .x6 .x7 (8172#13))) hne67 hbr
      set t6 := t5.setPC (pcAt 13)
      obtain ⟨s', hrest, hpc', hreg', hro', hdone', hzero'⟩ := ih (by omega) t6 rfl
        ((by simp [t6] : t6.getReg .x9 = t5.getReg .x9).trans ((hregs5 .x9 (by simp)).trans hx9))
        (by simpa [t6, show l + 1 = 24 - (k' + 1) by omega] using ht5_x5)
        (by simpa [t6, show l + 1 = 24 - (k' + 1) by omega] using ht5_x6)
        (by simpa [t6] using ht5_x7)
        (fun a ha => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hrot5 a ha))
        (fun l' h1 h2 => (by simp [t6] : t6.getMem _ = t5.getMem _).trans (hdonet5 l' h1 (by omega)))
        (fun a hal h1 h2 => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hzerot5 a hal h1 h2))
        (by omega)
      refine ⟨s', ?_, hpc', fun r hr => (hreg' r hr).trans ((by simp [t6] : t6.getReg r = t5.getReg r).trans (hregs5 r hr)),
        hro', hdone', hzero'⟩
      have hrun := (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans hrest
      simpa only [show 1 + 1 + 1 + 1 + 1 + 1 + 6 * (k' + 1) = 6 * (k' + 1 + 1) by omega] using hrun

private theorem openRuns_init_cm_loop {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} :
    ∀ k (hk : k ≤ 10) (sk : MachineState),
      sk.pc = pcAt 22 →
      sk.getReg .x5 = BitVec.ofNat 64 (68719475936 + 32 * (25 - k) + 16) →
      sk.getReg .x6 = BitVec.ofNat 64 (256 + 8 * (25 - k)) →
      sk.getReg .x7 = BitVec.ofNat 64 456 →
      ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) sk →
      (∀ l, 1 ≤ l → l ≤ 23 → sk.getMem (BitVec.ofNat 64 (8 * l)) = BitVec.ofNat 64 (4294971424 + levelBase l)) →
      (∀ l, 15 ≤ l → l < 25 - k → sk.getMem (BitVec.ofNat 64 (256 + 8 * l)) = BitVec.ofNat 64 (512 + capMarkOff l)) →
      (∀ a : Word, a.toNat % 8 = 0 → 512 ≤ a.toNat → a.toNat < 4096 → sk.getMem a = 0#64) →
      1 ≤ k →
      ∃ s' : MachineState,
        OpenRuns sk (6 * k) (6 * k) s' ∧
        s'.pc = pcAt 28 ∧
        RegsEqExcept [.x5, .x6, .x10] sk s' ∧
        ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s' ∧
        BaseTableReady s' ∧
        (∀ a : Word, a.toNat % 8 = 0 → 512 ≤ a.toNat → a.toNat < 4096 → s'.getMem a = 0#64) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h1; omega
  | succ k ih =>
    intro hk sk hpc hx5 hx6 hx7 hrok hbase hcm hzerok _
    set l := 25 - (k + 1)
    have hl15 : 15 ≤ l := by omega
    have hl24 : l ≤ 24 := by omega
    have hld_addr : sk.getReg .x5 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 16) := by
      rw [hx5, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hld_val : accessValid (sk.getReg .x5 + signExtend12 (0#12)) 8 = true := by
      rw [hld_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
    have h1 := step_LD (s := sk) (by decide) hpc (rfl : openInstr 22 = .base (.LD .x10 .x5 (0#12))) hld_val
    set t1 := (sk.setReg .x10 (sk.getMem (sk.getReg .x5 + signExtend12 (0#12)))).setPC (pcAt 23)
    have h2 := step_ADDI (s := t1) (by decide) rfl (rfl : openInstr 23 = .base (.ADDI .x10 .x10 (512#12)))
    set t2 := (t1.setReg .x10 (t1.getReg .x10 + signExtend12 (512#12))).setPC (pcAt 24)
    have ht2_x6 : t2.getReg .x6 = BitVec.ofNat 64 (256 + 8 * l) := by simp [t2, t1, getReg_setReg_ne', hx6]
    have hsd_addr : t2.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (256 + 8 * l) := by
      rw [ht2_x6, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsd_val : accessValid (t2.getReg .x6 + signExtend12 (0#12)) 8 = true := by
      rw [hsd_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
    have h3 := step_SD (s := t2) (by decide) rfl (rfl : openInstr 24 = .base (.SD .x6 .x10 (0#12))) hsd_val
    set t3 := (t2.setMem (t2.getReg .x6 + signExtend12 (0#12)) (t2.getReg .x10)).setPC (pcAt 25)
    have h4 := step_ADDI (s := t3) (by decide) rfl (rfl : openInstr 25 = .base (.ADDI .x5 .x5 (32#12)))
    set t4 := (t3.setReg .x5 (t3.getReg .x5 + signExtend12 (32#12))).setPC (pcAt 26)
    have h5 := step_ADDI (s := t4) (by decide) rfl (rfl : openInstr 26 = .base (.ADDI .x6 .x6 (8#12)))
    set t5 := (t4.setReg .x6 (t4.getReg .x6 + signExtend12 (8#12))).setPC (pcAt 27)
    have ht2_x10 : t2.getReg .x10 = BitVec.ofNat 64 (512 + capMarkOff l) := by
      simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        hld_addr, readOnly_getMem_data_markOff' hrok l (by omega), signExtend12_nonneg 512 (by omega), ← BitVec.ofNat_add]
      congr 1; omega
    have ht5_x5 : t5.getReg .x5 = BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 16) := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, getReg_setMem, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx5, signExtend12_nonneg 32 (by omega), ← BitVec.ofNat_add]
      congr 1
    have ht5_x6 : t5.getReg .x6 = BitVec.ofNat 64 (256 + 8 * (l + 1)) := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, getReg_setMem, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx6, signExtend12_nonneg 8 (by omega), ← BitVec.ofNat_add]
      congr 1
    have ht5_x7 : t5.getReg .x7 = BitVec.ofNat 64 456 := by
      simp [t5, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne', hx7]
    have hmem_pres : ∀ a : Word, a ≠ BitVec.ofNat 64 (256 + 8 * l) → t5.getMem a = sk.getMem a := by
      intro a ha
      simp only [t5, t4, t3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsd_addr]
      exact MachineState.getMem_setMem_ne ha
    have hrot5 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) t5 := by
      intro a ha; rw [hmem_pres a (by intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ha; omega)]
      exact hrok a ha
    have hbaset5 : ∀ l', 1 ≤ l' → l' ≤ 23 → t5.getMem (BitVec.ofNat 64 (8 * l')) = BitVec.ofNat 64 (4294971424 + levelBase l') := by
      intro l' h1 h2
      have hne : BitVec.ofNat 64 (8 * l') ≠ BitVec.ofNat 64 (256 + 8 * l) := by
        intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * l' < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 256 + 8 * l < 2 ^ 64)] at hn; omega
      rw [hmem_pres _ hne]
      exact hbase l' h1 h2
    have hzerot5 : ∀ a : Word, a.toNat % 8 = 0 → 512 ≤ a.toNat → a.toNat < 4096 → t5.getMem a = 0#64 := by
      intro a hal h1 h2; rw [hmem_pres a (by intro h; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1; omega)]
      exact hzerok a hal h1 h2
    have hcmt5 : ∀ l', 15 ≤ l' → l' < l + 1 →
        t5.getMem (BitVec.ofNat 64 (256 + 8 * l')) = BitVec.ofNat 64 (512 + capMarkOff l') := by
      intro l' hl'1 hl'2
      by_cases heq : l' = l
      · subst heq; simp [t5, t4, t3, hsd_addr, ht2_x10]
      · have hne : BitVec.ofNat 64 (256 + 8 * l') ≠ BitVec.ofNat 64 (256 + 8 * l) := by
          intro h; have hn := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 256 + 8 * l' < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 256 + 8 * l < 2 ^ 64)] at hn; omega
        rw [hmem_pres _ hne]
        exact hcm l' hl'1 (by omega)
    have hregs5 : RegsEqExcept [.x5, .x6, .x10] sk t5 := by
      intro reg hreg
      have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
      have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
      have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
      simp [t5, t4, t3, t2, t1, getReg_setMem, getReg_setReg_ne' .x6 reg h6'.symm,
        getReg_setReg_ne' .x5 reg h5'.symm, getReg_setReg_ne' .x10 reg h10'.symm]
    cases k with
    | zero =>
      have hl_eq : l = 24 := by omega
      have heq67 : t5.getReg .x6 = t5.getReg .x7 := by rw [ht5_x6, ht5_x7, hl_eq]
      have h6 := step_BNE_not_taken (s := t5) (by decide) rfl
        (rfl : openInstr 27 = .base (.BNE .x6 .x7 (8172#13))) heq67
      set t6 := t5.setPC (pcAt 28)
      refine ⟨t6, ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6, rfl,
        fun r hr => (by simp [t6] : t6.getReg r = t5.getReg r).trans (hregs5 r hr),
        fun a ha => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hrot5 a ha),
        ⟨fun l' h1 h2 => (by simp [t6] : t6.getMem _ = t5.getMem _).trans (hbaset5 l' h1 h2),
         fun l' h1 h2 => (by simp [t6] : t6.getMem _ = t5.getMem _).trans (hcmt5 l' h1 (by omega))⟩,
        fun a hal h1 h2 => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hzerot5 a hal h1 h2)⟩
    | succ k' =>
      have hne67 : t5.getReg .x6 ≠ t5.getReg .x7 := by
        rw [ht5_x6, ht5_x7]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 256 + 8 * (l + 1) < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 456 < 2 ^ 64)] at hn; omega
      have hbr : pcAt 27 + signExtend13 (8172#13) = pcAt 22 := by
        simpa only [show 8192 - 4 * (27 - 22) = 8172 by decide] using pcAt_add_neg13 27 22 (by omega) (by omega)
      have h6 := step_BNE_taken (s := t5) (by decide) rfl
        (rfl : openInstr 27 = .base (.BNE .x6 .x7 (8172#13))) hne67 hbr
      set t6 := t5.setPC (pcAt 22)
      obtain ⟨s', hrest, hpc', hreg', hro', hbt', hzero'⟩ := ih (by omega) t6 rfl
        (by simpa [t6, show l + 1 = 25 - (k' + 1) by omega] using ht5_x5)
        (by simpa [t6, show l + 1 = 25 - (k' + 1) by omega] using ht5_x6)
        (by simpa [t6] using ht5_x7)
        (fun a ha => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hrot5 a ha))
        (fun l' h1 h2 => (by simp [t6] : t6.getMem _ = t5.getMem _).trans (hbaset5 l' h1 h2))
        (fun l' h1 h2 => (by simp [t6] : t6.getMem _ = t5.getMem _).trans (hcmt5 l' h1 (by omega)))
        (fun a hal h1 h2 => (by simp [t6] : t6.getMem a = t5.getMem a).trans (hzerot5 a hal h1 h2))
        (by omega)
      refine ⟨s', ?_, hpc', fun r hr => (hreg' r hr).trans ((by simp [t6] : t6.getReg r = t5.getReg r).trans (hregs5 r hr)),
        hro', hbt', hzero'⟩
      have hrun := (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans hrest
      simpa only [show 1 + 1 + 1 + 1 + 1 + 1 + 6 * (k' + 1) = 6 * (k' + 1 + 1) by omega] using hrun

/-- Execute `entry` tail (`PC 28..59`, 31 cycles) setting all persistent registers. -/
private theorem openRuns_entry_regs {s : MachineState}
    (hpc : s.pc = pcAt 28)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hbt : BaseTableReady s) :
    ∃ s' : MachineState,
      OpenRuns s 31 31 s' ∧
      s'.pc = pcAt PC_rec_r0 ∧
      (∀ a, s'.getMem a = s.getMem a) ∧
      s'.getReg .x1 = BitVec.ofNat 64 (4294971424 + levelBase 1) ∧
      s'.getReg .x2 = BitVec.ofNat 64 (4294971424 + levelBase 2) ∧
      s'.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11) ∧
      s'.getReg .x4 = 1#64 ∧
      s'.getReg .x7 = BitVec.ofNat 64 (4294971424 + levelBase 10) ∧
      s'.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s'.getReg .x11 = mask40Word ∧
      s'.getReg .x12 = 0#64 ∧
      s'.getReg .x13 = BitVec.ofNat 64 5592064 ∧
      s'.getReg .x14 = BitVec.ofNat 64 (4294971424 + levelBase 3) ∧
      s'.getReg .x15 = BitVec.ofNat 64 tailBufBase ∧
      s'.getReg .x16 = 0#64 ∧
      s'.getReg .x17 = negCnt 0 ∧
      s'.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952) ∧
      s'.getReg .x19 = BitVec.ofNat 64 1364 ∧
      s'.getReg .x20 = BitVec.ofNat 64 3 ∧
      s'.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4) ∧
      s'.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9) ∧
      s'.getReg .x24 = s.getReg .x24 ∧
      s'.getReg .x25 = s.getReg .x25 ∧
      s'.getReg .x26 = BitVec.ofNat 64 (4294971424 + levelBase 5) ∧
      s'.getReg .x27 = s.getReg .x27 ∧
      s'.getReg .x29 = BitVec.ofNat 64 (4294971424 + levelBase 6) ∧
      s'.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7) ∧
      s'.getReg .x31 = BitVec.ofNat 64 (4294971424 + levelBase 8) := by
  have h28 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 28 = .base (.ADDI .x4 .x0 (1#12)))
  set s29 := (s.setReg .x4 (s.getReg .x0 + signExtend12 (1#12))).setPC (pcAt 29)
  have h29 := step_ADDI (s := s29) (by decide) rfl (rfl : openInstr 29 = .base (.ADDI .x11 .x0 (1#12)))
  set s30 := (s29.setReg .x11 (s29.getReg .x0 + signExtend12 (1#12))).setPC (pcAt 30)
  have h30 := step_SLLI (s := s30) (by decide) rfl (rfl : openInstr 30 = .base (.SLLI .x11 .x11 (40#6)))
  set s31 := (s30.setReg .x11 (s30.getReg .x11 <<< (40#6).toNat)).setPC (pcAt 31)
  have h31 := step_ADDI (s := s31) (by decide) rfl (rfl : openInstr 31 = .base (.ADDI .x11 .x11 (4095#12)))
  set s32 := (s31.setReg .x11 (s31.getReg .x11 + signExtend12 (4095#12))).setPC (pcAt 32)
  have h32 := step_ADDI (s := s32) (by decide) rfl (rfl : openInstr 32 = .base (.ADDI .x12 .x0 (0#12)))
  set s33 := (s32.setReg .x12 (s32.getReg .x0 + signExtend12 (0#12))).setPC (pcAt 33)
  have h33 := step_LUI (s := s33) (by decide) rfl (rfl : openInstr 33 = .base (.LUI .x13 (1365#20)))
  set s34 := (s33.setReg .x13 (((1365#20 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)).setPC (pcAt 34)
  have h34 := step_ADDI (s := s34) (by decide) rfl (rfl : openInstr 34 = .base (.ADDI .x13 .x13 (1024#12)))
  set s35 := (s34.setReg .x13 (s34.getReg .x13 + signExtend12 (1024#12))).setPC (pcAt 35)
  have h35 := step_ADDI (s := s35) (by decide) rfl (rfl : openInstr 35 = .base (.ADDI .x15 .x0 (2#12)))
  set s36 := (s35.setReg .x15 (s35.getReg .x0 + signExtend12 (2#12))).setPC (pcAt 36)
  have h36 := step_SLLI (s := s36) (by decide) rfl (rfl : openInstr 36 = .base (.SLLI .x15 .x15 (11#6)))
  set s37 := (s36.setReg .x15 (s36.getReg .x15 <<< (11#6).toNat)).setPC (pcAt 37)
  have h37 := step_ADDI (s := s37) (by decide) rfl (rfl : openInstr 37 = .base (.ADDI .x15 .x15 (672#12)))
  set s38 := (s37.setReg .x15 (s37.getReg .x15 + signExtend12 (672#12))).setPC (pcAt 38)
  have h38 := step_SLLI (s := s38) (by decide) rfl (rfl : openInstr 38 = .base (.SLLI .x15 .x15 (11#6)))
  set s39 := (s38.setReg .x15 (s38.getReg .x15 <<< (11#6).toNat)).setPC (pcAt 39)
  have h39 := step_ADDI (s := s39) (by decide) rfl (rfl : openInstr 39 = .base (.ADDI .x15 .x15 (761#12)))
  set s40 := (s39.setReg .x15 (s39.getReg .x15 + signExtend12 (761#12))).setPC (pcAt 40)
  have h40 := step_SLLI (s := s40) (by decide) rfl (rfl : openInstr 40 = .base (.SLLI .x15 .x15 (11#6)))
  set s41 := (s40.setReg .x15 (s40.getReg .x15 <<< (11#6).toNat)).setPC (pcAt 41)
  have h41 := step_ADDI (s := s41) (by decide) rfl (rfl : openInstr 41 = .base (.ADDI .x16 .x0 (0#12)))
  set s42 := (s41.setReg .x16 (s41.getReg .x0 + signExtend12 (0#12))).setPC (pcAt 42)
  have h42 := step_ADDI (s := s42) (by decide) rfl (rfl : openInstr 42 = .base (.ADDI .x17 .x0 (4032#12)))
  set s43 := (s42.setReg .x17 (s42.getReg .x0 + signExtend12 (4032#12))).setPC (pcAt 43)
  have h43 := step_LUI (s := s43) (by decide) rfl (rfl : openInstr 43 = .base (.LUI .x6 (262144#20)))
  set s44 := (s43.setReg .x6 (((262144#20 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)).setPC (pcAt 44)
  have h44 := step_ADDI (s := s44) (by decide) rfl (rfl : openInstr 44 = .base (.ADDI .x6 .x6 (1128#12)))
  set s45 := (s44.setReg .x6 (s44.getReg .x6 + signExtend12 (1128#12))).setPC (pcAt 45)
  have h45 := step_ADD (s := s45) (by decide) rfl (rfl : openInstr 45 = .base (.ADD .x18 .x9 .x6))
  set s46 := (s45.setReg .x18 (s45.getReg .x9 + s45.getReg .x6)).setPC (pcAt 46)
  have h46 := step_ADDI (s := s46) (by decide) rfl (rfl : openInstr 46 = .base (.ADDI .x19 .x0 (1364#12)))
  set s47 := (s46.setReg .x19 (s46.getReg .x0 + signExtend12 (1364#12))).setPC (pcAt 47)
  have h47 := step_ADDI (s := s47) (by decide) rfl (rfl : openInstr 47 = .base (.ADDI .x20 .x0 (3#12)))
  set s48 := (s47.setReg .x20 (s47.getReg .x0 + signExtend12 (3#12))).setPC (pcAt 48)
  have hmem48 : ∀ a, s48.getMem a = s.getMem a := fun a => by
    simp [s48, s47, s46, s45, s44, s43, s42, s41, s40, s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29]
  have hval_ld : ∀ k (hk : k < 2048), k % 8 = 0 →
      accessValid (0#64 + signExtend12 (BitVec.ofNat 12 k)) 8 = true := fun k hk hal => by
    rw [signExtend12_nonneg k hk, BitVec.zero_add]; exact accessValid_ofNat k 8 (by omega) hal
  have h48 := step_LD (s := s48) (by decide) rfl (rfl : openInstr 48 = .base (.LD .x1 .x0 (8#12))) (hval_ld 8 (by omega) (by omega))
  set s49 := (s48.setReg .x1 (s48.getMem (s48.getReg .x0 + signExtend12 (8#12)))).setPC (pcAt 49)
  have h49 := step_LD (s := s49) (by decide) rfl (rfl : openInstr 49 = .base (.LD .x2 .x0 (16#12))) (hval_ld 16 (by omega) (by omega))
  set s50 := (s49.setReg .x2 (s49.getMem (s49.getReg .x0 + signExtend12 (16#12)))).setPC (pcAt 50)
  have h50 := step_LD (s := s50) (by decide) rfl (rfl : openInstr 50 = .base (.LD .x14 .x0 (24#12))) (hval_ld 24 (by omega) (by omega))
  set s51 := (s50.setReg .x14 (s50.getMem (s50.getReg .x0 + signExtend12 (24#12)))).setPC (pcAt 51)
  have h51 := step_LD (s := s51) (by decide) rfl (rfl : openInstr 51 = .base (.LD .x21 .x0 (32#12))) (hval_ld 32 (by omega) (by omega))
  set s52 := (s51.setReg .x21 (s51.getMem (s51.getReg .x0 + signExtend12 (32#12)))).setPC (pcAt 52)
  have h52 := step_LD (s := s52) (by decide) rfl (rfl : openInstr 52 = .base (.LD .x26 .x0 (40#12))) (hval_ld 40 (by omega) (by omega))
  set s53 := (s52.setReg .x26 (s52.getMem (s52.getReg .x0 + signExtend12 (40#12)))).setPC (pcAt 53)
  have h53 := step_LD (s := s53) (by decide) rfl (rfl : openInstr 53 = .base (.LD .x29 .x0 (48#12))) (hval_ld 48 (by omega) (by omega))
  set s54 := (s53.setReg .x29 (s53.getMem (s53.getReg .x0 + signExtend12 (48#12)))).setPC (pcAt 54)
  have h54 := step_LD (s := s54) (by decide) rfl (rfl : openInstr 54 = .base (.LD .x30 .x0 (56#12))) (hval_ld 56 (by omega) (by omega))
  set s55 := (s54.setReg .x30 (s54.getMem (s54.getReg .x0 + signExtend12 (56#12)))).setPC (pcAt 55)
  have h55 := step_LD (s := s55) (by decide) rfl (rfl : openInstr 55 = .base (.LD .x31 .x0 (64#12))) (hval_ld 64 (by omega) (by omega))
  set s56 := (s55.setReg .x31 (s55.getMem (s55.getReg .x0 + signExtend12 (64#12)))).setPC (pcAt 56)
  have h56 := step_LD (s := s56) (by decide) rfl (rfl : openInstr 56 = .base (.LD .x23 .x0 (72#12))) (hval_ld 72 (by omega) (by omega))
  set s57 := (s56.setReg .x23 (s56.getMem (s56.getReg .x0 + signExtend12 (72#12)))).setPC (pcAt 57)
  have h57 := step_LD (s := s57) (by decide) rfl (rfl : openInstr 57 = .base (.LD .x7 .x0 (80#12))) (hval_ld 80 (by omega) (by omega))
  set s58 := (s57.setReg .x7 (s57.getMem (s57.getReg .x0 + signExtend12 (80#12)))).setPC (pcAt 58)
  have h58 := step_LD (s := s58) (by decide) rfl (rfl : openInstr 58 = .base (.LD .x3 .x0 (88#12))) (hval_ld 88 (by omega) (by omega))
  set s59 := (s58.setReg .x3 (s58.getMem (s58.getReg .x0 + signExtend12 (88#12)))).setPC (pcAt 59)
  have hrun : OpenRuns s 31 31 s59 := by
    have hA := (((((((((h28.trans h29).trans h30).trans h31).trans h32).trans h33).trans h34).trans h35).trans h36).trans h37)
    have hB := (((((((((h38.trans h39).trans h40).trans h41).trans h42).trans h43).trans h44).trans h45).trans h46).trans h47)
    have hC := ((((((((((h48.trans h49).trans h50).trans h51).trans h52).trans h53).trans h54).trans h55).trans h56).trans h57).trans h58)
    exact (hA.trans hB).trans hC
  have hx11_val : s32.getReg .x11 = mask40Word := by
    have h30' : s30.getReg .x11 = BitVec.ofNat 64 1 := by
      simp [s30, show s29.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1 (by omega)]
    have h31' : s31.getReg .x11 = BitVec.ofNat 64 (2 ^ 40) := by
      simp [s31, h30', bv64_shl]
    have hneg1 : signExtend12 (4095#12) = BitVec.ofNat 64 (2 ^ 64 - 1) :=
      signExtend12_neg 1 (by omega) (by omega)
    simp only [s32, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h31', hneg1, ← BitVec.ofNat_add, mask40Word]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
    have heq : 2 ^ 40 + (2 ^ 64 - 1) = (2 ^ 40 - 1) + 2 ^ 64 := by omega
    rw [heq, Nat.add_mod_right]
  have hx13_val : s35.getReg .x13 = BitVec.ofNat 64 5592064 := by
    have h34' : s34.getReg .x13 = BitVec.ofNat 64 (4096 * 1365) := by
      simp [s34, lui_ofNat_nonneg 1365 (by omega)]
    simp only [s35, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h34', signExtend12_nonneg 1024 (by omega), ← BitVec.ofNat_add]
  have hx15_val : s41.getReg .x15 = BitVec.ofNat 64 tailBufBase := by
    have h36' : s36.getReg .x15 = BitVec.ofNat 64 2 := by
      simp [s36, show s35.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 2 (by omega)]
    have h37' : s37.getReg .x15 = BitVec.ofNat 64 (2 * 2 ^ 11) := by simp [s37, h36', bv64_shl]
    have h38' : s38.getReg .x15 = BitVec.ofNat 64 (2 * 2 ^ 11 + 672) := by
      simp [s38, h37', signExtend12_nonneg 672 (by omega), ← BitVec.ofNat_add]
    have h39' : s39.getReg .x15 = BitVec.ofNat 64 ((2 * 2 ^ 11 + 672) * 2 ^ 11) := by simp [s39, h38', bv64_shl]
    have h40' : s40.getReg .x15 = BitVec.ofNat 64 ((2 * 2 ^ 11 + 672) * 2 ^ 11 + 761) := by
      simp [s40, h39', signExtend12_nonneg 761 (by omega), ← BitVec.ofNat_add]
    simp only [s41, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h40', bv64_shl, show (11#6 : BitVec 6).toNat = 11 from rfl, tailBufBase]
    congr 1
  have hx17_val : s43.getReg .x17 = negCnt 0 := by
    simp only [s43, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      show s42.getReg .x0 = 0#64 from rfl, BitVec.zero_add,
      show (4032#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 64) from rfl,
      signExtend12_neg 64 (by omega) (by omega), negCnt, Nat.add_zero]
  have hx18_val : s46.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952) := by
    have h44' : s44.getReg .x6 = BitVec.ofNat 64 (4096 * 262144) := by
      simp [s44, lui_ofNat_nonneg 262144 (by omega)]
    have h45' : s45.getReg .x6 = BitVec.ofNat 64 1073742952 := by
      simp only [s45, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        h44', signExtend12_nonneg 1128 (by omega), ← BitVec.ofNat_add]
    have h45_9 : s45.getReg .x9 = BitVec.ofNat 64 4294971424 := by
      simp [s45, s44, s43, s42, s41, s40, s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, getReg_setReg_ne', hx9]
    simp only [s46, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h45_9, h45', ← BitVec.ofNat_add]
  have hlb_eq : ∀ l, 1 ≤ l → l ≤ 23 →
      s.getMem (BitVec.ofNat 64 (8 * l)) = BitVec.ofNat 64 (4294971424 + levelBase l) := hbt.lvlBase
  refine ⟨s59, hrun, rfl, fun a => by simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, hmem48],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 8 (by omega),
      show s.getMem (BitVec.ofNat 64 8) = _ from hlb_eq 1 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 16 (by omega),
      show s.getMem (BitVec.ofNat 64 16) = _ from hlb_eq 2 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 88 (by omega),
      show s.getMem (BitVec.ofNat 64 88) = _ from hlb_eq 11 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, getReg_setReg_ne',
      show s.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1 (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 80 (by omega),
      show s.getMem (BitVec.ofNat 64 80) = _ from hlb_eq 10 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, getReg_setReg_ne', hx9]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, s35, s34, s33, getReg_setReg_ne', hx11_val]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, s35, s34, s33, getReg_setReg_ne', show s32.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 0 (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, getReg_setReg_ne', hx13_val]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 24 (by omega),
      show s.getMem (BitVec.ofNat 64 24) = _ from hlb_eq 3 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, getReg_setReg_ne', hx15_val]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, getReg_setReg_ne',
      show s41.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 0 (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, getReg_setReg_ne', hx17_val]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, getReg_setReg_ne', hx18_val]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, getReg_setReg_ne',
      show s46.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1364 (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, getReg_setReg_ne',
      show s47.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 3 (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 32 (by omega),
      show s.getMem (BitVec.ofNat 64 32) = _ from hlb_eq 4 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 72 (by omega),
      show s.getMem (BitVec.ofNat 64 72) = _ from hlb_eq 9 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, getReg_setReg_ne']
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, getReg_setReg_ne']
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 40 (by omega),
      show s.getMem (BitVec.ofNat 64 40) = _ from hlb_eq 5 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, s48, s47, s46, s45, s44, s43, s42, s41, s40,
      s39, s38, s37, s36, s35, s34, s33, s32, s31, s30, s29, getReg_setReg_ne']
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 48 (by omega),
      show s.getMem (BitVec.ofNat 64 48) = _ from hlb_eq 6 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 56 (by omega),
      show s.getMem (BitVec.ofNat 64 56) = _ from hlb_eq 7 (by omega) (by omega)]
  · simp [s59, s58, s57, s56, s55, s54, s53, s52, s51, s50, s49, getReg_setReg_ne', hmem48,
      show s48.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 64 (by omega),
      show s.getMem (BitVec.ofNat 64 64) = _ from hlb_eq 8 (by omega) (by omega)]

/-- Non-empty batch (`positions.card > 0`): exact `241` cycles to `PC_rec_r0 = 59`, initializing all
persistent registers, `BaseTableReady`, `CapMarks15State ... 0`, `SlowTablesState ... false`,
`WriterState ... ⟨0, _⟩ false 0 0 []`, and `TailState ... [] 0`. -/
theorem openRuns_entry_nonzero (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hpos : 0 < positions.card) :
    let s0 := openSub.initialState .opening (trapdoor, positions)
    ∃ s : MachineState,
      OpenRuns s0 241 241 s ∧
      s.pc = pcAt PC_rec_r0 ∧
      s.getReg .x1 = BitVec.ofNat 64 (4294971424 + levelBase 1) ∧
      s.getReg .x2 = BitVec.ofNat 64 (4294971424 + levelBase 2) ∧
      s.getReg .x3 = BitVec.ofNat 64 (4294971424 + levelBase 11) ∧
      s.getReg .x4 = 1#64 ∧
      s.getReg .x7 = BitVec.ofNat 64 (4294971424 + levelBase 10) ∧
      s.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s.getReg .x11 = mask40Word ∧
      s.getReg .x13 = BitVec.ofNat 64 5592064 ∧
      s.getReg .x14 = BitVec.ofNat 64 (4294971424 + levelBase 3) ∧
      s.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952) ∧
      s.getReg .x19 = BitVec.ofNat 64 1364 ∧
      s.getReg .x20 = BitVec.ofNat 64 3 ∧
      s.getReg .x21 = BitVec.ofNat 64 (4294971424 + levelBase 4) ∧
      s.getReg .x23 = BitVec.ofNat 64 (4294971424 + levelBase 9) ∧
      s.getReg .x24 = BitVec.ofNat 64 6912218176 ∧
      s.getReg .x26 = BitVec.ofNat 64 (4294971424 + levelBase 5) ∧
      s.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card) ∧
      s.getReg .x29 = BitVec.ofNat 64 (4294971424 + levelBase 6) ∧
      s.getReg .x30 = BitVec.ofNat 64 (4294971424 + levelBase 7) ∧
      s.getReg .x31 = BitVec.ofNat 64 (4294971424 + levelBase 8) ∧
      ReadOnlyPreserved s0 s ∧
      BaseTableReady s ∧
      CapMarks15State s positions 0 ∧
      SlowTablesState s false ∧
      WriterState (CleanTrapdoor trapdoor) s ⟨0, by omega⟩ false 0 0 [] ∧
      TailState (CleanTrapdoor trapdoor) s [] 0 := by
  set s0 := openSub.initialState .opening (trapdoor, positions)
  have hs0_eq : s0 = submission.initialState .opening (trapdoor, positions) := openSub_init_eq trapdoor positions
  have hcard := positions_card_le' positions
  obtain ⟨hpc0', hx2', hx12', hx13', hx15', hx16'⟩ := opening_initial_regs trapdoor positions
  have hpc0 : s0.pc = pcAt 0 := by rw [hs0_eq]; exact hpc0'
  have hx2_0 : s0.getReg .x2 = BitVec.ofNat 64 68719475936 := by rw [hs0_eq]; exact hx2'
  have hx12_0 : s0.getReg .x12 = BitVec.ofNat 64 4294971424 := by rw [hs0_eq]; exact hx12'
  have hx13_0 : s0.getReg .x13 = BitVec.ofNat 64 6912218176 := by rw [hs0_eq]; exact hx13'
  have hx15_0 : s0.getReg .x15 = BitVec.ofNat 64 11341403200 := by rw [hs0_eq]; exact hx15'
  have hx16_0 : s0.getReg .x16 = BitVec.ofNat 64 positions.card := by rw [hs0_eq]; exact hx16'
  have hne16 : s0.getReg .x16 ≠ s0.getReg .x0 := by
    rw [hx16_0]; intro h; have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : positions.card < 2 ^ 64),
      show (s0.getReg .x0).toNat = 0 from rfl] at hn; omega
  have hbr0 : pcAt 0 + signExtend13 (20#13) = pcAt 5 := by
    simpa only [show 4 * (5 - 0) = 20 by decide] using pcAt_add_pos13 0 5 (by omega) (by omega)
  have h0 := step_BNE_taken (s := s0) (by decide) hpc0 (rfl : openInstr 0 = .base (.BNE .x16 .x0 (20#13))) hne16 hbr0
  set t1 := s0.setPC (pcAt 5)
  have h5 := step_ADDI (s := t1) (by decide) rfl (rfl : openInstr 5 = .base (.ADDI .x9 .x12 (0#12)))
  set t2 := (t1.setReg .x9 (t1.getReg .x12 + signExtend12 (0#12))).setPC (pcAt 6)
  have h6 := step_ADDI (s := t2) (by decide) rfl (rfl : openInstr 6 = .base (.ADDI .x24 .x13 (0#12)))
  set t3 := (t2.setReg .x24 (t2.getReg .x13 + signExtend12 (0#12))).setPC (pcAt 7)
  have h7 := step_SLLI (s := t3) (by decide) rfl (rfl : openInstr 7 = .base (.SLLI .x27 .x16 (3#6)))
  set t4 := (t3.setReg .x27 (t3.getReg .x16 <<< (3#6).toNat)).setPC (pcAt 8)
  have h8 := step_ADD (s := t4) (by decide) rfl (rfl : openInstr 8 = .base (.ADD .x27 .x24 .x27))
  set t5 := (t4.setReg .x27 (t4.getReg .x24 + t4.getReg .x27)).setPC (pcAt 9)
  have h9 := step_ADDI (s := t5) (by decide) rfl (rfl : openInstr 9 = .base (.ADDI .x25 .x15 (0#12)))
  set t6 := (t5.setReg .x25 (t5.getReg .x15 + signExtend12 (0#12))).setPC (pcAt 10)
  have h10 := step_ADDI (s := t6) (by decide) rfl (rfl : openInstr 10 = .base (.ADDI .x5 .x2 (32#12)))
  set t7 := (t6.setReg .x5 (t6.getReg .x2 + signExtend12 (32#12))).setPC (pcAt 11)
  have h11 := step_ADDI (s := t7) (by decide) rfl (rfl : openInstr 11 = .base (.ADDI .x6 .x0 (8#12)))
  set t8 := (t7.setReg .x6 (t7.getReg .x0 + signExtend12 (8#12))).setPC (pcAt 12)
  have h12 := step_ADDI (s := t8) (by decide) rfl (rfl : openInstr 12 = .base (.ADDI .x7 .x0 (192#12)))
  set t9 := (t8.setReg .x7 (t8.getReg .x0 + signExtend12 (192#12))).setPC (pcAt 13)
  have hpre : OpenRuns s0 9 9 t9 := (((((((h0.trans h5).trans h6).trans h7).trans h8).trans h9).trans h10).trans h11).trans h12
  have ht9_x9 : t9.getReg .x9 = BitVec.ofNat 64 4294971424 := by
    simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, getReg_setReg_ne', hx12_0, signExtend12_nonneg 0 (by omega)]
  have ht9_x2 : t9.getReg .x2 = BitVec.ofNat 64 68719475936 := by
    simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, getReg_setReg_ne', hx2_0]
  have ht9_x24 : t9.getReg .x24 = BitVec.ofNat 64 6912218176 := by
    simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, getReg_setReg_ne', hx13_0, signExtend12_nonneg 0 (by omega)]
  have ht9_x25 : t9.getReg .x25 = BitVec.ofNat 64 11341403200 := by
    simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, getReg_setReg_ne', hx15_0, signExtend12_nonneg 0 (by omega)]
  have ht9_x27 : t9.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card) := by
    have ht4_27 : t4.getReg .x27 = BitVec.ofNat 64 (positions.card * 8) := by
      simp [t4, t3, t2, t1, getReg_setReg_ne', hx16_0, bv64_shl]
    have ht4_24 : t4.getReg .x24 = BitVec.ofNat 64 6912218176 := by
      simp [t4, t3, t2, t1, getReg_setReg_ne', hx13_0, signExtend12_nonneg 0 (by omega)]
    simp only [t9, t8, t7, t6, t5, MachineState.getReg_setPC, getReg_setReg_ne',
      MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, ht4_24, ht4_27, ← BitVec.ofNat_add]
    congr 1; omega
  obtain ⟨s19, hr19, hpc19, hregs19, hro19, hbase19, hzero19⟩ := openRuns_init_base_loop 23 (by omega) t9 rfl
    ht9_x9
    (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, getReg_setReg_ne', hx2_0, signExtend12_nonneg 32 (by omega), ← BitVec.ofNat_add])
    (by simp [t9, t8, t7, getReg_setReg_ne', show t7.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 8 (by omega)])
    (by simp [t9, show t8.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 192 (by omega)])
    (fun a _ => by simp only [t9, t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg]; rfl)
    (fun l h1 h2 => by omega)
    (fun a hal _ h2 => by
      simp only [t9, t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact opening_initial_zero_dword trapdoor positions a hal h2)
    (by omega)
  have h19 := step_ADDI (s := s19) (by decide) hpc19 (rfl : openInstr 19 = .base (.ADDI .x5 .x2 (496#12)))
  set s20 := (s19.setReg .x5 (s19.getReg .x2 + signExtend12 (496#12))).setPC (pcAt 20)
  have h20 := step_ADDI (s := s20) (by decide) rfl (rfl : openInstr 20 = .base (.ADDI .x6 .x0 (376#12)))
  set s21 := (s20.setReg .x6 (s20.getReg .x0 + signExtend12 (376#12))).setPC (pcAt 21)
  have h21 := step_ADDI (s := s21) (by decide) rfl (rfl : openInstr 21 = .base (.ADDI .x7 .x0 (456#12)))
  set s22 := (s21.setReg .x7 (s21.getReg .x0 + signExtend12 (456#12))).setPC (pcAt 22)
  have hs19_x2 : s19.getReg .x2 = BitVec.ofNat 64 68719475936 := (hregs19 .x2 (by simp)).trans ht9_x2
  obtain ⟨s28, hr28, hpc28, hregs28, hro28, hbt28, hzero28⟩ := openRuns_init_cm_loop 10 (by omega) s22 rfl
    (by simp [s22, s21, s20, getReg_setReg_ne', hs19_x2, signExtend12_nonneg 496 (by omega), ← BitVec.ofNat_add])
    (by simp [s22, s21, getReg_setReg_ne', show s20.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 376 (by omega)])
    (by simp [s22, show s21.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 456 (by omega)])
    (fun a ha => (by simp [s22, s21, s20] : s22.getMem a = s19.getMem a).trans (hro19 a ha))
    (fun l h1 h2 => (by simp [s22, s21, s20] : s22.getMem _ = s19.getMem _).trans (hbase19 l h1 h2))
    (fun l h1 h2 => by omega)
    (fun a hal h1 h2 => (by simp [s22, s21, s20] : s22.getMem a = s19.getMem a).trans (hzero19 a hal (by omega) h2))
    (by omega)
  have hs28_x9 : s28.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (hregs28 .x9 (by simp)).trans ((by simp [s22, s21, s20, getReg_setReg_ne'] : s22.getReg .x9 = s19.getReg .x9).trans
      ((hregs19 .x9 (by simp)).trans ht9_x9))
  have hs28_x24 : s28.getReg .x24 = BitVec.ofNat 64 6912218176 :=
    (hregs28 .x24 (by simp)).trans ((by simp [s22, s21, s20, getReg_setReg_ne'] : s22.getReg .x24 = s19.getReg .x24).trans
      ((hregs19 .x24 (by simp)).trans ht9_x24))
  have hs28_x25 : s28.getReg .x25 = BitVec.ofNat 64 11341403200 :=
    (hregs28 .x25 (by simp)).trans ((by simp [s22, s21, s20, getReg_setReg_ne'] : s22.getReg .x25 = s19.getReg .x25).trans
      ((hregs19 .x25 (by simp)).trans ht9_x25))
  have hs28_x27 : s28.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card) :=
    (hregs28 .x27 (by simp)).trans ((by simp [s22, s21, s20, getReg_setReg_ne'] : s22.getReg .x27 = s19.getReg .x27).trans
      ((hregs19 .x27 (by simp)).trans ht9_x27))
  obtain ⟨s59, hr59, hpc59, hmem59, rx1, rx2, rx3, rx4, rx7, rx9, rx11, _, rx13, rx14, rx15, rx16, rx17,
    rx18, rx19, rx20, rx21, rx23, rx24, rx25, rx26, rx27, rx29, rx30, rx31⟩ :=
    openRuns_entry_regs hpc28 hs28_x9 hbt28
  have htot : OpenRuns s0 241 241 s59 := by
    have h := ((((hpre.trans hr19).trans ((h19.trans h20).trans h21)).trans hr28).trans hr59)
    simpa only [show 9 + 6 * 23 + (1 + 1 + 1) + 6 * 10 + 31 = 241 by decide] using h
  have hzero59 : ∀ a : Word, a.toNat % 8 = 0 → 512 ≤ a.toNat → a.toNat < 4096 → s59.getMem a = 0#64 :=
    fun a hal h1 h2 => (hmem59 a).trans (hzero28 a hal h1 h2)
  have hbyte0 : ∀ q, 512 ≤ q → q < 1344 → s59.getByte (BitVec.ofNat 64 q) = 0#8 := by
    intro q h1 h2
    simp only [MachineState.getByte]
    have hal := alignToDword_ofNat_eq (8 * (q / 8)) (q % 8) (by omega) (by omega)
    rw [show 8 * (q / 8) + q % 8 = q by omega] at hal
    have hq_toNat : (BitVec.ofNat 64 (8 * (q / 8))).toNat = 8 * (q / 8) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hal, hzero59 (BitVec.ofNat 64 (8 * (q / 8))) (by rw [hq_toNat]; omega)
      (by rw [hq_toNat]; omega) (by rw [hq_toNat]; omega)]
    unfold extractByte; simp
  refine ⟨s59, htot, hpc59, rx1, rx2, rx3, rx4, rx7, rx9, rx11, rx13, rx14, rx18, rx19, rx20, rx21,
    rx23, rx24.trans hs28_x24, rx26, rx27.trans hs28_x27, rx29, rx30, rx31,
    fun a ha => (hmem59 a).trans (hro28 a ha),
    baseTableReady_of_lowEq hbt28 (fun a _ => hmem59 a),
    ⟨fun c hc => by simp [capMark15Prefix, hbyte0 (512 + c) (by omega) (by omega)],
     fun q h1 h2 => hbyte0 q (by omega) h2⟩,
    by unfold SlowTablesState; simp only [Bool.false_eq_true, ↓reduceIte]; exact hzero59 _ (by decide) (by decide) (by decide),
    ⟨by omega, by omega, by simp, by omega, by simpa using rx25.trans hs28_x25, by simp,
     fun _ _ hj => by omega, fun _ => by simp⟩,
    ⟨by simp, by omega, by simpa using rx15, by simpa using rx17, fun _ => ⟨0, by decide, by simpa using rx16, by simp [bytesToNat, bitsOf6]⟩⟩⟩

/-! ### 5. Shared Address Computation Sub-Blocks -/

def saltAddrCode : List Instruction :=
  [.base (.LD .x8 .x24 (0#12)),
   .base (.SRLI .x6 .x8 (1#6)),
   .base (.SLLI .x28 .x6 (7#6)),
   .base (.SLLI .x10 .x6 (6#6)),
   .base (.ADD .x28 .x28 .x10),
   .base (.SLLI .x10 .x6 (3#6)),
   .base (.SUB .x28 .x28 .x10),
   .base (.ANDI .x6 .x8 (1#12)),
   .base (.SLLI .x6 .x6 (4#6)),
   .base (.ADD .x28 .x28 .x6),
   .base (.ADD .x10 .x18 .x28)]

theorem openRuns_salt_addr {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {pc ordinal : Nat}
    (hcode : CodeAt pc saltAddrCode)
    (hpc : s.pc = pcAt pc)
    (hord : ordinal < positions.card)
    (hx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * ordinal))
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    ∃ s' : MachineState,
      OpenRuns s 11 11 s' ∧
      s'.pc = pcAt (pc + 11) ∧
      s'.getReg .x8 = BitVec.ofNat 64 i.val ∧
      s'.getReg .x10 = BitVec.ofNat 64 (4294971424 + saltOff i) ∧
      RegsEqExcept [.x6, .x8, .x10, .x28] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  have hi_lt : i.val < 16777216 := i.isLt
  have hcard := positions_card_le' positions
  have hbd : pc + 11 ≤ OPEN_CODE_LEN := by have := hcode.1; simpa [saltAddrCode] using this
  have hi0 : openInstr pc = .base (.LD .x8 .x24 (0#12)) := by have h := hcode.2 0 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi1 : openInstr (pc + 1) = .base (.SRLI .x6 .x8 (1#6)) := by have h := hcode.2 1 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi2 : openInstr (pc + 2) = .base (.SLLI .x28 .x6 (7#6)) := by have h := hcode.2 2 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi3 : openInstr (pc + 3) = .base (.SLLI .x10 .x6 (6#6)) := by have h := hcode.2 3 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi4 : openInstr (pc + 4) = .base (.ADD .x28 .x28 .x10) := by have h := hcode.2 4 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi5 : openInstr (pc + 5) = .base (.SLLI .x10 .x6 (3#6)) := by have h := hcode.2 5 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi6 : openInstr (pc + 6) = .base (.SUB .x28 .x28 .x10) := by have h := hcode.2 6 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi7 : openInstr (pc + 7) = .base (.ANDI .x6 .x8 (1#12)) := by have h := hcode.2 7 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi8 : openInstr (pc + 8) = .base (.SLLI .x6 .x6 (4#6)) := by have h := hcode.2 8 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi9 : openInstr (pc + 9) = .base (.ADD .x28 .x28 .x6) := by have h := hcode.2 9 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hi10 : openInstr (pc + 10) = .base (.ADD .x10 .x18 .x28) := by have h := hcode.2 10 (by simp [saltAddrCode]); simpa [saltAddrCode] using h
  have hld_addr : s.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (6912218176 + 8 * ordinal) := by
    rw [hx24, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
  have hld_val : accessValid (s.getReg .x24 + signExtend12 (0#12)) 8 = true := by
    rw [hld_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
  have hs0 := step_LD (s := s) (by omega) hpc hi0 hld_val
  set s1 := (s.setReg .x8 (s.getMem (s.getReg .x24 + signExtend12 (0#12)))).setPC (pcAt (pc + 1))
  have hs1 := step_SRLI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x6 (s1.getReg .x8 >>> (1#6).toNat)).setPC (pcAt (pc + 1 + 1))
  have hs2 := step_SLLI (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x28 (s2.getReg .x6 <<< (7#6).toNat)).setPC (pcAt (pc + 2 + 1))
  have hs3 := step_SLLI (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg .x10 (s3.getReg .x6 <<< (6#6).toNat)).setPC (pcAt (pc + 3 + 1))
  have hs4 := step_ADD (s := s4) (by omega) (by congr 1) hi4
  set s5 := (s4.setReg .x28 (s4.getReg .x28 + s4.getReg .x10)).setPC (pcAt (pc + 4 + 1))
  have hs5 := step_SLLI (s := s5) (by omega) (by congr 1) hi5
  set s6 := (s5.setReg .x10 (s5.getReg .x6 <<< (3#6).toNat)).setPC (pcAt (pc + 5 + 1))
  have hs6 := step_SUB (s := s6) (by omega) (by congr 1) hi6
  set s7 := (s6.setReg .x28 (s6.getReg .x28 - s6.getReg .x10)).setPC (pcAt (pc + 6 + 1))
  have hs7 := step_ANDI (s := s7) (by omega) (by congr 1) hi7
  set s8 := (s7.setReg .x6 (s7.getReg .x8 &&& signExtend12 (1#12))).setPC (pcAt (pc + 7 + 1))
  have hs8 := step_SLLI (s := s8) (by omega) (by congr 1) hi8
  set s9 := (s8.setReg .x6 (s8.getReg .x6 <<< (4#6).toNat)).setPC (pcAt (pc + 8 + 1))
  have hs9 := step_ADD (s := s9) (by omega) (by congr 1) hi9
  set s10 := (s9.setReg .x28 (s9.getReg .x28 + s9.getReg .x6)).setPC (pcAt (pc + 9 + 1))
  have hs10 := step_ADD (s := s10) (by omega) (by congr 1) hi10
  set s11 := (s10.setReg .x10 (s10.getReg .x18 + s10.getReg .x28)).setPC (pcAt (pc + 10 + 1))
  have hx8_1 : s1.getReg .x8 = BitVec.ofNat 64 i.val := by
    have hidx : openingIndex positions ordinal = i.val := by
      unfold openingIndex; simp [hord, i]
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hld_addr, readOnly_getMem_index' hro ordinal hord, hidx]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (i.val / 2) := by
    simp only [s2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hx8_1, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr i.val 1 (by omega),
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hx28_7 : s7.getReg .x28 = BitVec.ofNat 64 (184 * (i.val / 2)) := by
    have h3' : s3.getReg .x28 = BitVec.ofNat 64 (i.val / 2 * 128) := by simp [s3, hx6_2, bv64_shl]
    have h4' : s4.getReg .x10 = BitVec.ofNat 64 (i.val / 2 * 64) := by simp [s4, s3, getReg_setReg_ne', hx6_2, bv64_shl]
    have h5' : s5.getReg .x28 = BitVec.ofNat 64 (i.val / 2 * 192) := by
      simp only [s5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        show s4.getReg .x28 = s3.getReg .x28 by simp [s4, getReg_setReg_ne'], h3', h4', ← BitVec.ofNat_add]
      congr 1; omega
    have h6' : s6.getReg .x10 = BitVec.ofNat 64 (i.val / 2 * 8) := by
      simp [s6, s5, s4, s3, getReg_setReg_ne', hx6_2, bv64_shl]
    simp only [s7, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      show s6.getReg .x28 = s5.getReg .x28 by simp [s6, getReg_setReg_ne'], h5', h6',
      bv64_ofNat_sub (i.val / 2 * 192) (i.val / 2 * 8) (by omega)]
    congr 1; omega
  have hx6_9 : s9.getReg .x6 = BitVec.ofNat 64 (16 * (i.val % 2)) := by
    have h8' : s8.getReg .x6 = BitVec.ofNat 64 (i.val % 2) := by
      simp only [s8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        show s7.getReg .x8 = s1.getReg .x8 by simp [s7, s6, s5, s4, s3, s2, getReg_setReg_ne'],
        hx8_1, bv64_and1 i.val (by omega)]
    simp only [s9, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h8', bv64_shl, show (4#6 : BitVec 6).toNat = 4 from rfl]
    congr 1; omega
  refine ⟨s11, (((((((((hs0.trans hs1).trans hs2).trans hs3).trans hs4).trans hs5).trans hs6).trans hs7).trans hs8).trans hs9).trans hs10,
    by congr 1, ?_, ?_, ?_, fun _ => by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]⟩
  · simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, getReg_setReg_ne', hx8_1]
  · have h10_28 : s10.getReg .x28 = BitVec.ofNat 64 (184 * (i.val / 2) + 16 * (i.val % 2)) := by
      simp only [s10, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        show s9.getReg .x28 = s7.getReg .x28 by simp [s9, s8, getReg_setReg_ne'], hx28_7, hx6_9, ← BitVec.ofNat_add]
    have h10_18 : s10.getReg .x18 = BitVec.ofNat 64 (4294971424 + 1073742952) := by
      simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx18]
    simp only [s11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h10_18, h10_28, ← BitVec.ofNat_add, saltOff_formula' i]
    congr 1; omega
  · intro reg hreg
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      getReg_setReg_ne' .x10 reg h10'.symm, getReg_setReg_ne' .x28 reg h28'.symm,
      getReg_setReg_ne' .x6 reg h6'.symm, getReg_setReg_ne' .x8 reg h8'.symm]

def l0DivuCode : List Instruction :=
  [.base (.DIVU .x22 .x8 .x20),
   .base (.SLLI .x6 .x22 (1#6)),
   .base (.ADD .x6 .x6 .x22),
   .base (.SUB .x8 .x8 .x6)]

/-- Compute `x22 = i / 3`, `x6 = 3 * (i / 3)`, `x8 = i % 3` in `4` steps (`7` cycles). -/
theorem openRuns_l0_divu {s : MachineState} {pc : Nat} {i : Index}
    (hcode : CodeAt pc l0DivuCode)
    (hpc : s.pc = pcAt pc)
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 i.val)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 3) :
    ∃ s' : MachineState,
      OpenRuns s 4 7 s' ∧
      s'.pc = pcAt (pc + 4) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (i.val / 3) ∧
      s'.getReg .x6 = BitVec.ofNat 64 (3 * (i.val / 3)) ∧
      s'.getReg .x8 = BitVec.ofNat 64 (i.val % 3) ∧
      RegsEqExcept [.x6, .x8, .x22] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hi_lt : i.val < 16777216 := i.isLt
  have hbd : pc + 4 ≤ OPEN_CODE_LEN := by have := hcode.1; simpa [l0DivuCode] using this
  have hi0 : openInstr pc = .base (.DIVU .x22 .x8 .x20) := by have h := hcode.2 0 (by simp [l0DivuCode]); simpa [l0DivuCode] using h
  have hi1 : openInstr (pc + 1) = .base (.SLLI .x6 .x22 (1#6)) := by have h := hcode.2 1 (by simp [l0DivuCode]); simpa [l0DivuCode] using h
  have hi2 : openInstr (pc + 2) = .base (.ADD .x6 .x6 .x22) := by have h := hcode.2 2 (by simp [l0DivuCode]); simpa [l0DivuCode] using h
  have hi3 : openInstr (pc + 3) = .base (.SUB .x8 .x8 .x6) := by have h := hcode.2 3 (by simp [l0DivuCode]); simpa [l0DivuCode] using h
  have hs0 := step_DIVU (s := s) (by omega) hpc hi0
  set s1 := (s.setReg .x22 (rv64_divu (s.getReg .x8) (s.getReg .x20))).setPC (pcAt (pc + 1))
  have hs1 := step_SLLI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x6 (s1.getReg .x22 <<< (1#6).toNat)).setPC (pcAt (pc + 1 + 1))
  have hs2 := step_ADD (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x6 (s2.getReg .x6 + s2.getReg .x22)).setPC (pcAt (pc + 2 + 1))
  have hs3 := step_SUB (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg .x8 (s3.getReg .x8 - s3.getReg .x6)).setPC (pcAt (pc + 3 + 1))
  have hx22_1 : s1.getReg .x22 = BitVec.ofNat 64 (i.val / 3) := by
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hx8, hx20, show BitVec.ofNat 64 3 = 3#64 from rfl, rv64_divu_three,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i.val < 2 ^ 64)]
  have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (3 * (i.val / 3)) := by
    have h2' : s2.getReg .x6 = BitVec.ofNat 64 (i.val / 3 * 2) := by simp [s2, hx22_1, bv64_shl]
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h2', show s2.getReg .x22 = s1.getReg .x22 by simp [s2, getReg_setReg_ne'], hx22_1, ← BitVec.ofNat_add]
    congr 1; omega
  refine ⟨s4, ((hs0.trans hs1).trans hs2).trans hs3, by congr 1, ?_, ?_, ?_, ?_, fun _ => by simp [s4, s3, s2, s1]⟩
  · simp [s4, s3, s2, getReg_setReg_ne', hx22_1]
  · simp [s4, getReg_setReg_ne', hx6_3]
  · have h3_8 : s3.getReg .x8 = BitVec.ofNat 64 i.val := by simp [s3, s2, s1, getReg_setReg_ne', hx8]
    simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h3_8, hx6_3, bv64_ofNat_sub i.val (3 * (i.val / 3)) (by omega)]
    congr 1; omega
  · intro reg hreg
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    simp [s4, s3, s2, s1, getReg_setReg_ne' .x8 reg h8'.symm,
      getReg_setReg_ne' .x6 reg h6'.symm, getReg_setReg_ne' .x22 reg h22'.symm]

def l0SibsCode : List Instruction :=
  [.base (.SLLI .x28 .x6 (5#6)),
   .base (.ADD .x10 .x9 .x28),
   .base (.ADDI .x28 .x10 (64#12)),
   .base (.BNE .x8 .x0 (12#13)),
   .base (.ADDI .x10 .x10 (32#12)),
   .base (.JAL .x0 (12#21)),
   .base (.BEQ .x8 .x4 (8#13)),
   .base (.ADDI .x28 .x10 (32#12))]

def l0Sib1Idx (i : Index) : Nat := if i.val % 3 = 0 then 3 * (i.val / 3) + 1 else 3 * (i.val / 3)
def l0Sib2Idx (i : Index) : Nat := if i.val % 3 = 2 then 3 * (i.val / 3) + 1 else 3 * (i.val / 3) + 2

/-- Resolve the two `L0` sibling node addresses into `(x10, x28)` in `≤ 6` cycles. -/
theorem openRuns_l0_sibs {s : MachineState} {pc : Nat} {i : Index}
    (hcode : CodeAt pc l0SibsCode)
    (hpc : s.pc = pcAt pc)
    (hx4 : s.getReg .x4 = 1#64)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (3 * (i.val / 3)))
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 (i.val % 3))
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424) :
    ∃ cyc s',
      OpenRuns s cyc cyc s' ∧
      cyc ≤ 6 ∧
      s'.pc = pcAt (pc + 8) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 0 + nodeOffset 0 (l0Sib1Idx i)) ∧
      s'.getReg .x28 = BitVec.ofNat 64 (4294971424 + levelBase 0 + nodeOffset 0 (l0Sib2Idx i)) ∧
      RegsEqExcept [.x10, .x28] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hbd : pc + 8 ≤ OPEN_CODE_LEN := by have := hcode.1; simpa [l0SibsCode] using this
  have hi0 : openInstr pc = .base (.SLLI .x28 .x6 (5#6)) := by have h := hcode.2 0 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hi1 : openInstr (pc + 1) = .base (.ADD .x10 .x9 .x28) := by have h := hcode.2 1 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hi2 : openInstr (pc + 2) = .base (.ADDI .x28 .x10 (64#12)) := by have h := hcode.2 2 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hi3 : openInstr (pc + 3) = .base (.BNE .x8 .x0 (12#13)) := by have h := hcode.2 3 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hi4 : openInstr (pc + 4) = .base (.ADDI .x10 .x10 (32#12)) := by have h := hcode.2 4 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hi5 : openInstr (pc + 5) = .base (.JAL .x0 (12#21)) := by have h := hcode.2 5 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hi6 : openInstr (pc + 6) = .base (.BEQ .x8 .x4 (8#13)) := by have h := hcode.2 6 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hi7 : openInstr (pc + 7) = .base (.ADDI .x28 .x10 (32#12)) := by have h := hcode.2 7 (by simp [l0SibsCode]); simpa [l0SibsCode] using h
  have hs0 := step_SLLI (s := s) (by omega) hpc hi0
  set s1 := (s.setReg .x28 (s.getReg .x6 <<< (5#6).toNat)).setPC (pcAt (pc + 1))
  have hs1 := step_ADD (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x10 (s1.getReg .x9 + s1.getReg .x28)).setPC (pcAt (pc + 1 + 1))
  have hs2 := step_ADDI (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x28 (s2.getReg .x10 + signExtend12 (64#12))).setPC (pcAt (pc + 2 + 1))
  have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + 96 * (i.val / 3)) := by
    have h1' : s1.getReg .x28 = BitVec.ofNat 64 (3 * (i.val / 3) * 32) := by simp [s1, hx6, bv64_shl]
    simp only [s2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      show s1.getReg .x9 = s.getReg .x9 by simp [s1, getReg_setReg_ne'], hx9, h1', ← BitVec.ofNat_add]
    congr 1; omega
  have hx10_3 : s3.getReg .x10 = BitVec.ofNat 64 (4294971424 + 96 * (i.val / 3)) := by
    simp [s3, getReg_setReg_ne', hx10_2]
  have hx28_3 : s3.getReg .x28 = BitVec.ofNat 64 (4294971424 + 96 * (i.val / 3) + 64) := by
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hx10_2, signExtend12_nonneg 64 (by omega), ← BitVec.ofNat_add]
  have hx8_3 : s3.getReg .x8 = BitVec.ofNat 64 (i.val % 3) := by simp [s3, s2, s1, getReg_setReg_ne', hx8]
  have hx4_3 : s3.getReg .x4 = 1#64 := by simp [s3, s2, s1, getReg_setReg_ne', hx4]
  have hregs3 : RegsEqExcept [.x10, .x28] s s3 := by
    intro reg hreg
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    simp [s3, s2, s1, getReg_setReg_ne' .x28 reg h28'.symm, getReg_setReg_ne' .x10 reg h10'.symm]
  have hrem_lt : i.val % 3 < 3 := Nat.mod_lt _ (by omega)
  generalize hrv : i.val % 3 = rv at hrem_lt hx8_3
  have hno : ∀ k, levelBase 0 + nodeOffset 0 k = 32 * k := fun k => by unfold levelBase nodeOffset; simp
  interval_cases rv
  · have h3 := step_BNE_not_taken (s := s3) (by omega) (by congr 1) hi3 (by rw [hx8_3]; rfl)
    set s4 := s3.setPC (pcAt (pc + 3 + 1))
    have h4 := step_ADDI (s := s4) (by omega) (by congr 1) hi4
    set s5 := (s4.setReg .x10 (s4.getReg .x10 + signExtend12 (32#12))).setPC (pcAt (pc + 4 + 1))
    have hjal_tgt : pcAt (pc + 5) + signExtend21 (12#21) = pcAt (pc + 8) := by
      simpa only [show 4 * (pc + 8 - (pc + 5)) = 12 by omega] using pcAt_add_pos21 (pc + 5) (pc + 8) (by omega) (by omega)
    have h5 := step_JAL (s := s5) (by omega) (by congr 1) hi5 hjal_tgt
    set s6 := (s5.setReg .x0 (pcAt (pc + 5 + 1))).setPC (pcAt (pc + 8))
    refine ⟨6, s6, ((((hs0.trans hs1).trans hs2).trans h3).trans h4).trans h5, by omega, rfl, ?_, ?_, ?_, fun _ => by simp [s6, s5, s4, s3, s2, s1]⟩
    · simp only [s6, s5, s4, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        hx10_3, signExtend12_nonneg 32 (by omega), ← BitVec.ofNat_add, l0Sib1Idx, hrv, ↓reduceIte, Nat.add_assoc, hno]
      congr 1; omega
    · simp only [s6, s5, s4, MachineState.getReg_setPC, getReg_setReg_ne', ne_eq, reduceCtorEq, not_false_eq_true, hx28_3, l0Sib2Idx, hrv,
        show ¬ ((0 : Nat) = 2) by omega, ↓reduceIte, Nat.add_assoc, hno]
      congr 1; omega
    · intro reg hreg
      have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
      have h0 : s6.getReg reg = s5.getReg reg := by cases reg <;> simp [s6, setReg_x0_eq]
      exact h0.trans ((by simp [s5, s4, getReg_setReg_ne' .x10 reg h10'.symm] : s5.getReg reg = s3.getReg reg).trans (hregs3 reg hreg))
  · have hne : s3.getReg .x8 ≠ s3.getReg .x0 := by rw [hx8_3, show s3.getReg .x0 = 0#64 from rfl]; decide
    have hbr3 : pcAt (pc + 3) + signExtend13 (12#13) = pcAt (pc + 6) := by
      simpa only [show 4 * (pc + 6 - (pc + 3)) = 12 by omega] using pcAt_add_pos13 (pc + 3) (pc + 6) (by omega) (by omega)
    have h3 := step_BNE_taken (s := s3) (by omega) (by congr 1) hi3 hne hbr3
    set s4 := s3.setPC (pcAt (pc + 6))
    have hbr6 : pcAt (pc + 6) + signExtend13 (8#13) = pcAt (pc + 8) := by
      simpa only [show 4 * (pc + 8 - (pc + 6)) = 8 by omega] using pcAt_add_pos13 (pc + 6) (pc + 8) (by omega) (by omega)
    have h4 := step_BEQ_taken (s := s4) (by omega) rfl hi6 (by simp [s4, hx8_3, hx4_3]) hbr6
    set s5 := s4.setPC (pcAt (pc + 8))
    refine ⟨5, s5, (((hs0.trans hs1).trans hs2).trans h3).trans h4, by omega, rfl, ?_, ?_,
      fun r hr => (by simp [s5, s4] : s5.getReg r = s3.getReg r).trans (hregs3 r hr),
      fun _ => by simp [s5, s4, s3, s2, s1]⟩
    · simp only [s5, s4, MachineState.getReg_setPC, hx10_3, l0Sib1Idx, hrv, show ¬ ((1 : Nat) = 0) by omega, ↓reduceIte, Nat.add_assoc, hno]
      congr 1; omega
    · simp only [s5, s4, MachineState.getReg_setPC, hx28_3, l0Sib2Idx, hrv, show ¬ ((1 : Nat) = 2) by omega, ↓reduceIte, Nat.add_assoc, hno]
      congr 1; omega
  · have hne : s3.getReg .x8 ≠ s3.getReg .x0 := by rw [hx8_3, show s3.getReg .x0 = 0#64 from rfl]; decide
    have hbr3 : pcAt (pc + 3) + signExtend13 (12#13) = pcAt (pc + 6) := by
      simpa only [show 4 * (pc + 6 - (pc + 3)) = 12 by omega] using pcAt_add_pos13 (pc + 3) (pc + 6) (by omega) (by omega)
    have h3 := step_BNE_taken (s := s3) (by omega) (by congr 1) hi3 hne hbr3
    set s4 := s3.setPC (pcAt (pc + 6))
    have hne4 : s4.getReg .x8 ≠ s4.getReg .x4 := by simp [s4, hx8_3, hx4_3]
    have h4 := step_BEQ_not_taken (s := s4) (by omega) rfl hi6 hne4
    set s5 := s4.setPC (pcAt (pc + 6 + 1))
    have h5 := step_ADDI (s := s5) (by omega) (by congr 1) hi7
    set s6 := (s5.setReg .x28 (s5.getReg .x10 + signExtend12 (32#12))).setPC (pcAt (pc + 7 + 1))
    refine ⟨6, s6, ((((hs0.trans hs1).trans hs2).trans h3).trans h4).trans h5, by omega, by congr 1, ?_, ?_, ?_, fun _ => by simp [s6, s5, s4, s3, s2, s1]⟩
    · simp only [s6, s5, s4, MachineState.getReg_setPC, getReg_setReg_ne', ne_eq, reduceCtorEq, not_false_eq_true, hx10_3, l0Sib1Idx, hrv,
        show ¬ ((2 : Nat) = 0) by omega, ↓reduceIte, Nat.add_assoc, hno]
      congr 1; omega
    · simp only [s6, s5, s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        hx10_3, signExtend12_nonneg 32 (by omega), ← BitVec.ofNat_add, l0Sib2Idx, hrv, ↓reduceIte, Nat.add_assoc, hno]
      congr 1; omega
    · intro reg hreg
      have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
      exact (by simp [s6, s5, s4, getReg_setReg_ne' .x28 reg h28'.symm] : s6.getReg reg = s3.getReg reg).trans (hregs3 reg hreg)

/-- Binary-level sibling address computation using a cached `baseReg` (`5` cycles). -/
def lvlAddrRegCode (dstReg baseReg : Reg) : List Instruction :=
  [.base (.XORI .x28 .x22 (1#12)),
   .base (.SRLI .x22 .x22 (1#6)),
   .base (.ADD .x28 .x28 .x22),
   .base (.SLLI .x28 .x28 (5#6)),
   .base (.ADD dstReg baseReg .x28)]

/-- Binary-level sibling address computation reading `base(l)` from scratch `[8*l]` (`6` cycles). -/
def lvlAddrMemCode (dstReg : Reg) (l : Nat) : List Instruction :=
  [.base (.XORI .x28 .x22 (1#12)),
   .base (.SRLI .x22 .x22 (1#6)),
   .base (.ADD .x28 .x28 .x22),
   .base (.SLLI .x28 .x28 (5#6)),
   .base (.LD dstReg .x0 (BitVec.ofNat 12 (8 * l))),
   .base (.ADD dstReg dstReg .x28)]

theorem nodeOffset_bin (l idx : Nat) (hl : 1 ≤ l) :
    nodeOffset l (idx ^^^ 1) = 32 * ((idx ^^^ 1) + idx / 2) := by
  unfold nodeOffset gapOffset
  rw [if_neg (by omega)]
  have hdiv : (idx ^^^ 1) / 2 = idx / 2 := by
    rcases Nat.even_or_odd' idx with ⟨q, rfl | rfl⟩
    · rw [xor_one_even]; omega
    · rw [xor_one_odd]; omega
  rw [hdiv]

theorem openRuns_lvl_addr_reg {s : MachineState} {pc l idx : Nat} {dstReg baseReg : Reg}
    (hcode : CodeAt pc (lvlAddrRegCode dstReg baseReg))
    (hpc : s.pc = pcAt pc)
    (hl1 : 1 ≤ l) (hl23 : l ≤ 23) (hidx : idx < 16777216)
    (hdst_ne : dstReg ≠ .x0 ∧ dstReg ≠ .x22 ∧ dstReg ≠ .x28)
    (hbase_ne : baseReg ≠ .x22 ∧ baseReg ≠ .x28)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hbase : s.getReg baseReg = BitVec.ofNat 64 (4294971424 + levelBase l)) :
    ∃ s' : MachineState,
      OpenRuns s 5 5 s' ∧
      s'.pc = pcAt (pc + 5) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      s'.getReg dstReg = BitVec.ofNat 64 (4294971424 + levelBase l + nodeOffset l (idx ^^^ 1)) ∧
      RegsEqExcept [.x22, .x28, dstReg] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hbd : pc + 5 ≤ OPEN_CODE_LEN := by have := hcode.1; simpa [lvlAddrRegCode] using this
  have hi0 : openInstr pc = .base (.XORI .x28 .x22 (1#12)) := by have h := hcode.2 0 (by simp [lvlAddrRegCode]); simpa [lvlAddrRegCode] using h
  have hi1 : openInstr (pc + 1) = .base (.SRLI .x22 .x22 (1#6)) := by have h := hcode.2 1 (by simp [lvlAddrRegCode]); simpa [lvlAddrRegCode] using h
  have hi2 : openInstr (pc + 2) = .base (.ADD .x28 .x28 .x22) := by have h := hcode.2 2 (by simp [lvlAddrRegCode]); simpa [lvlAddrRegCode] using h
  have hi3 : openInstr (pc + 3) = .base (.SLLI .x28 .x28 (5#6)) := by have h := hcode.2 3 (by simp [lvlAddrRegCode]); simpa [lvlAddrRegCode] using h
  have hi4 : openInstr (pc + 4) = .base (.ADD dstReg baseReg .x28) := by have h := hcode.2 4 (by simp [lvlAddrRegCode]); simpa [lvlAddrRegCode] using h
  have hs0 := step_XORI (s := s) (by omega) hpc hi0
  set s1 := (s.setReg .x28 (s.getReg .x22 ^^^ signExtend12 (1#12))).setPC (pcAt (pc + 1))
  have hs1 := step_SRLI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x22 (s1.getReg .x22 >>> (1#6).toNat)).setPC (pcAt (pc + 1 + 1))
  have hs2 := step_ADD (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x28 (s2.getReg .x28 + s2.getReg .x22)).setPC (pcAt (pc + 2 + 1))
  have hs3 := step_SLLI (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg .x28 (s3.getReg .x28 <<< (5#6).toNat)).setPC (pcAt (pc + 3 + 1))
  have hs4 := step_ADD (s := s4) (by omega) (by congr 1) hi4
  set s5 := (s4.setReg dstReg (s4.getReg baseReg + s4.getReg .x28)).setPC (pcAt (pc + 4 + 1))
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 (idx ^^^ 1) := by
    simp [s1, hx22, bv64_xor1 idx (by omega)]
  have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 (idx / 2) := by
    simp only [s2, s1, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hx22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr idx 1 (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hx28_4 : s4.getReg .x28 = BitVec.ofNat 64 (nodeOffset l (idx ^^^ 1)) := by
    have h2_28 : s2.getReg .x28 = BitVec.ofNat 64 (idx ^^^ 1) := by simp [s2, getReg_setReg_ne', hx28_1]
    have h3' : s3.getReg .x28 = BitVec.ofNat 64 ((idx ^^^ 1) + idx / 2) := by
      simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        h2_28, hx22_2, ← BitVec.ofNat_add]
    simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h3', bv64_shl, show (5#6 : BitVec 6).toNat = 5 from rfl, nodeOffset_bin l idx hl1]
    congr 1; omega
  have hbase4 : s4.getReg baseReg = BitVec.ofNat 64 (4294971424 + levelBase l) := by
    simp [s4, s3, s2, s1, getReg_setReg_ne' .x28 baseReg hbase_ne.2.symm,
      getReg_setReg_ne' .x22 baseReg hbase_ne.1.symm, hbase]
  refine ⟨s5, (((hs0.trans hs1).trans hs2).trans hs3).trans hs4, by congr 1, ?_, ?_, ?_, fun _ => by simp [s5, s4, s3, s2, s1]⟩
  · simp [s5, s4, s3, getReg_setReg_ne' dstReg .x22 hdst_ne.2.1, getReg_setReg_ne', hx22_2]
  · simp only [s5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hdst_ne.1,
      hbase4, hx28_4, ← BitVec.ofNat_add]
  · intro reg hreg
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    have hd' : reg ≠ dstReg := fun h => hreg (by simp [h])
    simp [s5, s4, s3, s2, s1, getReg_setReg_ne' dstReg reg hd'.symm,
      getReg_setReg_ne' .x28 reg h28'.symm, getReg_setReg_ne' .x22 reg h22'.symm]

theorem openRuns_lvl_addr_mem {s : MachineState} {pc l idx : Nat} {dstReg : Reg}
    (hcode : CodeAt pc (lvlAddrMemCode dstReg l))
    (hpc : s.pc = pcAt pc)
    (hl1 : 1 ≤ l) (hl23 : l ≤ 23) (hidx : idx < 16777216)
    (hdst_ne : dstReg ≠ .x0 ∧ dstReg ≠ .x22 ∧ dstReg ≠ .x28)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hbt : BaseTableReady s) :
    ∃ s' : MachineState,
      OpenRuns s 6 6 s' ∧
      s'.pc = pcAt (pc + 6) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      s'.getReg dstReg = BitVec.ofNat 64 (4294971424 + levelBase l + nodeOffset l (idx ^^^ 1)) ∧
      RegsEqExcept [.x22, .x28, dstReg] s s' ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have hbd : pc + 6 ≤ OPEN_CODE_LEN := by have := hcode.1; simpa [lvlAddrMemCode] using this
  have hi0 : openInstr pc = .base (.XORI .x28 .x22 (1#12)) := by have h := hcode.2 0 (by simp [lvlAddrMemCode]); simpa [lvlAddrMemCode] using h
  have hi1 : openInstr (pc + 1) = .base (.SRLI .x22 .x22 (1#6)) := by have h := hcode.2 1 (by simp [lvlAddrMemCode]); simpa [lvlAddrMemCode] using h
  have hi2 : openInstr (pc + 2) = .base (.ADD .x28 .x28 .x22) := by have h := hcode.2 2 (by simp [lvlAddrMemCode]); simpa [lvlAddrMemCode] using h
  have hi3 : openInstr (pc + 3) = .base (.SLLI .x28 .x28 (5#6)) := by have h := hcode.2 3 (by simp [lvlAddrMemCode]); simpa [lvlAddrMemCode] using h
  have hi4 : openInstr (pc + 4) = .base (.LD dstReg .x0 (BitVec.ofNat 12 (8 * l))) := by have h := hcode.2 4 (by simp [lvlAddrMemCode]); simpa [lvlAddrMemCode] using h
  have hi5 : openInstr (pc + 5) = .base (.ADD dstReg dstReg .x28) := by have h := hcode.2 5 (by simp [lvlAddrMemCode]); simpa [lvlAddrMemCode] using h
  have hs0 := step_XORI (s := s) (by omega) hpc hi0
  set s1 := (s.setReg .x28 (s.getReg .x22 ^^^ signExtend12 (1#12))).setPC (pcAt (pc + 1))
  have hs1 := step_SRLI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x22 (s1.getReg .x22 >>> (1#6).toNat)).setPC (pcAt (pc + 1 + 1))
  have hs2 := step_ADD (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x28 (s2.getReg .x28 + s2.getReg .x22)).setPC (pcAt (pc + 2 + 1))
  have hs3 := step_SLLI (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg .x28 (s3.getReg .x28 <<< (5#6).toNat)).setPC (pcAt (pc + 3 + 1))
  have hld_val : accessValid (s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * l))) 8 = true := by
    rw [show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * l) (by omega), BitVec.zero_add]
    exact accessValid_ofNat (8 * l) 8 (by omega) (by omega)
  have hs4 := step_LD (s := s4) (by omega) (by congr 1) hi4 hld_val
  set s5 := (s4.setReg dstReg (s4.getMem (s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * l))))).setPC (pcAt (pc + 4 + 1))
  have hs5 := step_ADD (s := s5) (by omega) (by congr 1) hi5
  set s6 := (s5.setReg dstReg (s5.getReg dstReg + s5.getReg .x28)).setPC (pcAt (pc + 5 + 1))
  have hx28_1 : s1.getReg .x28 = BitVec.ofNat 64 (idx ^^^ 1) := by simp [s1, hx22, bv64_xor1 idx (by omega)]
  have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 (idx / 2) := by
    simp only [s2, s1, MachineState.getReg_setPC, getReg_setReg_ne', MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hx22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr idx 1 (by omega), Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hx28_4 : s4.getReg .x28 = BitVec.ofNat 64 (nodeOffset l (idx ^^^ 1)) := by
    have h2_28 : s2.getReg .x28 = BitVec.ofNat 64 (idx ^^^ 1) := by simp [s2, getReg_setReg_ne', hx28_1]
    have h3' : s3.getReg .x28 = BitVec.ofNat 64 ((idx ^^^ 1) + idx / 2) := by
      simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        h2_28, hx22_2, ← BitVec.ofNat_add]
    simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      h3', bv64_shl, show (5#6 : BitVec 6).toNat = 5 from rfl, nodeOffset_bin l idx hl1]
    congr 1; omega
  have hdst5 : s5.getReg dstReg = BitVec.ofNat 64 (4294971424 + levelBase l) := by
    simp only [s5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hdst_ne.1,
      show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * l) (by omega), BitVec.zero_add,
      show ∀ a, s4.getMem a = s.getMem a from fun a => by simp [s4, s3, s2, s1], hbt.lvlBase l hl1 hl23]
  refine ⟨s6, ((((hs0.trans hs1).trans hs2).trans hs3).trans hs4).trans hs5, by congr 1, ?_, ?_, ?_, fun _ => by simp [s6, s5, s4, s3, s2, s1]⟩
  · simp [s6, s5, s4, s3, getReg_setReg_ne' dstReg .x22 hdst_ne.2.1, getReg_setReg_ne', hx22_2]
  · simp only [s6, MachineState.getReg_setPC, MachineState.getReg_setReg_eq hdst_ne.1,
      hdst5, show s5.getReg .x28 = s4.getReg .x28 by simp [s5, getReg_setReg_ne' dstReg .x28 hdst_ne.2.2],
      hx28_4, ← BitVec.ofNat_add]
  · intro reg hreg
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    have hd' : reg ≠ dstReg := fun h => hreg (by simp [h])
    simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne' dstReg reg hd'.symm,
      getReg_setReg_ne' .x28 reg h28'.symm, getReg_setReg_ne' .x22 reg h22'.symm]

/-! ### 6. Record-Class Sibling Presence Arithmetic (`g = i.val / 3`) -/

private theorem levelSize_3 : levelSize 3 = 1398102 := by decide
private theorem levelSize_4 : levelSize 4 = 699051 := by decide
private theorem levelSize_6 : levelSize 6 = 174763 := by decide
private theorem levelSize_7 : levelSize 7 = 87382 := by decide
private theorem levelSize_8 : levelSize 8 = 43691 := by decide
private theorem levelSize_9 : levelSize 9 = 21846 := by decide
private theorem levelSize_10 : levelSize 10 = 10923 := by decide
private theorem levelSize_11 : levelSize 11 = 5462 := by decide
private theorem levelSize_12 : levelSize 12 = 2731 := by decide
private theorem levelSize_13 : levelSize 13 = 1366 := by decide
private theorem levelSize_14 : levelSize 14 = 683 := by decide

theorem level_sib_lt_of_fast (g : Nat) (hg : g < 5592064) :
    g < FULL_TRIPLETS ∧
    ((g >>> 1) ^^^ 1) < levelSize 2 ∧
    ((g >>> 2) ^^^ 1) < levelSize 3 ∧
    ((g >>> 3) ^^^ 1) < levelSize 4 ∧
    ((g >>> 4) ^^^ 1) < levelSize 5 ∧
    ((g >>> 5) ^^^ 1) < levelSize 6 ∧
    ((g >>> 6) ^^^ 1) < levelSize 7 ∧
    ((g >>> 7) ^^^ 1) < levelSize 8 ∧
    ((g >>> 8) ^^^ 1) < levelSize 9 ∧
    ((g >>> 9) ^^^ 1) < levelSize 10 ∧
    ((g >>> 10) ^^^ 1) < levelSize 11 ∧
    ((g >>> 12) ^^^ 1) < levelSize 13 ∧
    g >>> 12 < 1366 := by
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hx : ∀ x m, x < 2 * m → (x ^^^ 1) < 2 * m := fun _ _ h => xor_one_lt_even h
  simp only [Nat.shiftRight_eq_div_pow]
  rw [hft, levelSize_2, levelSize_3, levelSize_4, levelSize_5, levelSize_6, levelSize_7,
      levelSize_8, levelSize_9, levelSize_10, levelSize_11, levelSize_13]
  refine ⟨by omega,
    Nat.lt_of_lt_of_le (hx _ 1398100 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 699050 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 349524 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 174762 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 87380 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 43690 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 21844 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 10922 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 5461 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 2731 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 683 (by omega)) (by omega),
    by omega⟩

theorem level12_14_of_idx13 (g : Nat) (hg : g < 5592064) :
    (((g >>> 11) ^^^ 1) < levelSize 12 ↔ g >>> 12 < 1365) ∧
    (((g >>> 13) ^^^ 1) < levelSize 14 ↔ g >>> 12 < 1364) := by
  simp only [Nat.shiftRight_eq_div_pow]
  rw [levelSize_12, levelSize_14]
  constructor
  · rcases Nat.even_or_odd' (g / 2 ^ 11) with ⟨q, hq | hq⟩
    · rw [hq, xor_one_even]; omega
    · rw [hq, xor_one_odd]; omega
  · rcases Nat.even_or_odd' (g / 2 ^ 13) with ⟨q, hq | hq⟩
    · rw [hq, xor_one_even]; omega
    · rw [hq, xor_one_odd]; omega

theorem level_sib_of_slow_mid (g : Nat) (hg1 : 5592064 ≤ g) (hg2 : g < 5592384) :
    g < FULL_TRIPLETS ∧
    ((g >>> 1) ^^^ 1) < levelSize 2 ∧
    ((g >>> 2) ^^^ 1) < levelSize 3 ∧
    ((g >>> 3) ^^^ 1) < levelSize 4 ∧
    ((g >>> 4) ^^^ 1) < levelSize 5 ∧
    ((g >>> 5) ^^^ 1) < levelSize 6 ∧
    ((g >>> 6) ^^^ 1) < levelSize 7 ∧
    (((g >>> 7) ^^^ 1) < levelSize 8 ↔ (g >>> 7) % 4 < 2) ∧
    ((g >>> 8) ^^^ 1) < levelSize 9 ∧
    ¬ (((g >>> 9) ^^^ 1) < levelSize 10) ∧
    ((g >>> 10) ^^^ 1) < levelSize 11 ∧
    ¬ (((g >>> 11) ^^^ 1) < levelSize 12) ∧
    ((g >>> 12) ^^^ 1) < levelSize 13 ∧
    ¬ (((g >>> 13) ^^^ 1) < levelSize 14) := by
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hx : ∀ x m, x < 2 * m → (x ^^^ 1) < 2 * m := fun _ _ h => xor_one_lt_even h
  simp only [Nat.shiftRight_eq_div_pow]
  rw [hft, levelSize_2, levelSize_3, levelSize_4, levelSize_5, levelSize_6, levelSize_7,
      levelSize_8, levelSize_9, levelSize_10, levelSize_11, levelSize_12, levelSize_13, levelSize_14]
  have h8 : g / 2 ^ 7 = 43688 ∨ g / 2 ^ 7 = 43689 ∨ g / 2 ^ 7 = 43690 := by omega
  have h10 : g / 2 ^ 9 = 10922 := by omega
  have h12 : g / 2 ^ 11 = 2730 := by omega
  have h14 : g / 2 ^ 13 = 682 := by omega
  refine ⟨by omega,
    Nat.lt_of_lt_of_le (hx _ 1398100 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 699050 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 349524 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 174762 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 87381 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 43691 (by omega)) (by omega),
    ?_,
    Nat.lt_of_lt_of_le (hx _ 10923 (by omega)) (by omega),
    by rw [h10]; decide,
    Nat.lt_of_lt_of_le (hx _ 2731 (by omega)) (by omega),
    by rw [h12]; decide,
    Nat.lt_of_lt_of_le (hx _ 683 (by omega)) (by omega),
    by rw [h14]; decide⟩
  rcases h8 with h | h | h <;> rw [h] <;> decide

theorem level_sib_of_slow_tail (g : Nat) (hg1 : 5592384 ≤ g) (hg2 : g ≤ 5592405) :
    ((g >>> 2) ^^^ 1) < levelSize 3 ∧
    ((g >>> 4) ^^^ 1) < levelSize 5 ∧
    ¬ (((g >>> 5) ^^^ 1) < levelSize 6) ∧
    ((g >>> 6) ^^^ 1) < levelSize 7 ∧
    ¬ (((g >>> 7) ^^^ 1) < levelSize 8) ∧
    ((g >>> 8) ^^^ 1) < levelSize 9 ∧
    ¬ (((g >>> 9) ^^^ 1) < levelSize 10) ∧
    ((g >>> 10) ^^^ 1) < levelSize 11 ∧
    ¬ (((g >>> 11) ^^^ 1) < levelSize 12) ∧
    ((g >>> 12) ^^^ 1) < levelSize 13 ∧
    ¬ (((g >>> 13) ^^^ 1) < levelSize 14) := by
  have hx : ∀ x m, x < 2 * m → (x ^^^ 1) < 2 * m := fun _ _ h => xor_one_lt_even h
  simp only [Nat.shiftRight_eq_div_pow]
  rw [levelSize_3, levelSize_5, levelSize_6, levelSize_7, levelSize_8, levelSize_9,
      levelSize_10, levelSize_11, levelSize_12, levelSize_13, levelSize_14]
  have h6 : g / 2 ^ 5 = 174762 := by omega
  have h8 : g / 2 ^ 7 = 43690 := by omega
  have h10 : g / 2 ^ 9 = 10922 := by omega
  have h12 : g / 2 ^ 11 = 2730 := by omega
  have h14 : g / 2 ^ 13 = 682 := by omega
  refine ⟨
    Nat.lt_of_lt_of_le (hx _ 699051 (by omega)) (by omega),
    Nat.lt_of_lt_of_le (hx _ 174763 (by omega)) (by omega),
    by rw [h6]; decide,
    Nat.lt_of_lt_of_le (hx _ 43691 (by omega)) (by omega),
    by rw [h8]; decide,
    Nat.lt_of_lt_of_le (hx _ 10923 (by omega)) (by omega),
    by rw [h10]; decide,
    Nat.lt_of_lt_of_le (hx _ 2731 (by omega)) (by omega),
    by rw [h12]; decide,
    Nat.lt_of_lt_of_le (hx _ 683 (by omega)) (by omega),
    by rw [h14]; decide⟩

end CommitGolfCandidate.MoonOpen
