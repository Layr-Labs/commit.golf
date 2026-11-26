import CommitGolfCandidate.MoonCheckBase

/-! Symbolic execution of the `check` program prologue, empty case, leaf hashing,
3-ary queue climb loop, cap-leaf store/dedup check, and full position loop (`pc[0..155]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Pure Position, Record-Offset, and 3-ary Climb Specifications -/

def posAt (positions : Positions) (ord : Nat) : Index :=
  if h : ord < positions.card then
    (positions.sort (· ≤ ·))[ord]'(by simpa using h)
  else
    ⟨0, by unfold LENGTH LOG_LENGTH; omega⟩

theorem posAt_val (positions : Positions) (ord : Nat) :
    (posAt positions ord).val = openingIndex positions ord := by
  unfold posAt openingIndex
  split <;> rfl

def valAt (input : CheckInput) (ord : Nat) : Entry :=
  if h : ord < input.positions.card then
    input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ord]'(by simpa using h))
  else 0

def posRecordOff (positions : Positions) : Nat → Nat
  | 0 => 0
  | n + 1 => posRecordOff positions n + (24 + 64 * climbStepsFrom (posAt positions n).val)

theorem posRecordOff_mod8 (positions : Positions) (n : Nat) :
    posRecordOff positions n % 8 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => unfold posRecordOff; omega

theorem posRecordOff_le (positions : Positions) (n : Nat) :
    posRecordOff positions n ≤ 664 * n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    unfold posRecordOff
    have hc := climbStepsFrom_le_10 (posAt positions k).val
    omega

theorem posRecordOff_mono (positions : Positions) {a b : Nat} (h : a ≤ b) :
    posRecordOff positions a ≤ posRecordOff positions b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    change posRecordOff positions a ≤ posRecordOff positions _ + _
    omega

def posMarked (positions : Positions) (n c : Nat) : Bool :=
  decide (∃ ord < n, ord < positions.card ∧ capLeafOf (posAt positions ord) = c)

theorem posMarked_zero (positions : Positions) (c : Nat) :
    posMarked positions 0 c = false := by
  simp [posMarked]

theorem posMarked_succ (positions : Positions) {n : Nat} (hn : n < positions.card) (c : Nat) :
    posMarked positions (n + 1) c =
      (posMarked positions n c || decide (capLeafOf (posAt positions n) = c)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [posMarked, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ord, hlt, hcard, heq⟩
    by_cases h : ord < n
    · exact Or.inl ⟨ord, h, hcard, heq⟩
    · have ho : ord = n := by omega
      subst ho; exact Or.inr heq
  · rintro (⟨ord, hlt, hcard, heq⟩ | heq)
    · exact ⟨ord, by omega, hcard, heq⟩
    · exact ⟨n, by omega, hn, heq⟩

theorem posMarked_card_eq_capMark (positions : Positions) (c : Nat) (hc : c < 286) :
    posMarked positions positions.card c = capMark positions c := by
  rw [capMark_leaf positions c hc]
  apply Bool.eq_iff_iff.mpr
  simp only [posMarked, decide_eq_true_eq]
  constructor
  · rintro ⟨ord, hord, _, heq⟩
    refine ⟨posAt positions ord, ?_, heq⟩
    unfold posAt; rw [dif_pos hord]
    exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _)
  · rintro ⟨i, hi, heq⟩
    have hmem : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
    obtain ⟨ord, hord, hget⟩ := List.getElem_of_mem hmem
    have hord' : ord < positions.card := by simpa using hord
    refine ⟨ord, hord', hord', ?_⟩
    unfold posAt; rw [dif_pos hord', hget]; exact heq

def leafInputsOf (c : Comp96) (i : Index) (salt : Salt192) (val : Entry) : List (BitVec 768) :=
  let iU := leafUInput val
  let u := c iU
  let iA := leafAInput u val
  let a := c iA
  let iB := leafBInput val
  let b := c iB
  let iF := leafFinalInput i a b salt
  [iU, iA, iB, iF]

def evalClimb (c : Comp96) (s0 : MachineState) (v off : Nat) (cur : Digest) : Digest :=
  if v < CAP_LEAF_LO then
    let s0d := readBuffer s0 (11072966688 + off) 32
    let s1d := readBuffer s0 (11072966688 + off + 32) 32
    evalClimb c s0 (parentNode v) (off + 64) (c (stepInput v cur (s0d, s1d)))
  else cur
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

theorem evalClimb_of_lt (c : Comp96) (s0 : MachineState) {v : Nat} (hv : v < CAP_LEAF_LO)
    (off : Nat) (cur : Digest) :
    evalClimb c s0 v off cur =
      evalClimb c s0 (parentNode v) (off + 64)
        (c (stepInput v cur (readBuffer s0 (11072966688 + off) 32,
                             readBuffer s0 (11072966688 + off + 32) 32))) := by
  rw [evalClimb]; simp only [hv, ite_true]

theorem evalClimb_of_ge (c : Comp96) (s0 : MachineState) {v : Nat} (hv : CAP_LEAF_LO ≤ v)
    (off : Nat) (cur : Digest) :
    evalClimb c s0 v off cur = cur := by
  rw [evalClimb]; simp only [show ¬ (v < CAP_LEAF_LO) by omega, ite_false]

def climbInputs (c : Comp96) (s0 : MachineState) (v off : Nat) (cur : Digest) : List (BitVec 768) :=
  if v < CAP_LEAF_LO then
    let s0d := readBuffer s0 (11072966688 + off) 32
    let s1d := readBuffer s0 (11072966688 + off + 32) 32
    let inp := stepInput v cur (s0d, s1d)
    inp :: climbInputs c s0 (parentNode v) (off + 64) (c inp)
  else []
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

theorem climbInputs_of_lt (c : Comp96) (s0 : MachineState) {v : Nat} (hv : v < CAP_LEAF_LO)
    (off : Nat) (cur : Digest) :
    climbInputs c s0 v off cur =
      let inp := stepInput v cur (readBuffer s0 (11072966688 + off) 32,
                                  readBuffer s0 (11072966688 + off + 32) 32)
      inp :: climbInputs c s0 (parentNode v) (off + 64) (c inp) := by
  rw [climbInputs]; simp only [hv, ite_true]

theorem climbInputs_of_ge (c : Comp96) (s0 : MachineState) {v : Nat} (hv : CAP_LEAF_LO ≤ v)
    (off : Nat) (cur : Digest) :
    climbInputs c s0 v off cur = [] := by
  rw [climbInputs]; simp only [show ¬ (v < CAP_LEAF_LO) by omega, ite_false]

def climbSibOf (s0 : MachineState) (v off target : Nat) : Digest × Digest :=
  if v < CAP_LEAF_LO then
    if target = v then
      (readBuffer s0 (11072966688 + off) 32, readBuffer s0 (11072966688 + off + 32) 32)
    else
      climbSibOf s0 (parentNode v) (off + 64) target
  else (0, 0)
termination_by CAP_LEAF_LO - v
decreasing_by
  unfold parentNode CAP_LEAF_LO CAP_START TREE_NODES QUEUE_CALLS CAP_CALLS CAP_LEAVES LENGTH LOG_LENGTH at *
  omega

theorem climbSibOf_self (s0 : MachineState) {v : Nat} (hv : v < CAP_LEAF_LO) (off : Nat) :
    climbSibOf s0 v off v =
      (readBuffer s0 (11072966688 + off) 32, readBuffer s0 (11072966688 + off + 32) 32) := by
  rw [climbSibOf]; simp only [hv, ite_true]

theorem climbSibOf_step (s0 : MachineState) {v target : Nat} (hv : v < CAP_LEAF_LO)
    (hne : target ≠ v) (off : Nat) :
    climbSibOf s0 v off target = climbSibOf s0 (parentNode v) (off + 64) target := by
  rw [climbSibOf]; simp only [hv, hne, ite_true, ite_false]

def posCapDigest (c : Comp96) (s0 : MachineState) (input : CheckInput) (ord : Nat) : Digest :=
  let i := posAt input.positions ord
  let off := posRecordOff input.positions ord
  let salt := readBuffer s0 (11072966688 + off) 24
  evalClimb c s0 i.val (off + 24) (leafDigest c i salt (valAt input ord))

def PosConsistent (c : Comp96) (s0 : MachineState) (input : CheckInput) (n : Nat) : Prop :=
  posRecordOff input.positions n ≤ input.proof.length ∧
  ∀ a < n, ∀ b < n,
    capLeafOf (posAt input.positions a) = capLeafOf (posAt input.positions b) →
    posCapDigest c s0 input a = posCapDigest c s0 input b

/-! ### 2. Branch Target and Isolated Backward-Branch Lemmas (`pc[0..155]`) -/

private theorem k_tgt_0   : kPcAt 0   + signExtend13 (20#13)   = kPcAt 5   := by decide
private theorem k_tgt_1   : kPcAt 1   + signExtend13 (1060#13) = kPcAt 266 := by decide
private theorem k_tgt_33  : kPcAt 33  + signExtend13 (932#13)  = kPcAt 266 := by decide
private theorem k_tgt_63  : kPcAt 63  + signExtend13 (16#13)   = kPcAt 67  := by decide
private theorem k_tgt_66  : kPcAt 66  + signExtend21 (12#21)   = kPcAt 69  := by decide
private theorem k_tgt_81  : kPcAt 81  + signExtend13 (740#13)  = kPcAt 266 := by decide
private theorem k_tgt_90  : kPcAt 90  + signExtend13 (12#13)   = kPcAt 93  := by decide
private theorem k_tgt_92  : kPcAt 92  + signExtend21 (16#21)   = kPcAt 96  := by decide
private theorem k_tgt_94  : kPcAt 94  + signExtend13 (8#13)    = kPcAt 96  := by decide
private theorem k_tgt_125 : kPcAt 125 + signExtend13 (8008#13) = kPcAt 79  := by decide
private theorem k_tgt_131 : kPcAt 131 + signExtend13 (48#13)   = kPcAt 143 := by decide
private theorem k_tgt_142 : kPcAt 142 + signExtend21 (52#21)   = kPcAt 155 := by decide
private theorem k_tgt_145 : kPcAt 145 + signExtend13 (484#13)  = kPcAt 266 := by decide
private theorem k_tgt_148 : kPcAt 148 + signExtend13 (472#13)  = kPcAt 266 := by decide
private theorem k_tgt_151 : kPcAt 151 + signExtend13 (460#13)  = kPcAt 266 := by decide
private theorem k_tgt_154 : kPcAt 154 + signExtend13 (448#13)  = kPcAt 266 := by decide
private theorem k_tgt_155 : kPcAt 155 + signExtend13 (7688#13) = kPcAt 29  := by decide

private theorem k_step_125_back (oracle : Oracle) {s : MachineState} {v : Nat}
    (hpc : s.pc = kPcAt 125)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 v)
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 CAP_LEAF_LO)
    (hlt : v < CAP_LEAF_LO) :
    StepsTo oracle s (s.setPC (kPcAt 79)) 1 0 [] := by
  have hcl := capLeafLo_eq
  refine k_step_BLTU_taken (oracle := oracle) (by decide) hpc rfl ?_ k_tgt_125
  rw [hx28, hx23, k_toNat_ofNat v (by omega), k_toNat_ofNat CAP_LEAF_LO (by omega)]
  exact hlt

private theorem k_step_125_done (oracle : Oracle) {s : MachineState} {v : Nat}
    (hpc : s.pc = kPcAt 125)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 v)
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 CAP_LEAF_LO)
    (hge : CAP_LEAF_LO ≤ v) (hbd : v < 2 ^ 64) :
    StepsTo oracle s (s.setPC (kPcAt 126)) 1 0 [] := by
  have hcl := capLeafLo_eq
  refine k_step_BLTU_not_taken (oracle := oracle) (by decide) hpc rfl ?_
  rw [hx28, hx23, k_toNat_ofNat v hbd, k_toNat_ofNat CAP_LEAF_LO (by omega)]
  exact hge

private theorem k_step_155_back (oracle : Oracle) {s : MachineState} {a b : Nat}
    (hpc : s.pc = kPcAt 155)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 a)
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 b)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    StepsTo oracle s (s.setPC (kPcAt 29)) 1 0 [] :=
  k_step_BNE_taken (oracle := oracle) (by decide) hpc rfl
    (by rw [hx9, hx18]; exact k_bv_ne ha hb hne) k_tgt_155

private theorem k_step_155_done (oracle : Oracle) {s : MachineState} {a : Nat}
    (hpc : s.pc = kPcAt 155)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 a)
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 a) :
    StepsTo oracle s (s.setPC (kPcAt 156)) 1 0 [] :=
  k_step_BNE_not_taken (oracle := oracle) (by decide) hpc rfl (by rw [hx9, hx18])

/-! ### 3. Empty and Non-Empty Prologues (`pc[0..28]`) -/

theorem check_prologue_empty (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hempty : input.positions.card = 0) :
    HaltsWith oracle (submission.initialState .check input) 5 0
      (if input.proof.length = 0 then .success else .failure) [] := by
  let s0 := submission.initialState .check input
  have hpc0 : s0.pc = kPcAt 0 := rfl
  have hx16 : s0.getReg .x16 = 0#64 := by
    change BitVec.ofNat 64 input.positions.card = 0#64; rw [hempty]
  have hx17 : s0.getReg .x17 = BitVec.ofNat 64 input.proof.length := rfl
  have hproof_bd : input.proof.length ≤ 11140077536 := hvalid
  have h0 := k_step_BNE_not_taken (oracle := oracle) (s := s0) (idx := 0) (by decide) hpc0 rfl
    (by rw [hx16, k_getReg_x0])
  let s1 := s0.setPC (kPcAt 1)
  by_cases hlen0 : input.proof.length = 0
  · simp only [hlen0, ite_true]
    have h1 := k_step_BNE_not_taken (oracle := oracle) (s := s1) (idx := 1) (by decide) rfl rfl
      (by simp only [s1, MachineState.getReg_setPC, hx17, hlen0, k_getReg_x0])
    have hh := k_step_halt_empty_accept oracle (s1.setPC (kPcAt 2)) rfl
    simpa using (h0.trans h1).halt hh
  · simp only [hlen0, ite_false]
    have h1 := k_step_BNE_taken (oracle := oracle) (s := s1) (idx := 1) (tgt := 266) (by decide) rfl rfl
      (by simp only [s1, MachineState.getReg_setPC, hx17, k_getReg_x0]
          exact k_bv_ne (by omega) (by omega) hlen0) k_tgt_1
    have hh := k_step_halt_reject oracle (s1.setPC (kPcAt 266)) rfl
    simpa using (h0.trans h1).halt hh

theorem check_prologue_nonempty (oracle : Oracle) (input : CheckInput)
    (hne : input.positions.card ≠ 0) :
    let s0 := submission.initialState .check input
    ∃ s1 : MachineState,
      StepsTo oracle s0 s1 25 0 [] ∧
      s1.pc = kPcAt 29 ∧
      s1.mem = s0.mem ∧
      CheckFixedRegs input s1 ∧
      s1.getReg .x9 = BitVec.ofNat 64 6643781664 ∧
      s1.getReg .x19 = BitVec.ofNat 64 6777999392 ∧
      s1.getReg .x20 = BitVec.ofNat 64 11072966688 := by
  intro s0
  have hcard_le := k_card_le input.positions
  have hpc0 : s0.pc = kPcAt 0 := rfl
  have hx11 : s0.getReg .x11 = BitVec.ofNat 64 4294971392 := rfl
  have hx13 : s0.getReg .x13 = BitVec.ofNat 64 6643781664 := rfl
  have hx14 : s0.getReg .x14 = BitVec.ofNat 64 6777999392 := rfl
  have hx15 : s0.getReg .x15 = BitVec.ofNat 64 11072966688 := rfl
  have hx16 : s0.getReg .x16 = BitVec.ofNat 64 input.positions.card := rfl
  have hx17 : s0.getReg .x17 = BitVec.ofNat 64 input.proof.length := rfl
  have h0 := k_step_BNE_taken (oracle := oracle) (s := s0) (idx := 0) (tgt := 5) (by decide) hpc0 rfl
    (by rw [hx16, k_getReg_x0]; exact k_bv_ne (by omega) (by omega) hne) k_tgt_0
  let t0 := s0.setPC (kPcAt 5)
  have h5  := k_step_ADDI (oracle := oracle) (s := t0) (idx := 5)  (by decide) rfl rfl
  let t1 := (t0.setReg .x8  (t0.getReg .x11 + signExtend12 0#12)).setPC (kPcAt 6)
  have h6  := k_step_ADDI (oracle := oracle) (s := t1) (idx := 6)  (by decide) rfl rfl
  let t2 := (t1.setReg .x9  (t1.getReg .x13 + signExtend12 0#12)).setPC (kPcAt 7)
  have h7  := k_step_SLLI (oracle := oracle) (s := t2) (idx := 7)  (by decide) rfl rfl
  let t3 := (t2.setReg .x6  (t2.getReg .x16 <<< (3#6 : BitVec 6).toNat)).setPC (kPcAt 8)
  have h8  := k_step_ADD  (oracle := oracle) (s := t3) (idx := 8)  (by decide) rfl rfl
  let t4 := (t3.setReg .x18 (t3.getReg .x9 + t3.getReg .x6)).setPC (kPcAt 9)
  have h9  := k_step_ADDI (oracle := oracle) (s := t4) (idx := 9)  (by decide) rfl rfl
  let t5 := (t4.setReg .x19 (t4.getReg .x14 + signExtend12 0#12)).setPC (kPcAt 10)
  have h10 := k_step_ADDI (oracle := oracle) (s := t5) (idx := 10) (by decide) rfl rfl
  let t6 := (t5.setReg .x20 (t5.getReg .x15 + signExtend12 0#12)).setPC (kPcAt 11)
  have h11 := k_step_ADD  (oracle := oracle) (s := t6) (idx := 11) (by decide) rfl rfl
  let t7 := (t6.setReg .x21 (t6.getReg .x15 + t6.getReg .x17)).setPC (kPcAt 12)
  have h12 := k_step_ADDI (oracle := oracle) (s := t7) (idx := 12) (by decide) rfl rfl
  let t8 := (t7.setReg .x22 (t7.getReg .x0 + signExtend12 4#12)).setPC (kPcAt 13)
  have h13 := k_step_SLLI (oracle := oracle) (s := t8) (idx := 13) (by decide) rfl rfl
  let t9 := (t8.setReg .x22 (t8.getReg .x22 <<< (11#6 : BitVec 6).toNat)).setPC (kPcAt 14)
  have h14 := k_step_SLLI (oracle := oracle) (s := t9) (idx := 14) (by decide) rfl rfl
  let t10 := (t9.setReg .x22 (t9.getReg .x22 <<< (11#6 : BitVec 6).toNat)).setPC (kPcAt 15)
  have h15 := k_step_ADDI (oracle := oracle) (s := t10) (idx := 15) (by decide) rfl rfl
  let t11 := (t10.setReg .x23 (t10.getReg .x0 + signExtend12 5#12)).setPC (kPcAt 16)
  have h16 := k_step_SLLI (oracle := oracle) (s := t11) (idx := 16) (by decide) rfl rfl
  let t12 := (t11.setReg .x23 (t11.getReg .x23 <<< (11#6 : BitVec 6).toNat)).setPC (kPcAt 17)
  have h17 := k_step_ADDI (oracle := oracle) (s := t12) (idx := 17) (by decide) rfl rfl
  let t13 := (t12.setReg .x23 (t12.getReg .x23 + signExtend12 2047#12)).setPC (kPcAt 18)
  have h18 := k_step_SLLI (oracle := oracle) (s := t13) (idx := 18) (by decide) rfl rfl
  let t14 := (t13.setReg .x23 (t13.getReg .x23 <<< (11#6 : BitVec 6).toNat)).setPC (kPcAt 19)
  have h19 := k_step_ADDI (oracle := oracle) (s := t14) (idx := 19) (by decide) rfl rfl
  let t15 := (t14.setReg .x23 (t14.getReg .x23 + signExtend12 1619#12)).setPC (kPcAt 20)
  have h20 := k_step_ADDI (oracle := oracle) (s := t15) (idx := 20) (by decide) rfl rfl
  let t16 := (t15.setReg .x24 (t15.getReg .x0 + signExtend12 2#12)).setPC (kPcAt 21)
  have h21 := k_step_SLLI (oracle := oracle) (s := t16) (idx := 21) (by decide) rfl rfl
  let t17 := (t16.setReg .x24 (t16.getReg .x24 <<< (11#6 : BitVec 6).toNat)).setPC (kPcAt 22)
  have h22 := k_step_ADDI (oracle := oracle) (s := t17) (idx := 22) (by decide) rfl rfl
  let t18 := (t17.setReg .x25 (t17.getReg .x0 + signExtend12 4#12)).setPC (kPcAt 23)
  have h23 := k_step_SLLI (oracle := oracle) (s := t18) (idx := 23) (by decide) rfl rfl
  let t19 := (t18.setReg .x25 (t18.getReg .x25 <<< (11#6 : BitVec 6).toNat)).setPC (kPcAt 24)
  have h24 := k_step_ADDI (oracle := oracle) (s := t19) (idx := 24) (by decide) rfl rfl
  let t20 := (t19.setReg .x26 (t19.getReg .x0 + signExtend12 256#12)).setPC (kPcAt 25)
  have h25 := k_step_ADDI (oracle := oracle) (s := t20) (idx := 25) (by decide) rfl rfl
  let t21 := (t20.setReg .x27 (t20.getReg .x0 + signExtend12 3#12)).setPC (kPcAt 26)
  have h26 := k_step_ADDI (oracle := oracle) (s := t21) (idx := 26) (by decide) rfl rfl
  let t22 := (t21.setReg .x5 (t21.getReg .x0 + signExtend12 0#12)).setPC (kPcAt 27)
  have h27 := k_step_ADDI (oracle := oracle) (s := t22) (idx := 27) (by decide) rfl rfl
  let t23 := (t22.setReg .x11 (t22.getReg .x0 + signExtend12 96#12)).setPC (kPcAt 28)
  have h28 := k_step_ADDI (oracle := oracle) (s := t23) (idx := 28) (by decide) rfl rfl
  let t24 := (t23.setReg .x13 (t23.getReg .x0 + signExtend12 0#12)).setPC (kPcAt 29)
  have hrun : StepsTo oracle s0 t24 25 0 [] := by
    have a := ((h0.trans h5).trans (h6.trans h7)).trans ((h8.trans h9).trans (h10.trans h11))
    have b := ((h12.trans h13).trans (h14.trans h15)).trans ((h16.trans h17).trans (h18.trans h19))
    have c := ((h20.trans h21).trans (h22.trans h23)).trans ((h24.trans h25).trans ((h26.trans h27).trans h28))
    simpa only [show 8 + 8 + 9 = 25 from rfl, List.append_nil] using (a.trans b).trans c
  have hx8_1 : t1.getReg .x8 = BitVec.ofNat 64 4294971392 := by
    simp only [t1, t0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx11]; decide
  have hx9_2 : t2.getReg .x9 = BitVec.ofNat 64 6643781664 := by
    simp only [t2, t1, t0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx13]; decide
  have hx6_3 : t3.getReg .x6 = BitVec.ofNat 64 (8 * input.positions.card) := by
    simp only [t3, t2, t1, t0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx16,
      show (3#6 : BitVec 6).toNat = 3 by decide, k_bv_shl]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx18_4 : t4.getReg .x18 = BitVec.ofNat 64 (6643781664 + 8 * input.positions.card) := by
    have h9_3 : t3.getReg .x9 = BitVec.ofNat 64 6643781664 := by
      simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x9), hx9_2]
    simp only [t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, h9_3, hx6_3, k_bv_add]
  have hx19_5 : t5.getReg .x19 = BitVec.ofNat 64 6777999392 := by
    simp only [t5, t4, t3, t2, t1, t0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx14]; decide
  have hx20_6 : t6.getReg .x20 = BitVec.ofNat 64 11072966688 := by
    simp only [t6, t5, t4, t3, t2, t1, t0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx15]; decide
  have hx21_7 : t7.getReg .x21 = BitVec.ofNat 64 (11072966688 + input.proof.length) := by
    simp only [t7, t6, t5, t4, t3, t2, t1, t0, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx15, hx17, k_bv_add]
  have hx22_10 : t10.getReg .x22 = BitVec.ofNat 64 LENGTH := by
    simp only [t10, t9, t8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx23_15 : t15.getReg .x23 = BitVec.ofNat 64 CAP_LEAF_LO := by
    rw [capLeafLo_eq]
    simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx24_17 : t17.getReg .x24 = BitVec.ofNat 64 4096 := by
    simp only [t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx25_19 : t19.getReg .x25 = BitVec.ofNat 64 8192 := by
    simp only [t19, t18, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx26_20 : t20.getReg .x26 = BitVec.ofNat 64 256 := by
    simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx27_21 : t21.getReg .x27 = BitVec.ofNat 64 3 := by
    simp only [t21, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx5_22 : t22.getReg .x5 = 0#64 := by
    simp only [t22, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx11_23 : t23.getReg .x11 = BitVec.ofNat 64 96 := by
    simp only [t23, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  have hx13_24 : t24.getReg .x13 = 0#64 := by
    simp only [t24, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  refine ⟨t24, hrun, rfl,
    by simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10,
         t9, t8, t7, t6, t5, t4, t3, t2, t1, t0, k_mem_setPC, k_mem_setReg],
    ⟨?_, ?_, ?_, hx13_24, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [t24, t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx5_22]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx8_1]
  · simp only [t24, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx11_23]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx18_4]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx21_7]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx22_10]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx23_15]
  · simp only [t24, t23, t22, t21, t20, t19, t18, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx24_17]
  · simp only [t24, t23, t22, t21, t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx25_19]
  · simp only [t24, t23, t22, t21, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx26_20]
  · simp only [t24, t23, t22, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx27_21]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx9_2]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx19_5]
  · simp only [t24, t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx20_6]

/-! ### 4. Leaf Hashing Phase (`pc[29..78]`, 4 Compression Calls) -/

private theorem k_ecall_ex (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (s : MachineState) (idx src dst : Nat)
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base .ECALL)
    (hx5 : s.getReg .x5 = 0#64) (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx11 : s.getReg .x11 = BitVec.ofNat 64 96) (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hx13 : s.getReg .x13 = 0#64)
    (hsAl : src % 8 = 0) (hsBd : src + 96 ≤ 68719476736)
    (hdAl : dst % 8 = 0) (hdBd : dst + 32 ≤ 68719476736)
    {inp : BitVec 768} (hinp : readBuffer s src 96 = inp) :
    ∃ s',
      StepsTo oracle s s' 1 1 [(inp.cast h768.symm, oracle.compression (inp.cast h768.symm))] ∧
      s'.pc = kPcAt (idx + 1) ∧
      (∀ r, s'.getReg r = s.getReg r) ∧
      readBuffer s' dst 32 = oracle.compression (inp.cast h768.symm) ∧
      MemEqOutside s s' dst (dst + 32) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := k_step_ecall_compress h768 oracle s idx src dst
    hhi hpc hi hx5 hx10 hx11 hx12 hx13 hsAl hsBd hdAl hdBd
  subst hinp
  exact ⟨_, h1, h2, h3, h4, h5⟩

private theorem check_step_leaf (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    {ord off : Nat} {s : MachineState}
    (hord : ord < input.positions.card)
    (hoff_le : off ≤ input.proof.length) (hoff8 : off % 8 = 0)
    (hpc : s.pc = kPcAt 29) (hfix : CheckFixedRegs input s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * ord))
    (hx19 : s.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * ord))
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + off)) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let val := valAt input ord
    let salt := readBuffer s0 (11072966688 + off) 24
    PhaseOutcome oracle s 48 4 (input.proof.length < off + 24)
      (fun s' q tr =>
        q = 4 ∧
        off + 24 ≤ input.proof.length ∧
        s'.pc = kPcAt 79 ∧
        CheckFixedRegs input s' ∧
        s'.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (ord + 1)) ∧
        s'.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * (ord + 1)) ∧
        s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + (off + 24)) ∧
        s'.getReg .x28 = BitVec.ofNat 64 i.val ∧
        readBuffer s' 448 32 = leafDigest c96 i salt val ∧
        MemEqOutside s s' 256 480 ∧
        ∀ x ∈ leafInputsOf c96 i salt val, InTrace h768 oracle tr x) := by
  intro s0 c96 i val salt
  have hcard_le := k_card_le input.positions
  have hproof_bd : input.proof.length ≤ 11140077536 := hvalid
  have hi_lt : i.val < 16777216 := i.isLt
  -- pc[29..33]: load index i, advance x9, check remaining proof bytes >= 24
  have ha29 : s.getReg .x9 + signExtend12 0#12 = BitVec.ofNat 64 (6643781664 + 8 * ord) := by
    rw [hx9, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
  have h29 := k_step_LD (oracle := oracle) (s := s) (idx := 29) (by decide) hpc rfl
    (by rw [ha29]; exact k_accessValid _ 8 (by omega) (by omega))
  let t1 := (s.setReg .x28 (s.getMem (s.getReg .x9 + signExtend12 0#12))).setPC (kPcAt 30)
  have h30 := k_step_ADDI (oracle := oracle) (s := t1) (idx := 30) (by decide) rfl rfl
  let t2 := (t1.setReg .x9 (t1.getReg .x9 + signExtend12 8#12)).setPC (kPcAt 31)
  have h31 := k_step_SUB (oracle := oracle) (s := t2) (idx := 31) (by decide) rfl rfl
  let t3 := (t2.setReg .x6 (t2.getReg .x21 - t2.getReg .x20)).setPC (kPcAt 32)
  have h32 := k_step_ADDI (oracle := oracle) (s := t3) (idx := 32) (by decide) rfl rfl
  let t4 := (t3.setReg .x7 (t3.getReg .x0 + signExtend12 24#12)).setPC (kPcAt 33)
  have hpre : StepsTo oracle s t4 4 0 [] := by
    simpa only [show 1 + 1 + 1 + 1 = 4 from rfl, List.append_nil] using (h29.trans h30).trans (h31.trans h32)
  have hx6_4 : t4.getReg .x6 = BitVec.ofNat 64 (input.proof.length - off) := by
    have h21 : t2.getReg .x21 = BitVec.ofNat 64 (11072966688 + input.proof.length) := by
      simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x21]
    have h20 : t2.getReg .x20 = BitVec.ofNat 64 (11072966688 + off) := by
      simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx20]
    simp only [t4, t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, h21, h20]
    rw [k_bv_sub _ _ (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx7_4 : t4.getReg .x7 = BitVec.ofNat 64 24 := by
    simp only [t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  by_cases hlt24 : input.proof.length < off + 24
  · have h33 := k_step_BLTU_taken (oracle := oracle) (s := t4) (idx := 33) (tgt := 266) (by decide) rfl rfl
      (by rw [hx6_4, hx7_4, k_toNat_ofNat _ (by omega), k_toNat_ofNat 24 (by omega)]; omega) k_tgt_33
    have hh := k_step_halt_reject oracle (t4.setPC (kPcAt 266)) rfl
    exact .rejected 8 0 [] hlt24 (by omega) (by omega) (by simpa using (hpre.trans h33).halt hh)
  · have hge24 : off + 24 ≤ input.proof.length := by omega
    have h33 := k_step_BLTU_not_taken (oracle := oracle) (s := t4) (idx := 33) (by decide) rfl rfl
      (by rw [hx6_4, hx7_4, k_toNat_ofNat 24 (by omega), k_toNat_ofNat _ (by omega)]; omega)
    let t5 := t4.setPC (kPcAt 34)
    have hmem5 : t5.mem = s.mem := by simp only [t5, t4, t3, t2, t1, k_mem_setPC, k_mem_setReg]
    have hx28_5 : t5.getReg .x28 = BitVec.ofNat 64 i.val := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha29]
      rw [hhigh.getMem_eq (by omega) (by omega) (by omega), check_initial_index input ord hord, ← posAt_val]
    have hx9_5 : t5.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (ord + 1)) := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx9,
        show signExtend12 8#12 = BitVec.ofNat 64 8 by decide, k_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx19_5 : t5.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * ord) := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hx19]
    have hx20_5 : t5.getReg .x20 = BitVec.ofNat 64 (11072966688 + off) := by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hx20]
    have hfix5 : CheckFixedRegs input t5 := hfix.of_agree (fun r hr => by
      have h28 : r ≠ .x28 := isCheckFixedReg_ne hr rfl
      have h9  : r ≠ .x9  := isCheckFixedReg_ne hr rfl
      have h6  : r ≠ .x6  := isCheckFixedReg_ne hr rfl
      have h7  : r ≠ .x7  := isCheckFixedReg_ne hr rfl
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h7.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h9.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h28.symm])
    -- Helper: read initial value slice directly from any state agreeing with s outside [256, 480)
    have hval_slice : ∀ (st : MachineState) (vOff cnt : Nat), MemEqOutside s st 256 480 →
        vOff + cnt ≤ 256 →
        readBuffer st (6777999392 + 256 * ord + vOff) cnt = val.extractLsb' (8 * vOff) (8 * cnt) := by
      intro st vOff cnt hfr hbd
      rw [hfr.readBuffer_eq (by omega) (by omega), hhigh.readBuffer_eq (by omega) (by omega),
        check_initial_value_slice input ord vOff cnt hord hbd]
      simp only [val, valAt, dif_pos hord]
    -- pc[34..36]: ECALL U (x19 -> 256)
    have h34 := k_step_ADDI (oracle := oracle) (s := t5) (idx := 34) (by decide) rfl rfl
    let t6 := (t5.setReg .x10 (t5.getReg .x19 + signExtend12 0#12)).setPC (kPcAt 35)
    have h35 := k_step_ADDI (oracle := oracle) (s := t6) (idx := 35) (by decide) rfl rfl
    let t7 := (t6.setReg .x12 (t6.getReg .x26 + signExtend12 0#12)).setPC (kPcAt 36)
    have hx10_7 : t7.getReg .x10 = BitVec.ofNat 64 (6777999392 + 256 * ord) := by
      simp only [t7, t6, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx19_5, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    have hx12_7 : t7.getReg .x12 = BitVec.ofNat 64 256 := by
      simp only [t7, t6, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix5.x26, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    have hfix7 : CheckFixedRegs input t7 := hfix5.of_agree (fun r hr => by
      have h10 : r ≠ .x10 := isCheckFixedReg_ne hr rfl
      have h12 : r ≠ .x12 := isCheckFixedReg_ne hr rfl
      simp only [t7, t6, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm])
    have hmem7 : t7.mem = s.mem := by simp only [t7, t6, k_mem_setPC, k_mem_setReg, hmem5]
    have hiU_eq : readBuffer t7 (6777999392 + 256 * ord) 96 = leafUInput val := by
      simpa only [Nat.add_zero, leafUInput] using hval_slice t7 0 96 (MemEqOutside.of_mem_eq hmem7 256 480) (by omega)
    obtain ⟨t8, h36, hpc8, hreg8, hu_buf, hfr8⟩ := k_ecall_ex h768 oracle t7 36
      (6777999392 + 256 * ord) 256 (by decide) rfl rfl hfix7.x5 hx10_7 hfix7.x11 hx12_7 hfix7.x13
      (by omega) (by omega) (by omega) (by omega) hiU_eq
    set u := c96 (leafUInput val)
    have hu_eq : readBuffer t8 256 32 = u := hu_buf
    have hfr_s8 : MemEqOutside s t8 256 480 :=
      (MemEqOutside.of_mem_eq hmem7 256 480).trans (hfr8.mono (by omega) (by omega))
    have hfix8 : CheckFixedRegs input t8 := hfix7.of_agree (fun r _ => hreg8 r)
    have hx19_8 : t8.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * ord) := by
      rw [hreg8 .x19]; simp only [t7, t6, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx19_5]
    -- pc[37..52]: two 32B copies x19+96..160 -> 256+32..96
    obtain ⟨t9, hcp1, hpc9, hreg9, hmid1, hfr9⟩ := k_copy_32 oracle (s := t8) (idx := 37) (tmp := .x29)
      (srcReg := .x19) (dstReg := .x26) (srcOff := 96) (dstOff := 32) (by decide) hpc8 (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) hx19_8 hfix8.x26
      (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨t10, hcp2, hpc10, hreg10, hmid2, hfr10⟩ := k_copy_32 oracle (s := t9) (idx := 45) (tmp := .x29)
      (srcReg := .x19) (dstReg := .x26) (srcOff := 128) (dstOff := 64) (by decide) hpc9 (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      ((hreg9 .x19 (by decide)).trans hx19_8) ((hreg9 .x26 (by decide)).trans hfix8.x26)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hfr_s10 : MemEqOutside s t10 256 480 :=
      hfr_s8.trans ((hfr9.mono (by omega) (by omega)).trans (hfr10.mono (by omega) (by omega)))
    have hfix10 : CheckFixedRegs input t10 := hfix8.of_agree (fun r hr =>
      (hreg10 r (isCheckFixedReg_ne hr rfl)).trans (hreg9 r (isCheckFixedReg_ne hr rfl)))
    have hiA_eq : readBuffer t10 256 96 = leafAInput u val := by
      rw [readBuffer_leafA t10 256]
      have hu10 : readBuffer t10 256 32 = u := by
        rw [hfr10.readBuffer_eq (by omega) (by omega), hfr9.readBuffer_eq (by omega) (by omega), hu_eq]
      have hmid : readBuffer t10 (256 + 32) 64 = val.extractLsb' 768 512 := by
        have hlo : readBuffer t10 (256 + 32) 32 = val.extractLsb' (8 * 96) (8 * 32) := by
          rw [hfr10.readBuffer_eq (by omega) (by omega), hmid1]
          exact hval_slice t8 96 32 hfr_s8 (by omega)
        have hhi : readBuffer t10 (256 + 64) 32 = val.extractLsb' (8 * 128) (8 * 32) := by
          rw [hmid2]
          exact hval_slice t9 128 32 (hfr_s8.trans (hfr9.mono (by omega) (by omega))) (by omega)
        exact read_serialized_slice t10 val (256 + 32) 96 64 fun j hj => by
          by_cases h32 : j < 32
          · have hb := congrArg (fun v : Digest => v.extractLsb' (8 * j) 8) hlo
            rw [read_buffer_byte t10 (256 + 32) 32 j h32] at hb
            rw [hb]
            apply BitVec.eq_of_getLsbD_eq; intro b hb8
            simp only [BitVec.getLsbD_extractLsb', hb8, decide_true, Bool.true_and,
              show 8 * j + b < 8 * 32 by omega,
              show 8 * 96 + (8 * j + b) = 8 * (96 + j) + b by omega]
          · have hb := congrArg (fun v : Digest => v.extractLsb' (8 * (j - 32)) 8) hhi
            rw [read_buffer_byte t10 (256 + 64) 32 (j - 32) (by omega)] at hb
            have ha : 256 + 32 + j = 256 + 64 + (j - 32) := by omega
            rw [ha, hb]
            apply BitVec.eq_of_getLsbD_eq; intro b hb8
            simp only [BitVec.getLsbD_extractLsb', hb8, decide_true, Bool.true_and,
              show 8 * (j - 32) + b < 8 * 32 by omega,
              show 8 * 128 + (8 * (j - 32) + b) = 8 * (96 + j) + b by omega]
      rw [hu10, hmid]; rfl
    -- pc[53..58]: compute parity slot, ECALL A (256 -> 352 + 32 * (i.val % 2))
    have h53 := k_step_ANDI (oracle := oracle) (s := t10) (idx := 53) (by decide) hpc10 rfl
    let t11 := (t10.setReg .x6 (t10.getReg .x28 &&& signExtend12 1#12)).setPC (kPcAt 54)
    have h54 := k_step_SLLI (oracle := oracle) (s := t11) (idx := 54) (by decide) rfl rfl
    let t12 := (t11.setReg .x7 (t11.getReg .x6 <<< (5#6 : BitVec 6).toNat)).setPC (kPcAt 55)
    have h55 := k_step_ADDI (oracle := oracle) (s := t12) (idx := 55) (by decide) rfl rfl
    let t13 := (t12.setReg .x12 (t12.getReg .x26 + signExtend12 96#12)).setPC (kPcAt 56)
    have h56 := k_step_ADD  (oracle := oracle) (s := t13) (idx := 56) (by decide) rfl rfl
    let t14 := (t13.setReg .x12 (t13.getReg .x12 + t13.getReg .x7)).setPC (kPcAt 57)
    have h57 := k_step_ADDI (oracle := oracle) (s := t14) (idx := 57) (by decide) rfl rfl
    let t15 := (t14.setReg .x10 (t14.getReg .x26 + signExtend12 0#12)).setPC (kPcAt 58)
    have hreg10_5 : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x29 → t10.getReg r = t5.getReg r := fun r h10 h12 h29 => by
      rw [hreg10 r h29, hreg9 r h29, hreg8 r]
      simp only [t7, t6, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h12),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h10)]
    have hx6_11 : t11.getReg .x6 = BitVec.ofNat 64 (i.val % 2) := by
      have h28 : t10.getReg .x28 = BitVec.ofNat 64 i.val :=
        (hreg10_5 .x28 (by decide) (by decide) (by decide)).trans hx28_5
      simp only [t11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, h28]
      exact k_bv_and1 i.val (by omega)
    have hx7_12 : t12.getReg .x7 = BitVec.ofNat 64 (32 * (i.val % 2)) := by
      simp only [t12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        hx6_11, show (5#6 : BitVec 6).toNat = 5 by decide, k_bv_shl]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx12_15 : t15.getReg .x12 = BitVec.ofNat 64 (352 + 32 * (i.val % 2)) := by
      have h26 : t12.getReg .x26 = BitVec.ofNat 64 256 := by
        simp only [t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hfix10.x26]
      have h12_13 : t13.getReg .x12 = BitVec.ofNat 64 352 := by
        simp only [t13, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
          h26, show signExtend12 96#12 = BitVec.ofNat 64 96 by decide, k_bv_add]
      have h7_13 : t13.getReg .x7 = BitVec.ofNat 64 (32 * (i.val % 2)) := by
        simp only [t13, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx7_12]
      simp only [t15, t14, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, h12_13, h7_13, k_bv_add]
    have hx10_15 : t15.getReg .x10 = BitVec.ofNat 64 256 := by
      simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix10.x26,
        show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    have hfix15 : CheckFixedRegs input t15 := hfix10.of_agree (fun r hr => by
      have h6 := isCheckFixedReg_ne hr (r' := .x6) rfl
      have h7 := isCheckFixedReg_ne hr (r' := .x7) rfl
      have h12 := isCheckFixedReg_ne hr (r' := .x12) rfl
      have h10 := isCheckFixedReg_ne hr (r' := .x10) rfl
      simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h7.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm])
    have hmem15 : t15.mem = t10.mem := by simp only [t15, t14, t13, t12, t11, k_mem_setPC, k_mem_setReg]
    have hiA_15 : readBuffer t15 256 96 = leafAInput u val := by
      rw [(MemEqOutside.of_mem_eq hmem15 0 0).readBuffer_eq (by omega) (by omega), hiA_eq]
    obtain ⟨t16, h58, hpc16, hreg16, ha_buf, hfr16⟩ := k_ecall_ex h768 oracle t15 58
      256 (352 + 32 * (i.val % 2)) (by decide) rfl rfl hfix15.x5 hx10_15 hfix15.x11 hx12_15 hfix15.x13
      (by omega) (by omega) (by omega) (by omega) hiA_15
    set a := leafA c96 val
    have ha_eq : readBuffer t16 (352 + 32 * (i.val % 2)) 32 = a := ha_buf
    have hfr_s16 : MemEqOutside s t16 256 480 :=
      hfr_s10.trans ((MemEqOutside.of_mem_eq hmem15 256 480).trans (hfr16.mono (by omega) (by omega)))
    -- pc[59..62]: ECALL B (x19+160 -> 384 + 32 * (i.val % 2)), x19 += 256
    have h59 := k_step_ADDI (oracle := oracle) (s := t16) (idx := 59) (by decide) hpc16 rfl
    let t17 := (t16.setReg .x10 (t16.getReg .x19 + signExtend12 160#12)).setPC (kPcAt 60)
    have h60 := k_step_ADDI (oracle := oracle) (s := t17) (idx := 60) (by decide) rfl rfl
    let t18 := (t17.setReg .x12 (t17.getReg .x12 + signExtend12 32#12)).setPC (kPcAt 61)
    have hx19_16 : t16.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * ord) := by
      rw [hreg16 .x19]; simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg10_5 .x19 (by decide) (by decide) (by decide)).trans hx19_5
    have hx10_18 : t18.getReg .x10 = BitVec.ofNat 64 (6777999392 + 256 * ord + 160) := by
      simp only [t18, t17, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx19_16, show signExtend12 160#12 = BitVec.ofNat 64 160 by decide, k_bv_add]
    have hx12_18 : t18.getReg .x12 = BitVec.ofNat 64 (384 + 32 * (i.val % 2)) := by
      have h12_16 : t16.getReg .x12 = BitVec.ofNat 64 (352 + 32 * (i.val % 2)) := (hreg16 .x12).trans hx12_15
      simp only [t18, t17, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, h12_16, show signExtend12 32#12 = BitVec.ofNat 64 32 by decide, k_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hfix18 : CheckFixedRegs input t18 := (hfix15.of_agree (fun r _ => hreg16 r)).of_agree (fun r hr => by
      have h10 := isCheckFixedReg_ne hr (r' := .x10) rfl
      have h12 := isCheckFixedReg_ne hr (r' := .x12) rfl
      simp only [t18, t17, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm])
    have hmem18 : t18.mem = t16.mem := by simp only [t18, t17, k_mem_setPC, k_mem_setReg]
    have hiB_18 : readBuffer t18 (6777999392 + 256 * ord + 160) 96 = leafBInput val := by
      simpa only [leafBInput] using
        hval_slice t18 160 96 (hfr_s16.trans (MemEqOutside.of_mem_eq hmem18 256 480)) (by omega)
    obtain ⟨t19, h61, hpc19, hreg19, hb_buf, hfr19⟩ := k_ecall_ex h768 oracle t18 61
      (6777999392 + 256 * ord + 160) (384 + 32 * (i.val % 2)) (by decide) rfl rfl
      hfix18.x5 hx10_18 hfix18.x11 hx12_18 hfix18.x13 (by omega) (by omega) (by omega) (by omega) hiB_18
    set b := leafB c96 val
    have hb_eq : readBuffer t19 (384 + 32 * (i.val % 2)) 32 = b := hb_buf
    have ha_19 : readBuffer t19 (352 + 32 * (i.val % 2)) 32 = a := by
      rw [hfr19.readBuffer_eq (by omega) (by omega),
        (MemEqOutside.of_mem_eq hmem18 0 0).readBuffer_eq (by omega) (by omega), ha_eq]
    have h62 := k_step_ADDI (oracle := oracle) (s := t19) (idx := 62) (by decide) hpc19 rfl
    let t20 := (t19.setReg .x19 (t19.getReg .x19 + signExtend12 256#12)).setPC (kPcAt 63)
    have hfix20 : CheckFixedRegs input t20 := (hfix18.of_agree (fun r _ => hreg19 r)).of_agree (fun r hr => by
      have h19 := isCheckFixedReg_ne hr (r' := .x19) rfl
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h19.symm])
    have hx6_20 : t20.getReg .x6 = BitVec.ofNat 64 (i.val % 2) := by
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x19 ≠ .x6)]
      rw [hreg19 .x6]
      simp only [t18, t17, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      rw [hreg16 .x6]
      simp only [t15, t14, t13, t12, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx6_11]
    have hx19_20 : t20.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * (ord + 1)) := by
      have h19_19 : t19.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * ord) := by
        rw [hreg19 .x19]; simp only [t18, t17, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx19_16]
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h19_19, show signExtend12 256#12 = BitVec.ofNat 64 256 by decide, k_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx9_20 : t20.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (ord + 1)) := by
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x19 ≠ .x9)]
      rw [hreg19 .x9]; simp only [t18, t17, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      rw [hreg16 .x9]; simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg10_5 .x9 (by decide) (by decide) (by decide)).trans hx9_5
    have hx20_20 : t20.getReg .x20 = BitVec.ofNat 64 (11072966688 + off) := by
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x19 ≠ .x20)]
      rw [hreg19 .x20]; simp only [t18, t17, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      rw [hreg16 .x20]; simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg10_5 .x20 (by decide) (by decide) (by decide)).trans hx20_5
    have hx28_20 : t20.getReg .x28 = BitVec.ofNat 64 i.val := by
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x19 ≠ .x28)]
      rw [hreg19 .x28]; simp only [t18, t17, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      rw [hreg16 .x28]; simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg10_5 .x28 (by decide) (by decide) (by decide)).trans hx28_5
    have hmem20 : t20.mem = t19.mem := by simp only [t20, k_mem_setPC, k_mem_setReg]
    have hfr_s20 : MemEqOutside s t20 256 480 :=
      hfr_s16.trans ((MemEqOutside.of_mem_eq hmem18 256 480).trans
        ((hfr19.mono (by omega) (by omega)).trans (MemEqOutside.of_mem_eq hmem20 256 480)))
    -- pc[63..68]: zero 8-byte gap and set x16 = salt destination (424 if even, 352 if odd)
    let saltDst := if i.val % 2 = 0 then 424 else 352
    have hpar : ∃ kPar t21, kPar ≤ 4 ∧ StepsTo oracle t20 t21 kPar 0 [] ∧
        t21.pc = kPcAt 69 ∧
        (∀ r, r ≠ .x16 → t21.getReg r = t20.getReg r) ∧
        t21.getReg .x16 = BitVec.ofNat 64 saltDst ∧
        MemEqOutside t20 t21 256 480 ∧
        (i.val % 2 = 0 → readBuffer t21 352 32 = a ∧ readBuffer t21 384 32 = b ∧ readBuffer t21 416 8 = 0) ∧
        (i.val % 2 ≠ 0 → readBuffer t21 384 32 = a ∧ readBuffer t21 416 32 = b ∧ readBuffer t21 376 8 = 0) := by
      by_cases hev : i.val % 2 = 0
      · have h63 := k_step_BNE_not_taken (oracle := oracle) (s := t20) (idx := 63) (by decide) rfl rfl
          (by rw [hx6_20, hev, k_getReg_x0])
        let u1 := t20.setPC (kPcAt 64)
        have ha64 : u1.getReg .x26 + signExtend12 160#12 = BitVec.ofNat 64 416 := by
          simp only [u1, MachineState.getReg_setPC, hfix20.x26]; decide
        have h64 := k_step_SD (oracle := oracle) (s := u1) (idx := 64) (by decide) rfl rfl
          (by rw [ha64]; exact k_accessValid 416 8 (by omega) (by omega))
        let u2 := (u1.setMem (u1.getReg .x26 + signExtend12 160#12) (u1.getReg .x0)).setPC (kPcAt 65)
        have h65 := k_step_ADDI (oracle := oracle) (s := u2) (idx := 65) (by decide) rfl rfl
        let u3 := (u2.setReg .x16 (u2.getReg .x26 + signExtend12 168#12)).setPC (kPcAt 66)
        have h66 := k_step_JAL_x0 (oracle := oracle) (s := u3) (idx := 66) (tgt := 69) (by decide) rfl rfl k_tgt_66
        let u4 := u3.setPC (kPcAt 69)
        have hfr_u4 : MemEqOutside t20 u4 416 424 := by
          intro addr had hout
          simp only [u4, u3, u2, k_getByte_setPC, k_getByte_setReg, ha64]
          rw [setMem_getByte_ofNat u1 416 addr _ (by omega) (by omega) had hout]
          simp only [u1, k_getByte_setPC]
        refine ⟨4, u4, le_rfl, by simpa using (h63.trans h64).trans (h65.trans h66), rfl,
          fun r hr => by simp only [u4, u3, u2, u1, MachineState.getReg_setPC, k_getReg_setMem,
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)],
          by simp only [u4, u3, u2, u1, MachineState.getReg_setPC, k_getReg_setMem,
               MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix20.x26, saltDst, hev, ite_true]; decide,
          hfr_u4.mono (by omega) (by omega), ?_, fun h => (h hev).elim⟩
        intro _
        refine ⟨?_, ?_, ?_⟩
        · rw [hfr_u4.readBuffer_eq (by omega) (by omega), (MemEqOutside.of_mem_eq hmem20 0 0).readBuffer_eq (by omega) (by omega)]
          simpa [hev] using ha_19
        · rw [hfr_u4.readBuffer_eq (by omega) (by omega), (MemEqOutside.of_mem_eq hmem20 0 0).readBuffer_eq (by omega) (by omega)]
          simpa [hev] using hb_eq
        · rw [readBuffer_word u4 416 (by omega)]
          have hm : u4.getMem (BitVec.ofNat 64 416) = (u1.setMem (BitVec.ofNat 64 416) (u1.getReg .x0)).getMem (BitVec.ofNat 64 416) := by
            simp only [u4, u3, u2, MachineState.getMem, k_mem_setPC, k_mem_setReg, ha64]
          rw [hm, MachineState.getMem_setMem_eq, k_getReg_x0]; rfl
      · have hmod1 : i.val % 2 = 1 := by omega
        have h63 := k_step_BNE_taken (oracle := oracle) (s := t20) (idx := 63) (tgt := 67) (by decide) rfl rfl
          (by rw [hx6_20, hmod1, k_getReg_x0]; decide) k_tgt_63
        let u1 := t20.setPC (kPcAt 67)
        have ha67 : u1.getReg .x26 + signExtend12 120#12 = BitVec.ofNat 64 376 := by
          simp only [u1, MachineState.getReg_setPC, hfix20.x26]; decide
        have h67 := k_step_SD (oracle := oracle) (s := u1) (idx := 67) (by decide) rfl rfl
          (by rw [ha67]; exact k_accessValid 376 8 (by omega) (by omega))
        let u2 := (u1.setMem (u1.getReg .x26 + signExtend12 120#12) (u1.getReg .x0)).setPC (kPcAt 68)
        have h68 := k_step_ADDI (oracle := oracle) (s := u2) (idx := 68) (by decide) rfl rfl
        let u3 := (u2.setReg .x16 (u2.getReg .x26 + signExtend12 96#12)).setPC (kPcAt 69)
        have hfr_u3 : MemEqOutside t20 u3 376 384 := by
          intro addr had hout
          simp only [u3, u2, k_getByte_setPC, k_getByte_setReg, ha67]
          rw [setMem_getByte_ofNat u1 376 addr _ (by omega) (by omega) had hout]
          simp only [u1, k_getByte_setPC]
        refine ⟨3, u3, by omega, by simpa using (h63.trans h67).trans h68, rfl,
          fun r hr => by simp only [u3, u2, u1, MachineState.getReg_setPC, k_getReg_setMem,
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)],
          by simp only [u3, u2, u1, MachineState.getReg_setPC, k_getReg_setMem,
               MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix20.x26, saltDst, hev, ite_false]; decide,
          hfr_u3.mono (by omega) (by omega), fun h => (hev h).elim, ?_⟩
        intro _
        refine ⟨?_, ?_, ?_⟩
        · rw [hfr_u3.readBuffer_eq (by omega) (by omega), (MemEqOutside.of_mem_eq hmem20 0 0).readBuffer_eq (by omega) (by omega)]
          simpa [hmod1] using ha_19
        · rw [hfr_u3.readBuffer_eq (by omega) (by omega), (MemEqOutside.of_mem_eq hmem20 0 0).readBuffer_eq (by omega) (by omega)]
          simpa [hmod1] using hb_eq
        · rw [readBuffer_word u3 376 (by omega)]
          have hm : u3.getMem (BitVec.ofNat 64 376) = (u1.setMem (BitVec.ofNat 64 376) (u1.getReg .x0)).getMem (BitVec.ofNat 64 376) := by
            simp only [u3, u2, MachineState.getMem, k_mem_setPC, k_mem_setReg, ha67]
          rw [hm, MachineState.getMem_setMem_eq, k_getReg_x0]; rfl
    obtain ⟨kPar, t21, hkPar, hrPar, hpc21, hreg21, hx16_21, hfr21, hEven21, hOdd21⟩ := hpar
    have hfr_s21 : MemEqOutside s t21 256 480 := hfr_s20.trans hfr21
    -- pc[69..75]: copy 24B salt x20 -> x16, x20 += 24
    have hsd_bd : saltDst % 8 = 0 ∧ 352 ≤ saltDst ∧ saltDst + 24 ≤ 448 := by
      dsimp only [saltDst]; split_ifs <;> omega
    obtain ⟨t22, hcpS, hpc22, hreg22, hsalt_buf, hfr22⟩ := k_copy_24 oracle (s := t21) (idx := 69)
      (tmp := .x29) (srcReg := .x20) (dstReg := .x16) (srcOff := 0) (dstOff := 0)
      (by decide) hpc21 (by decide) (by decide) rfl rfl rfl rfl rfl rfl
      (by decide) (by decide) (by decide) ((hreg21 .x20 (by decide)).trans hx20_20) hx16_21
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hsalt_eq : readBuffer t22 saltDst 24 = salt := by
      have hs1 : readBuffer t22 saltDst 24 = readBuffer t21 (11072966688 + off) 24 := by
        simpa only [Nat.add_zero] using hsalt_buf
      rw [hs1, hfr_s21.readBuffer_eq (by omega) (by omega), hhigh.readBuffer_eq (by omega) (by omega)]
    have h75 := k_step_ADDI (oracle := oracle) (s := t22) (idx := 75) (by decide) hpc22 rfl
    let t23 := (t22.setReg .x20 (t22.getReg .x20 + signExtend12 24#12)).setPC (kPcAt 76)
    have h76 := k_step_ADDI (oracle := oracle) (s := t23) (idx := 76) (by decide) rfl rfl
    let t24 := (t23.setReg .x10 (t23.getReg .x26 + signExtend12 96#12)).setPC (kPcAt 77)
    have h77 := k_step_ADDI (oracle := oracle) (s := t24) (idx := 77) (by decide) rfl rfl
    let t25 := (t24.setReg .x12 (t24.getReg .x26 + signExtend12 192#12)).setPC (kPcAt 78)
    have hfix22 : CheckFixedRegs input t22 := hfix20.of_agree (fun r hr =>
      (hreg22 r (isCheckFixedReg_ne hr rfl)).trans (hreg21 r (isCheckFixedReg_ne hr rfl)))
    have hfix25 : CheckFixedRegs input t25 := hfix22.of_agree (fun r hr => by
      have h20 := isCheckFixedReg_ne hr (r' := .x20) rfl
      have h10 := isCheckFixedReg_ne hr (r' := .x10) rfl
      have h12 := isCheckFixedReg_ne hr (r' := .x12) rfl
      simp only [t25, t24, t23, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h20.symm])
    have hx10_25 : t25.getReg .x10 = BitVec.ofNat 64 352 := by
      simp only [t25, t24, t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix22.x26]; decide
    have hx12_25 : t25.getReg .x12 = BitVec.ofNat 64 448 := by
      simp only [t25, t24, t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix22.x26]; decide
    have hmem25 : t25.mem = t22.mem := by simp only [t25, t24, t23, k_mem_setPC, k_mem_setReg]
    have hiF_25 : readBuffer t25 352 96 = leafFinalInput i a b salt := by
      rw [(MemEqOutside.of_mem_eq hmem25 0 0).readBuffer_eq (by omega) (by omega)]
      unfold leafFinalInput
      by_cases hev : i.val % 2 = 0
      · simp only [hev, ite_true]
        have hsd : saltDst = 424 := by simp [saltDst, hev]
        obtain ⟨ha21, hb21, hgap21⟩ := hEven21 hev
        have hfr22' : MemEqOutside t21 t22 424 448 := by simpa [hsd] using hfr22
        rw [readBuffer_lateEven t22 352 (by rw [hfr22'.readBuffer_eq (by omega) (by omega)]; exact hgap21),
          hfr22'.readBuffer_eq (by omega) (by omega), hfr22'.readBuffer_eq (by omega) (by omega),
          ha21, hb21, show (352 + 72 : Nat) = saltDst by omega, hsalt_eq]
      · simp only [hev, ite_false]
        have hsd : saltDst = 352 := by simp [saltDst, hev]
        obtain ⟨ha21, hb21, hgap21⟩ := hOdd21 hev
        have hfr22' : MemEqOutside t21 t22 352 376 := by simpa [hsd] using hfr22
        rw [readBuffer_lateOdd t22 352 (by rw [hfr22'.readBuffer_eq (by omega) (by omega)]; exact hgap21),
          hfr22'.readBuffer_eq (by omega) (by omega), hfr22'.readBuffer_eq (by omega) (by omega),
          ha21, hb21, ← hsd, hsalt_eq]
    obtain ⟨t26, h78, hpc26, hreg26, hf_buf, hfr26⟩ := k_ecall_ex h768 oracle t25 78
      352 448 (by decide) rfl rfl hfix25.x5 hx10_25 hfix25.x11 hx12_25 hfix25.x13
      (by omega) (by omega) (by omega) (by omega) hiF_25
    have p1 : StepsTo oracle s t8 8 1
        [((leafUInput val).cast h768.symm, oracle.compression ((leafUInput val).cast h768.symm))] := by
      simpa only [show 4 + 1 + (1 + 1 + 1) = 8 from rfl, List.nil_append, List.append_nil] using
        (hpre.trans h33).trans ((h34.trans h35).trans h36)
    have p2 : StepsTo oracle t8 t16 22 1
        [((leafAInput u val).cast h768.symm, oracle.compression ((leafAInput u val).cast h768.symm))] := by
      simpa only [show 8 + 8 + (1 + 1 + (1 + 1) + 1 + 1) = 22 from rfl, List.nil_append, List.append_nil] using
        (hcp1.trans hcp2).trans ((((h53.trans h54).trans (h55.trans h56)).trans h57).trans h58)
    have p3 : StepsTo oracle t16 t20 4 1
        [((leafBInput val).cast h768.symm, oracle.compression ((leafBInput val).cast h768.symm))] := by
      simpa only [show 1 + 1 + 1 + 1 = 4 from rfl, List.nil_append, List.append_nil] using
        ((h59.trans h60).trans h61).trans h62
    have p4 : StepsTo oracle t20 t26 (kPar + 10) 1
        [((leafFinalInput i a b salt).cast h768.symm, oracle.compression ((leafFinalInput i a b salt).cast h768.symm))] := by
      simpa only [show kPar + 6 + (1 + 1 + 1 + 1) = kPar + 10 by omega, List.nil_append, List.append_nil] using
        (hrPar.trans hcpS).trans (((h75.trans h76).trans h77).trans h78)
    have hsteps_all := (p1.trans p2).trans (p3.trans p4)
    refine .continued t26 (8 + 22 + (4 + (kPar + 10))) 4 _ (by omega) (by omega) hsteps_all
      ⟨rfl, hge24, hpc26, hfix25.of_agree (fun r _ => hreg26 r), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hreg26 .x9]
      simp only [t25, t24, t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg22 .x9 (by decide)).trans ((hreg21 .x9 (by decide)).trans hx9_20)
    · rw [hreg26 .x19]
      simp only [t25, t24, t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg22 .x19 (by decide)).trans ((hreg21 .x19 (by decide)).trans hx19_20)
    · rw [hreg26 .x20]
      simp only [t25, t24, t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, (hreg22 .x20 (by decide)).trans ((hreg21 .x20 (by decide)).trans hx20_20),
        show signExtend12 24#12 = BitVec.ofNat 64 24 by decide, k_bv_add, Nat.add_assoc]
    · rw [hreg26 .x28]
      simp only [t25, t24, t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg22 .x28 (by decide)).trans ((hreg21 .x28 (by decide)).trans hx28_20)
    · exact hf_buf
    · exact hfr_s21.trans ((hfr22.mono (by omega) (by omega)).trans
        ((MemEqOutside.of_mem_eq hmem25 256 480).trans (hfr26.mono (by omega) (by omega))))
    · intro x hx
      unfold InTrace
      simp only [leafInputsOf, List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.cons_append, List.nil_append]
      rcases hx with rfl | rfl | rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-! ### 5. Single 3-ary Climb Step and Climb Loop (`pc[79..125]`) -/

private theorem check_climb_one (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    {v off : Nat} {s : MachineState}
    (hv : v < CAP_LEAF_LO) (hoff_le : off ≤ input.proof.length) (hoff8 : off % 8 = 0)
    (hpc : s.pc = kPcAt 79) (hfix : CheckFixedRegs input s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + off))
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 v) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let cur := readBuffer s 448 32
    let inp := stepInput v cur (readBuffer s0 (11072966688 + off) 32,
                                readBuffer s0 (11072966688 + off + 32) 32)
    PhaseOutcome oracle s 45 1 (input.proof.length < off + 64)
      (fun s' q tr =>
        q = 1 ∧
        off + 64 ≤ input.proof.length ∧
        s'.pc = (if parentNode v < CAP_LEAF_LO then kPcAt 79 else kPcAt 126) ∧
        CheckFixedRegs input s' ∧
        s'.getReg .x9 = s.getReg .x9 ∧
        s'.getReg .x19 = s.getReg .x19 ∧
        s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + (off + 64)) ∧
        s'.getReg .x28 = BitVec.ofNat 64 (parentNode v) ∧
        readBuffer s' 448 32 = c96 inp ∧
        MemEqOutside s s' 256 480 ∧
        InTrace h768 oracle tr inp) := by
  intro s0 c96 cur inp
  have hcl := capLeafLo_eq
  have hqc := queueCalls_eq
  have hlen_eq : LENGTH = 16777216 := by decide
  have hproof_bd : input.proof.length ≤ 11140077536 := hvalid
  -- pc[79..81]: bounds check proof.length - off >= 64
  have h79 := k_step_SUB (oracle := oracle) (s := s) (idx := 79) (by decide) hpc rfl
  let t1 := (s.setReg .x6 (s.getReg .x21 - s.getReg .x20)).setPC (kPcAt 80)
  have h80 := k_step_ADDI (oracle := oracle) (s := t1) (idx := 80) (by decide) rfl rfl
  let t2 := (t1.setReg .x7 (t1.getReg .x0 + signExtend12 64#12)).setPC (kPcAt 81)
  have hx6_2 : t2.getReg .x6 = BitVec.ofNat 64 (input.proof.length - off) := by
    simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, hfix.x21, hx20]
    rw [k_bv_sub _ _ (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx7_2 : t2.getReg .x7 = BitVec.ofNat 64 64 := by
    simp only [t2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  by_cases hlt64 : input.proof.length < off + 64
  · have h81 := k_step_BLTU_taken (oracle := oracle) (s := t2) (idx := 81) (tgt := 266) (by decide) rfl rfl
      (by rw [hx6_2, hx7_2, k_toNat_ofNat _ (by omega), k_toNat_ofNat 64 (by omega)]; omega) k_tgt_81
    have hh := k_step_halt_reject oracle (t2.setPC (kPcAt 266)) rfl
    exact .rejected 6 0 [] hlt64 (by omega) (by omega) (by simpa using ((h79.trans h80).trans h81).halt hh)
  · have hge64 : off + 64 ≤ input.proof.length := by omega
    have h81 := k_step_BLTU_not_taken (oracle := oracle) (s := t2) (idx := 81) (by decide) rfl rfl
      (by rw [hx6_2, hx7_2, k_toNat_ofNat 64 (by omega), k_toNat_ofNat _ (by omega)]; omega)
    let t3 := t2.setPC (kPcAt 82)
    -- pc[82..89]: q = v / 3, r = v % 3, x15 = 256 + 32*r, x16 = 256, x17 = 320
    have h82 := k_step_DIVU (oracle := oracle) (s := t3) (idx := 82) (by decide) rfl rfl
    let t4 := (t3.setReg .x6 (rv64_divu (t3.getReg .x28) (t3.getReg .x27))).setPC (kPcAt 83)
    have h83 := k_step_SLLI (oracle := oracle) (s := t4) (idx := 83) (by decide) rfl rfl
    let t5 := (t4.setReg .x7 (t4.getReg .x6 <<< (1#6 : BitVec 6).toNat)).setPC (kPcAt 84)
    have h84 := k_step_ADD  (oracle := oracle) (s := t5) (idx := 84) (by decide) rfl rfl
    let t6 := (t5.setReg .x7 (t5.getReg .x7 + t5.getReg .x6)).setPC (kPcAt 85)
    have h85 := k_step_SUB  (oracle := oracle) (s := t6) (idx := 85) (by decide) rfl rfl
    let t7 := (t6.setReg .x7 (t6.getReg .x28 - t6.getReg .x7)).setPC (kPcAt 86)
    have h86 := k_step_ADDI (oracle := oracle) (s := t7) (idx := 86) (by decide) rfl rfl
    let t8 := (t7.setReg .x16 (t7.getReg .x26 + signExtend12 0#12)).setPC (kPcAt 87)
    have h87 := k_step_ADDI (oracle := oracle) (s := t8) (idx := 87) (by decide) rfl rfl
    let t9 := (t8.setReg .x17 (t8.getReg .x26 + signExtend12 64#12)).setPC (kPcAt 88)
    have h88 := k_step_SLLI (oracle := oracle) (s := t9) (idx := 88) (by decide) rfl rfl
    let t10 := (t9.setReg .x15 (t9.getReg .x7 <<< (5#6 : BitVec 6).toNat)).setPC (kPcAt 89)
    have h89 := k_step_ADD  (oracle := oracle) (s := t10) (idx := 89) (by decide) rfl rfl
    let t11 := (t10.setReg .x15 (t10.getReg .x26 + t10.getReg .x15)).setPC (kPcAt 90)
    have hpre11 : StepsTo oracle s t11 11 0 [] := by
      have a := ((h79.trans h80).trans h81).trans ((h82.trans h83).trans (h84.trans h85))
      have b := (h86.trans h87).trans (h88.trans h89)
      simpa only [show 7 + 4 = 11 from rfl, List.append_nil] using a.trans b
    have hx6_4 : t4.getReg .x6 = BitVec.ofNat 64 (v / 3) := by
      have h28 : t3.getReg .x28 = BitVec.ofNat 64 v := by
        simp only [t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx28]
      have h27 : t3.getReg .x27 = 3#64 := by
        simp only [t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x27]
      simp only [t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h28, h27, rv64_divu_three, k_toNat_ofNat v (by omega)]
    have hx7_7 : t7.getReg .x7 = BitVec.ofNat 64 (v % 3) := by
      have h6_5 : t5.getReg .x6 = BitVec.ofNat 64 (v / 3) := by
        simp only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hx6_4]
      have h7_5 : t5.getReg .x7 = BitVec.ofNat 64 (2 * (v / 3)) := by
        simp only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
          hx6_4, show (1#6 : BitVec 6).toNat = 1 by decide, k_bv_shl]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have h7_6 : t6.getReg .x7 = BitVec.ofNat 64 (3 * (v / 3)) := by
        simp only [t6, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
          h7_5, h6_5, k_bv_add]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have h28_6 : t6.getReg .x28 = BitVec.ofNat 64 v := by
        simp only [t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx28]
      simp only [t7, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h28_6, h7_6]
      rw [k_bv_sub _ _ (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx26_11 : ∀ r, r = .x26 → t11.getReg r = BitVec.ofNat 64 256 := fun r hr => by
      subst hr; simp only [t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x26]
    have hx15_11 : t11.getReg .x15 = BitVec.ofNat 64 (256 + 32 * (v % 3)) := by
      have h7_9 : t9.getReg .x7 = BitVec.ofNat 64 (v % 3) := by
        simp only [t9, t8, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx7_7]
      have h15_10 : t10.getReg .x15 = BitVec.ofNat 64 (32 * (v % 3)) := by
        simp only [t10, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
          h7_9, show (5#6 : BitVec 6).toNat = 5 by decide, k_bv_shl]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have h26_10 : t10.getReg .x26 = BitVec.ofNat 64 256 := by
        simp only [t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x26]
      simp only [t11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h26_10, h15_10, k_bv_add]
    have hx16_11 : t11.getReg .x16 = BitVec.ofNat 64 256 := by
      simp only [t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x26]; decide
    have hx17_11 : t11.getReg .x17 = BitVec.ofNat 64 320 := by
      simp only [t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x26]; decide
    have hx7_11 : t11.getReg .x7 = BitVec.ofNat 64 (v % 3) := by
      simp only [t11, t10, t9, t8, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx7_7]
    -- pc[90..95]: branch on v % 3 to set (dCur, dS0, dS1)
    let dCur := 256 + 32 * (v % 3)
    let dS0  := if v % 3 = 0 then 288 else 256
    let dS1  := if v % 3 = 2 then 288 else 320
    have hsel : ∃ kSel t12, kSel ≤ 4 ∧ StepsTo oracle t11 t12 kSel 0 [] ∧
        t12.pc = kPcAt 96 ∧ t12.mem = t11.mem ∧
        (∀ r, r ≠ .x7 → r ≠ .x16 → r ≠ .x17 → t12.getReg r = t11.getReg r) ∧
        t12.getReg .x16 = BitVec.ofNat 64 dS0 ∧
        t12.getReg .x17 = BitVec.ofNat 64 dS1 := by
      have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hr0 | hr1 | hr2
      · have h90 := k_step_BNE_not_taken (oracle := oracle) (s := t11) (idx := 90) (by decide) rfl rfl
          (by rw [hx7_11, hr0, k_getReg_x0])
        let u1 := t11.setPC (kPcAt 91)
        have h91 := k_step_ADDI (oracle := oracle) (s := u1) (idx := 91) (by decide) rfl rfl
        let u2 := (u1.setReg .x16 (u1.getReg .x26 + signExtend12 32#12)).setPC (kPcAt 92)
        have h92 := k_step_JAL_x0 (oracle := oracle) (s := u2) (idx := 92) (tgt := 96) (by decide) rfl rfl k_tgt_92
        refine ⟨3, u2.setPC (kPcAt 96), by omega, by simpa using (h90.trans h91).trans h92, rfl,
          by simp only [u2, u1, k_mem_setPC, k_mem_setReg],
          fun r _ h16 _ => by simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h16)],
          by simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx26_11 .x26 rfl, dS0, hr0, ite_true]; decide,
          by simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x16 ≠ .x17), hx17_11, dS1, hr0]; rfl⟩
      · have h90 := k_step_BNE_taken (oracle := oracle) (s := t11) (idx := 90) (tgt := 93) (by decide) rfl rfl
          (by rw [hx7_11, hr1, k_getReg_x0]; decide) k_tgt_90
        let u1 := t11.setPC (kPcAt 93)
        have h93 := k_step_ADDI (oracle := oracle) (s := u1) (idx := 93) (by decide) rfl rfl
        let u2 := (u1.setReg .x7 (u1.getReg .x7 + signExtend12 4095#12)).setPC (kPcAt 94)
        have hx7_u2 : u2.getReg .x7 = 0#64 := by
          simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx7_11, hr1]
          exact k_bv_add_neg1 0
        have h94 := k_step_BEQ_taken (oracle := oracle) (s := u2) (idx := 94) (tgt := 96) (by decide) rfl rfl
          (by rw [hx7_u2, k_getReg_x0]) k_tgt_94
        refine ⟨3, u2.setPC (kPcAt 96), by omega, by simpa using (h90.trans h93).trans h94, rfl,
          by simp only [u2, u1, k_mem_setPC, k_mem_setReg],
          fun r h7 _ _ => by simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7)],
          by simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x16), hx16_11, dS0, hr1]; rfl,
          by simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x17), hx17_11, dS1, hr1]; rfl⟩
      · have h90 := k_step_BNE_taken (oracle := oracle) (s := t11) (idx := 90) (tgt := 93) (by decide) rfl rfl
          (by rw [hx7_11, hr2, k_getReg_x0]; decide) k_tgt_90
        let u1 := t11.setPC (kPcAt 93)
        have h93 := k_step_ADDI (oracle := oracle) (s := u1) (idx := 93) (by decide) rfl rfl
        let u2 := (u1.setReg .x7 (u1.getReg .x7 + signExtend12 4095#12)).setPC (kPcAt 94)
        have hx7_u2 : u2.getReg .x7 = 1#64 := by
          simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx7_11, hr2]
          exact k_bv_add_neg1 1
        have h94 := k_step_BEQ_not_taken (oracle := oracle) (s := u2) (idx := 94) (by decide) rfl rfl
          (by rw [hx7_u2, k_getReg_x0]; decide)
        let u3 := u2.setPC (kPcAt 95)
        have h95 := k_step_ADDI (oracle := oracle) (s := u3) (idx := 95) (by decide) rfl rfl
        let u4 := (u3.setReg .x17 (u3.getReg .x26 + signExtend12 32#12)).setPC (kPcAt 96)
        refine ⟨4, u4, le_rfl, by simpa using ((h90.trans h93).trans h94).trans h95, rfl,
          by simp only [u4, u3, u2, u1, k_mem_setPC, k_mem_setReg],
          fun r h7 _ h17 => by simp only [u4, u3, u2, u1, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h17),
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7)],
          by simp only [u4, u3, u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx16_11, dS0, hr2]; rfl,
          by simp only [u4, u3, u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
               MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx26_11 .x26 rfl, dS1, hr2, ite_true]; decide⟩
    obtain ⟨kSel, t12, hkSel, hrSel, hpc12, hmem12_11, hreg12, hx16_12, hx17_12⟩ := hsel
    have hmem12 : t12.mem = s.mem := hmem12_11.trans (by simp only [t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, k_mem_setPC, k_mem_setReg])
    have hreg12_s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → t12.getReg r = s.getReg r := fun r h6 h7 h15 h16 h17 => by
      rw [hreg12 r h7 h16 h17]
      simp only [t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h17),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h16),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6)]
    have hslots : dCur % 8 = 0 ∧ dS0 % 8 = 0 ∧ dS1 % 8 = 0 ∧
        256 ≤ dCur ∧ dCur + 32 ≤ 352 ∧ 256 ≤ dS0 ∧ dS0 + 32 ≤ 352 ∧ 256 ≤ dS1 ∧ dS1 + 32 ≤ 352 ∧
        (dCur + 32 ≤ dS0 ∨ dS0 + 32 ≤ dCur) ∧
        (dCur + 32 ≤ dS1 ∨ dS1 + 32 ≤ dCur) ∧
        (dS0 + 32 ≤ dS1 ∨ dS1 + 32 ≤ dS0) := by
      dsimp only [dCur, dS0, dS1]; have : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases this with h | h | h <;> simp [h]
    -- pc[96..119]: 3 aligned 32B copies into dCur, dS0, dS1
    obtain ⟨t13, hcp0, hpc13, hreg13, hbuf0, hfr13⟩ := k_copy_32 oracle (s := t12) (idx := 96) (tmp := .x29)
      (srcReg := .x26) (dstReg := .x15) (srcOff := 192) (dstOff := 0) (by decide) hpc12 (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      ((hreg12_s .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x26)
      ((hreg12 .x15 (by decide) (by decide) (by decide)).trans hx15_11)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨t14, hcp1, hpc14, hreg14, hbuf1, hfr14⟩ := k_copy_32 oracle (s := t13) (idx := 104) (tmp := .x29)
      (srcReg := .x20) (dstReg := .x16) (srcOff := 0) (dstOff := 0) (by decide) hpc13 (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      ((hreg13 .x20 (by decide)).trans ((hreg12_s .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20))
      ((hreg13 .x16 (by decide)).trans hx16_12)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨t15, hcp2, hpc15, hreg15, hbuf2, hfr15⟩ := k_copy_32 oracle (s := t14) (idx := 112) (tmp := .x29)
      (srcReg := .x20) (dstReg := .x17) (srcOff := 32) (dstOff := 0) (by decide) hpc14 (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      ((hreg14 .x20 (by decide)).trans ((hreg13 .x20 (by decide)).trans ((hreg12_s .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20)))
      ((hreg14 .x17 (by decide)).trans ((hreg13 .x17 (by decide)).trans hx17_12))
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have hfr_s15 : MemEqOutside s t15 256 352 :=
      (MemEqOutside.of_mem_eq hmem12 256 352).trans
        ((hfr13.mono (by omega) (by omega)).trans
          ((hfr14.mono (by omega) (by omega)).trans (hfr15.mono (by omega) (by omega))))
    -- Reconstruct readBuffer t15 256 96 = stepInput v cur (s0d, s1d)
    have hdCur_15 : readBuffer t15 dCur 32 = cur := by
      have h13' : readBuffer t13 dCur 32 = cur := by
        simpa only [Nat.add_zero, show (256 + 192 : Nat) = 448 from rfl] using
          hbuf0.trans ((MemEqOutside.of_mem_eq hmem12 0 0).readBuffer_eq (by omega) (by omega))
      rw [hfr15.readBuffer_eq (by omega) (by omega), hfr14.readBuffer_eq (by omega) (by omega), h13']
    have hdS0_15 : readBuffer t15 dS0 32 = readBuffer s0 (11072966688 + off) 32 := by
      have h14' : readBuffer t14 dS0 32 = readBuffer s0 (11072966688 + off) 32 := by
        simpa only [Nat.add_zero] using
          hbuf1.trans ((hfr13.readBuffer_eq (by omega) (by omega)).trans
            (((MemEqOutside.of_mem_eq hmem12 0 0).readBuffer_eq (by omega) (by omega)).trans
              (hhigh.readBuffer_eq (by omega) (by omega))))
      rw [hfr15.readBuffer_eq (by omega) (by omega), h14']
    have hdS1_15 : readBuffer t15 dS1 32 = readBuffer s0 (11072966688 + off + 32) 32 := by
      simpa only [Nat.add_zero] using
        hbuf2.trans ((hfr14.readBuffer_eq (by omega) (by omega)).trans
          ((hfr13.readBuffer_eq (by omega) (by omega)).trans
            (((MemEqOutside.of_mem_eq hmem12 0 0).readBuffer_eq (by omega) (by omega)).trans
              (hhigh.readBuffer_eq (by omega) (by omega)))))
    have hinp_15 : readBuffer t15 256 96 = inp := by
      rw [readBuffer_ternary t15 256]
      unfold inp stepInput
      have hnot_last : ¬ (v / 3 = QUEUE_CALLS - 1) := by omega
      simp only [hnot_last, ite_false]
      have hmod : v % 3 = 0 ∨ v % 3 = 1 ∨ v % 3 = 2 := by omega
      rcases hmod with hr0 | hr1 | hr2
      · simp only [hr0, ite_true]
        have h0 : dCur = 256 := by simp [dCur, hr0]
        have h1 : dS0 = 288 := by simp [dS0, hr0]
        have h2 : dS1 = 320 := by simp [dS1, hr0]
        rw [show (256 + 32 : Nat) = dS0 by omega, show (256 + 64 : Nat) = dS1 by omega, ← h0,
          hdCur_15, hdS0_15, hdS1_15]
      · simp only [hr1, show (1 : Nat) ≠ 0 by omega, ite_false, ite_true]
        have h0 : dS0 = 256 := by simp [dS0, hr1]
        have h1 : dCur = 288 := by simp [dCur, hr1]
        have h2 : dS1 = 320 := by simp [dS1, hr1]
        rw [show (256 + 32 : Nat) = dCur by omega, show (256 + 64 : Nat) = dS1 by omega, ← h0,
          hdS0_15, hdCur_15, hdS1_15]
      · simp only [hr2, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false]
        have h0 : dS0 = 256 := by simp [dS0, hr2]
        have h1 : dS1 = 288 := by simp [dS1, hr2]
        have h2 : dCur = 320 := by simp [dCur, hr2]
        rw [show (256 + 32 : Nat) = dS1 by omega, show (256 + 64 : Nat) = dCur by omega, ← h0,
          hdS0_15, hdS1_15, hdCur_15]
    -- pc[120..124]: x20 += 64, ECALL (256 -> 448), x28 = LENGTH + q
    have h120 := k_step_ADDI (oracle := oracle) (s := t15) (idx := 120) (by decide) hpc15 rfl
    let t16 := (t15.setReg .x20 (t15.getReg .x20 + signExtend12 64#12)).setPC (kPcAt 121)
    have h121 := k_step_ADDI (oracle := oracle) (s := t16) (idx := 121) (by decide) rfl rfl
    let t17 := (t16.setReg .x10 (t16.getReg .x26 + signExtend12 0#12)).setPC (kPcAt 122)
    have h122 := k_step_ADDI (oracle := oracle) (s := t17) (idx := 122) (by decide) rfl rfl
    let t18 := (t17.setReg .x12 (t17.getReg .x26 + signExtend12 192#12)).setPC (kPcAt 123)
    have hreg15_12 : ∀ r, r ≠ .x29 → t15.getReg r = t12.getReg r := fun r hr =>
      (hreg15 r hr).trans ((hreg14 r hr).trans (hreg13 r hr))
    have hfix15 : CheckFixedRegs input t15 := hfix.of_agree (fun r hr =>
      (hreg15_12 r (isCheckFixedReg_ne hr rfl)).trans
        (hreg12_s r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl)
          (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl)))
    have hfix18 : CheckFixedRegs input t18 := hfix15.of_agree (fun r hr => by
      have h20 := isCheckFixedReg_ne hr (r' := .x20) rfl
      have h10 := isCheckFixedReg_ne hr (r' := .x10) rfl
      have h12 := isCheckFixedReg_ne hr (r' := .x12) rfl
      simp only [t18, t17, t16, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h20.symm])
    have hx10_18 : t18.getReg .x10 = BitVec.ofNat 64 256 := by
      simp only [t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix15.x26]; decide
    have hx12_18 : t18.getReg .x12 = BitVec.ofNat 64 448 := by
      simp only [t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix15.x26]; decide
    have hmem18 : t18.mem = t15.mem := by simp only [t18, t17, t16, k_mem_setPC, k_mem_setReg]
    let t19 := writeBits t18 (BitVec.ofNat 64 448)
      (oracle.compression ((readBuffer t18 256 96).cast h768.symm))
    obtain ⟨h123, hpc19, hreg19_raw, hdig_buf_raw, hfr19_raw⟩ := k_step_ecall_compress h768 oracle t18 123
      256 448 (by decide) rfl rfl hfix18.x5 hx10_18 hfix18.x11 hx12_18 hfix18.x13
      (by omega) (by omega) (by omega) (by omega)
    have hreg19 : ∀ r, t19.getReg r = t18.getReg r := hreg19_raw
    have hdig_buf : readBuffer t19 448 32 = oracle.compression ((readBuffer t18 256 96).cast h768.symm) := hdig_buf_raw
    have hfr19 : MemEqOutside t18 t19 448 (448 + 32) := hfr19_raw
    have hinp_18 : readBuffer t18 256 96 = inp := by
      rw [(MemEqOutside.of_mem_eq hmem18 0 0).readBuffer_eq (by omega) (by omega), hinp_15]
    have h124 := k_step_ADD (oracle := oracle) (s := t19) (idx := 124) (by decide) hpc19 rfl
    let t20 := (t19.setReg .x28 (t19.getReg .x22 + t19.getReg .x6)).setPC (kPcAt 125)
    have hx6_19 : t19.getReg .x6 = BitVec.ofNat 64 (v / 3) := by
      rw [hreg19 .x6]; simp only [t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      rw [hreg15_12 .x6 (by decide), hreg12 .x6 (by decide) (by decide) (by decide)]
      simp only [t11, t10, t9, t8, t7, t6, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx6_4]
    have hx28_20 : t20.getReg .x28 = BitVec.ofNat 64 (parentNode v) := by
      have h22_19 : t19.getReg .x22 = BitVec.ofNat 64 LENGTH := (hreg19 .x22).trans hfix18.x22
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h22_19, hx6_19, k_bv_add, parentNode]
    have hfix20 : CheckFixedRegs input t20 := (hfix18.of_agree (fun r _ => hreg19 r)).of_agree (fun r hr => by
      have h28 := isCheckFixedReg_ne hr (r' := .x28) rfl
      simp only [t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h28.symm])
    -- pc[125]: isolated backward branch BLTU x28 x23 -> 79
    let t21 := t20.setPC (if parentNode v < CAP_LEAF_LO then kPcAt 79 else kPcAt 126)
    have h125 : StepsTo oracle t20 t21 1 0 [] := by
      by_cases hpar : parentNode v < CAP_LEAF_LO
      · simpa only [t21, hpar, ite_true] using k_step_125_back oracle (s := t20) rfl hx28_20 hfix20.x23 hpar
      · have hpar_bd : parentNode v < 2 ^ 64 := by unfold parentNode; omega
        simpa only [t21, hpar, ite_false] using k_step_125_done oracle (s := t20) rfl hx28_20 hfix20.x23 (by omega) hpar_bd
    have hsteps_all : StepsTo oracle s t21 (11 + kSel + 8 + 8 + 8 + 3 + 1 + 1 + 1) 1
        [((readBuffer t18 256 96).cast h768.symm, oracle.compression ((readBuffer t18 256 96).cast h768.symm))] := by
      have p1 := (hpre11.trans hrSel).trans ((hcp0.trans hcp1).trans hcp2)
      have p2 := ((h120.trans h121).trans h122).trans ((h123.trans h124).trans h125)
      simpa only [Nat.add_assoc, List.nil_append, List.append_nil] using p1.trans p2
    refine .continued t21 _ 1 _ (by omega) (by omega) hsteps_all
      ⟨rfl, hge64, rfl, hfix20.of_agree (fun r _ => k_getReg_setPC t20 _ r), ?_, ?_, ?_,
        (k_getReg_setPC t20 _ .x28).trans hx28_20, ?_, ?_, ?_⟩
    · simp only [t21, t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x9)]
      rw [hreg19 .x9]; simp only [t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg15_12 .x9 (by decide)).trans (hreg12_s .x9 (by decide) (by decide) (by decide) (by decide) (by decide))
    · simp only [t21, t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x19)]
      rw [hreg19 .x19]; simp only [t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
      exact (hreg15_12 .x19 (by decide)).trans (hreg12_s .x19 (by decide) (by decide) (by decide) (by decide) (by decide))
    · simp only [t21, t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x20)]
      rw [hreg19 .x20]; simp only [t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        (hreg15_12 .x20 (by decide)).trans ((hreg12_s .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20),
        show signExtend12 64#12 = BitVec.ofNat 64 64 by decide, k_bv_add, Nat.add_assoc]
    · have hm21 : t21.mem = t19.mem := by simp only [t21, t20, k_mem_setPC, k_mem_setReg]
      rw [(MemEqOutside.of_mem_eq hm21 0 0).readBuffer_eq (by omega) (by omega), hdig_buf]
      have hcast : (readBuffer t18 256 96).cast h768.symm = inp.cast h768.symm :=
        congrArg (·.cast h768.symm) hinp_18
      rw [hcast]
    · have hm21 : t21.mem = t19.mem := by simp only [t21, t20, k_mem_setPC, k_mem_setReg]
      exact (hfr_s15.mono (by omega) (by omega)).trans
        ((MemEqOutside.of_mem_eq hmem18 256 480).trans
          ((hfr19.mono (by omega) (by omega)).trans
            (MemEqOutside.of_mem_eq hm21 256 480)))
    · unfold InTrace; rw [hinp_18]; exact List.mem_cons_self

private theorem check_climb_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof) :
    ∀ steps v off (s : MachineState),
      v < CAP_LEAF_LO → climbStepsFrom v = steps →
      off ≤ input.proof.length → off % 8 = 0 →
      s.pc = kPcAt 79 → CheckFixedRegs input s →
      HighMemPreserved (submission.initialState .check input) s →
      s.getReg .x20 = BitVec.ofNat 64 (11072966688 + off) →
      s.getReg .x28 = BitVec.ofNat 64 v →
      let s0 := submission.initialState .check input
      let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
      let cur0 := readBuffer s 448 32
      PhaseOutcome oracle s (45 * steps) steps (input.proof.length < off + 64 * steps)
        (fun s' q tr =>
          q = steps ∧
          off + 64 * steps ≤ input.proof.length ∧
          s'.pc = kPcAt 126 ∧
          CheckFixedRegs input s' ∧
          s'.getReg .x9 = s.getReg .x9 ∧
          s'.getReg .x19 = s.getReg .x19 ∧
          s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + (off + 64 * steps)) ∧
          s'.getReg .x28 = BitVec.ofNat 64 (climbEndFrom v) ∧
          readBuffer s' 448 32 = evalClimb c96 s0 v off cur0 ∧
          MemEqOutside s s' 256 480 ∧
          ∀ x ∈ climbInputs c96 s0 v off cur0, InTrace h768 oracle tr x) := by
  intro steps
  induction steps with
  | zero =>
    intro v _ _ hv hcs; rw [climbStepsFrom_of_lt hv] at hcs; omega
  | succ k ih =>
    intro v off s hv hcs hoff_le hoff8 hpc hfix hhigh hx20 hx28
    have hcs_par : climbStepsFrom (parentNode v) = k := by
      rw [climbStepsFrom_of_lt hv] at hcs; omega
    have hone := check_climb_one h768 oracle input hvalid hv hoff_le hoff8 hpc hfix hhigh hx20 hx28
    by_cases hpar : parentNode v < CAP_LEAF_LO
    · refine (hone.bind_dep (fun hlt => by omega) (fun s1 q1 tr1 hp1 => by
        obtain ⟨hq1, hge1, hpc1, hfix1, hx9_1, hx19_1, hx20_1, hx28_1, hdig1, hfr1, htr1⟩ := hp1
        subst hq1
        have hpc79 : s1.pc = kPcAt 79 := by simpa only [hpar, ite_true] using hpc1
        have hhigh1 : HighMemPreserved (submission.initialState .check input) s1 :=
          hhigh.trans (hfr1.mono (by omega) (by omega))
        have hrest := ih (parentNode v) (off + 64) s1 hpar hcs_par hge1 (by omega)
          hpc79 hfix1 hhigh1 hx20_1 hx28_1
        refine hrest.weaken le_rfl le_rfl (fun hlt => by omega) (fun s2 q2 tr2 hp2 => by
          obtain ⟨hq2, hge2, hpc2, hfix2, hx9_2, hx19_2, hx20_2, hx28_2, hdig2, hfr2, htr2⟩ := hp2
          let s0 := submission.initialState .check input
          let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
          have hdig1' : readBuffer s1 448 32 = c96 (stepInput v (readBuffer s 448 32)
              (readBuffer s0 (11072966688 + off) 32, readBuffer s0 (11072966688 + off + 32) 32)) := hdig1
          refine ⟨by omega, by omega, hpc2, hfix2, hx9_2.trans hx9_1, hx19_2.trans hx19_1,
            by simpa only [show off + 64 + 64 * k = off + 64 * (k + 1) by omega] using hx20_2,
            by rw [climbEndFrom_of_lt hv]; exact hx28_2,
            ?_, hfr1.trans hfr2, ?_⟩
          · change readBuffer s2 448 32 = evalClimb c96 s0 v off (readBuffer s 448 32)
            rw [evalClimb_of_lt c96 s0 hv off _, ← hdig1']; exact hdig2
          · intro x hx
            change x ∈ climbInputs c96 s0 v off (readBuffer s 448 32) at hx
            rw [climbInputs_of_lt c96 s0 hv off _] at hx
            dsimp only at hx
            rcases List.mem_cons.mp hx with rfl | htail
            · exact htr1.append_left
            · rw [← hdig1'] at htail
              exact (htr2 x htail).append_right))).weaken (by omega) (by omega) id (fun _ _ _ h => h)
    · have hk0 : k = 0 := by rw [climbStepsFrom_of_ge (by omega)] at hcs_par; omega
      subst hk0
      refine hone.weaken (by omega) (by omega) (fun hlt => by omega) (fun s1 q1 tr1 hp1 => by
        obtain ⟨hq1, hge1, hpc1, hfix1, hx9_1, hx19_1, hx20_1, hx28_1, hdig1, hfr1, htr1⟩ := hp1
        let s0 := submission.initialState .check input
        let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
        refine ⟨hq1, by omega, by simpa only [hpar, ite_false] using hpc1, hfix1, hx9_1, hx19_1,
          by simpa only [show off + 64 * 1 = off + 64 by omega] using hx20_1,
          by rw [climbEndFrom_of_lt hv, climbEndFrom_of_ge (by omega)]; exact hx28_1,
          ?_, hfr1, ?_⟩
        · change readBuffer s1 448 32 = evalClimb c96 s0 v off (readBuffer s 448 32)
          rw [evalClimb_of_lt c96 s0 hv off _, evalClimb_of_ge c96 s0 (v := parentNode v) (by omega) _ _]
          exact hdig1
        · intro x hx
          change x ∈ climbInputs c96 s0 v off (readBuffer s 448 32) at hx
          rw [climbInputs_of_lt c96 s0 hv off _] at hx
          dsimp only at hx
          rw [climbInputs_of_ge c96 s0 (v := parentNode v) (by omega) _ _] at hx
          rcases List.mem_cons.mp hx with rfl | hnil
          · exact htr1
          · simp at hnil)

/-! ### 6. Cap-Leaf Store / Duplicate Check (`pc[126..154]`) and Full Position Loop -/

private theorem check_cap_store_or_dup (oracle : Oracle) (input : CheckInput)
    {c : Nat} {isMarked : Bool} {s : MachineState}
    (hc : c < 286) (hpc : s.pc = kPcAt 126) (hfix : CheckFixedRegs input s)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 (CAP_LEAF_LO + c))
    (hmark : s.getByte (BitVec.ofNat 64 (4096 + c)) = if isMarked then 1#8 else 0#8) :
    PhaseOutcome oracle s 21 0
      (isMarked = true ∧ readBuffer s 448 32 ≠ readBuffer s (8192 + 32 * c) 32)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        s'.pc = kPcAt 155 ∧
        CheckFixedRegs input s' ∧
        s'.getReg .x9 = s.getReg .x9 ∧
        s'.getReg .x19 = s.getReg .x19 ∧
        s'.getReg .x20 = s.getReg .x20 ∧
        (isMarked = true → readBuffer s 448 32 = readBuffer s (8192 + 32 * c) 32 ∧ s'.mem = s.mem) ∧
        (isMarked = false →
          s'.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 ∧
          readBuffer s' (8192 + 32 * c) 32 = readBuffer s 448 32 ∧
          (∀ a < 2 ^ 64, a ≠ 4096 + c → (a < 8192 + 32 * c ∨ 8192 + 32 * c + 32 ≤ a) →
            s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)))) := by
  have hcl := capLeafLo_eq
  -- pc[126..130]
  have h126 := k_step_SUB (oracle := oracle) (s := s) (idx := 126) (by decide) hpc rfl
  let t1 := (s.setReg .x28 (s.getReg .x28 - s.getReg .x23)).setPC (kPcAt 127)
  have h127 := k_step_ADD (oracle := oracle) (s := t1) (idx := 127) (by decide) rfl rfl
  let t2 := (t1.setReg .x6 (t1.getReg .x24 + t1.getReg .x28)).setPC (kPcAt 128)
  have h128 := k_step_SLLI (oracle := oracle) (s := t2) (idx := 128) (by decide) rfl rfl
  let t3 := (t2.setReg .x7 (t2.getReg .x28 <<< (5#6 : BitVec 6).toNat)).setPC (kPcAt 129)
  have h129 := k_step_ADD (oracle := oracle) (s := t3) (idx := 129) (by decide) rfl rfl
  let t4 := (t3.setReg .x7 (t3.getReg .x25 + t3.getReg .x7)).setPC (kPcAt 130)
  have hx28_1 : t1.getReg .x28 = BitVec.ofNat 64 c := by
    simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      hx28, hfix.x23]
    rw [k_bv_sub _ _ (by omega), Nat.add_sub_cancel_left]
  have hx6_4 : t4.getReg .x6 = BitVec.ofNat 64 (4096 + c) := by
    simp only [t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, hfix.x24, hx28_1, k_bv_add]
  have hx7_4 : t4.getReg .x7 = BitVec.ofNat 64 (8192 + 32 * c) := by
    have h7_3 : t3.getReg .x7 = BitVec.ofNat 64 (32 * c) := by
      simp only [t3, t2, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx28_1, show (5#6 : BitVec 6).toNat = 5 by decide, k_bv_shl]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h25_3 : t3.getReg .x25 = BitVec.ofNat 64 8192 := by
      simp only [t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x25]
    simp only [t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h25_3, h7_3, k_bv_add]
  have ha130 : t4.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
    rw [hx6_4, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
  have h130 := k_step_LBU (oracle := oracle) (s := t4) (idx := 130) (by decide) rfl rfl
    (by rw [ha130]; exact k_accessValid _ 1 (by omega) (by omega))
  let t5 := (t4.setReg .x15 ((t4.getByte (t4.getReg .x6 + signExtend12 0#12)).zeroExtend 64)).setPC (kPcAt 131)
  have hmem5 : t5.mem = s.mem := by simp only [t5, t4, t3, t2, t1, k_mem_setPC, k_mem_setReg]
  have hpre5 : StepsTo oracle s t5 5 0 [] := by
    simpa only [show 1 + 1 + 1 + 1 + 1 = 5 from rfl, List.append_nil] using
      ((h126.trans h127).trans (h128.trans h129)).trans h130
  have hx15_5 : t5.getReg .x15 = if isMarked then 1#64 else 0#64 := by
    simp only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha130]
    have hb : t4.getByte (BitVec.ofNat 64 (4096 + c)) = s.getByte (BitVec.ofNat 64 (4096 + c)) := by
      simp only [t4, t3, t2, t1, k_getByte_setPC, k_getByte_setReg]
    rw [hb, hmark]; exact k_bool_byte_zext isMarked
  have hreg5_s : ∀ r, r ≠ .x28 → r ≠ .x6 → r ≠ .x7 → r ≠ .x15 → t5.getReg r = s.getReg r := fun r h28 h6 h7 h15 => by
    simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h28)]
  have hfix5 : CheckFixedRegs input t5 := hfix.of_agree (fun r hr =>
    hreg5_s r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl))
  cases isMarked with
  | false =>
    have h131 := k_step_BNE_not_taken (oracle := oracle) (s := t5) (idx := 131) (by decide) rfl rfl
      (by rw [hx15_5, k_getReg_x0]; rfl)
    let u1 := t5.setPC (kPcAt 132)
    have h132 := k_step_ADDI (oracle := oracle) (s := u1) (idx := 132) (by decide) rfl rfl
    let u2 := (u1.setReg .x15 (u1.getReg .x0 + signExtend12 1#12)).setPC (kPcAt 133)
    have hx6_u2 : u2.getReg .x6 = BitVec.ofNat 64 (4096 + c) := by
      simp only [u2, u1, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx6_4]
    have ha133 : u2.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + c) := by
      rw [hx6_u2, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    have h133 := k_step_SB (oracle := oracle) (s := u2) (idx := 133) (by decide) rfl rfl
      (by rw [ha133]; exact k_accessValid _ 1 (by omega) (by omega))
    let u3 := (u2.setByte (u2.getReg .x6 + signExtend12 0#12) ((u2.getReg .x15).truncate 8)).setPC (kPcAt 134)
    have htr1 : (u2.getReg .x15).truncate 8 = 1#8 := by
      have h15 : u2.getReg .x15 = 1#64 := by
        simp only [u2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
      rw [h15]; decide
    have hx26_u3 : u3.getReg .x26 = BitVec.ofNat 64 256 := by
      simp only [u3, u2, u1, MachineState.getReg_setPC, k_getReg_setByte,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x26), hfix5.x26]
    have hx7_u3 : u3.getReg .x7 = BitVec.ofNat 64 (8192 + 32 * c) := by
      simp only [u3, u2, u1, t5, MachineState.getReg_setPC, k_getReg_setByte,
        MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx7_4]
    obtain ⟨u4, hcp, hpc4, hreg4, hbuf4, hfr4⟩ := k_copy_32 oracle (s := u3) (idx := 134) (tmp := .x29)
      (srcReg := .x26) (dstReg := .x7) (srcOff := 192) (dstOff := 0) (by decide) rfl (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      hx26_u3 hx7_u3 (by omega) (by omega) (by omega) (by omega) (by omega)
    have h142 := k_step_JAL_x0 (oracle := oracle) (s := u4) (idx := 142) (tgt := 155) (by decide) hpc4 rfl k_tgt_142
    let u5 := u4.setPC (kPcAt 155)
    have hreg_u5 : ∀ r, r ≠ .x29 → r ≠ .x15 → u5.getReg r = t5.getReg r := fun r h29 h15 => by
      simp only [u5, MachineState.getReg_setPC]
      rw [hreg4 r h29]
      simp only [u3, u2, u1, MachineState.getReg_setPC, k_getReg_setByte,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15)]
    have hfr_s_u3 : MemEqOutside s u3 (4096 + c) (4096 + c + 1) := by
      intro a ha hout
      simp only [u3, k_getByte_setPC, ha133, set_byte_read,
        k_bv_ne ha (show 4096 + c < 2 ^ 64 by omega) (by omega), ite_false]
      have hm_u2 : u2.mem = s.mem := by simp only [u2, u1, k_mem_setPC, k_mem_setReg, hmem5]
      simp only [MachineState.getByte, MachineState.getMem, hm_u2]
    refine .continued u5 17 0 [] (by omega) (by omega)
      (by simpa only [show 5 + 1 + 1 + 1 + 8 + 1 = 17 from rfl, List.append_nil, Nat.add_assoc] using
        (((hpre5.trans h131).trans (h132.trans h133)).trans hcp).trans h142)
      ⟨rfl, rfl, rfl,
        hfix5.of_agree (fun r hr => hreg_u5 r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl)),
        (hreg_u5 .x9 (by decide) (by decide)).trans (hreg5_s .x9 (by decide) (by decide) (by decide) (by decide)),
        (hreg_u5 .x19 (by decide) (by decide)).trans (hreg5_s .x19 (by decide) (by decide) (by decide) (by decide)),
        (hreg_u5 .x20 (by decide) (by decide)).trans (hreg5_s .x20 (by decide) (by decide) (by decide) (by decide)),
        (fun h => by cases h), ?_⟩
    intro _
    refine ⟨?_, ?_, ?_⟩
    · simp only [u5, k_getByte_setPC]
      rw [hfr4 (4096 + c) (by omega) (by omega)]
      simp only [u3, k_getByte_setPC, ha133, htr1, set_byte_read, ite_true]
    · simp only [u5, readBuffer, k_getByte_setPC]
      change readBuffer u4 (8192 + 32 * c) 32 = readBuffer s 448 32
      simpa only [Nat.add_zero, show (256 + 192 : Nat) = 448 from rfl] using
        hbuf4.trans (hfr_s_u3.readBuffer_eq (by omega) (by omega))
    · intro a ha hne hout
      simp only [u5, k_getByte_setPC]
      exact (hfr4 a ha (by simpa only [Nat.add_zero] using hout)).trans (hfr_s_u3 a ha (by omega))
  | true =>
    have h131 := k_step_BNE_taken (oracle := oracle) (s := t5) (idx := 131) (tgt := 143) (by decide) rfl rfl
      (by rw [hx15_5, k_getReg_x0]; decide) k_tgt_131
    let u1 := t5.setPC (kPcAt 143)
    have hcmp := k_cmp32_or_reject oracle (s := u1) (idx := 143) (aReg := .x26) (bReg := .x7)
      (aOff := 192) (bOff := 0) (a := 256) (b := 8192 + 32 * c)
      (by decide) rfl (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      k_tgt_145 k_tgt_148 k_tgt_151 k_tgt_154
      (by decide) (by decide) (by decide) (by decide)
      hfix5.x26
      (by simp only [u1, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx7_4])
      (by omega) (by omega) (by omega) (by omega)
    have hmem_u1 : u1.mem = s.mem := hmem5
    have hrb_a : readBuffer u1 (256 + 192) 32 = readBuffer s 448 32 :=
      (MemEqOutside.of_mem_eq hmem_u1 0 0).readBuffer_eq (by omega) (by omega)
    have hrb_b : readBuffer u1 (8192 + 32 * c + 0) 32 = readBuffer s (8192 + 32 * c) 32 :=
      (MemEqOutside.of_mem_eq hmem_u1 0 0).readBuffer_eq (by omega) (by omega)
    have hpre6 : StepsTo oracle s u1 6 0 [] := by
      simpa only [show 5 + 1 = 6 from rfl, List.append_nil] using hpre5.trans h131
    refine (hpre6.prepend_pure hcmp).weaken (by omega) (by omega)
      (fun hne => ⟨rfl, by rwa [hrb_a, hrb_b] at hne⟩)
      (fun s' q tr hp => by
        obtain ⟨hq, htr, hpc', heq, hmem', hreg'⟩ := hp
        rw [hrb_a, hrb_b] at heq
        refine ⟨hq, htr, hpc',
          hfix5.of_agree (fun r hr => hreg' r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl)),
          (hreg' .x9 (by decide) (by decide)).trans (hreg5_s .x9 (by decide) (by decide) (by decide) (by decide)),
          (hreg' .x19 (by decide) (by decide)).trans (hreg5_s .x19 (by decide) (by decide) (by decide) (by decide)),
          (hreg' .x20 (by decide) (by decide)).trans (hreg5_s .x20 (by decide) (by decide) (by decide) (by decide)),
          fun _ => ⟨heq, hmem'.trans hmem_u1⟩, fun h => by cases h⟩)

structure PosLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (n : Nat) (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed    : CheckFixedRegs input s
  high     : HighMemPreserved (submission.initialState .check input) s
  pc       : s.pc = if n = input.positions.card then kPcAt 156 else kPcAt 29
  x9       : s.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * n)
  x19      : s.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * n)
  x20      : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + posRecordOff input.positions n)
  len_le   : posRecordOff input.positions n ≤ input.proof.length
  marks_lo : ∀ c < 286, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if posMarked input.positions n c then 1#8 else 0#8
  marks_hi : ∀ u, 286 ≤ u → u < 429 → s.getByte (BitVec.ofNat 64 (4096 + u)) = 0#8
  vals_hi  : ∀ a, 8192 + 32 * 286 ≤ a → a < 8192 + 32 * 429 → s.getByte (BitVec.ofNat 64 a) = 0#8
  pos_done : ∀ ord < n,
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let i := posAt input.positions ord
    let off := posRecordOff input.positions ord
    let salt := readBuffer s0 (11072966688 + off) 24
    readBuffer s (8192 + 32 * capLeafOf i) 32 = posCapDigest c96 s0 input ord ∧
    (∀ x ∈ leafInputsOf c96 i salt (valAt input ord), InTrace h768 oracle tr x) ∧
    (∀ x ∈ climbInputs c96 s0 i.val (off + 24) (leafDigest c96 i salt (valAt input ord)),
      InTrace h768 oracle tr x)

private theorem check_pos_iter (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    {n : Nat} (hn : n < input.positions.card) {s : MachineState} {tr : CompressionReplies}
    (hinv : PosLoopInv h768 oracle input n s tr) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle s 520 14
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' _ tr' => PosLoopInv h768 oracle input (n + 1) s' (tr ++ tr')) := by
  intro s0 c96
  have hcard_le := k_card_le input.positions
  have hpc29 : s.pc = kPcAt 29 := by
    have h := hinv.pc; simp only [Nat.ne_of_lt hn, ite_false] at h; exact h
  let off := posRecordOff input.positions n
  let i := posAt input.positions n
  let c := capLeafOf i
  have hc_lt : c < 286 := by rw [← capLeaves_eq]; exact capLeafOf_lt i
  have hi_lt : i.val < CAP_LEAF_LO := by
    have h1 : i.val < 16777216 := i.isLt; rw [capLeafLo_eq]; omega
  have hcs_le : climbStepsFrom i.val ≤ 10 := climbStepsFrom_le_10 i.val
  have hoff_next : posRecordOff input.positions (n + 1) = off + 24 + 64 * climbStepsFrom i.val := by
    change off + (24 + 64 * climbStepsFrom i.val) = _; omega
  have hleaf := check_step_leaf h768 oracle input hvalid hn hinv.len_le (posRecordOff_mod8 _ _)
    hpc29 hinv.fixed hinv.high hinv.x9 hinv.x19 hinv.x20
  cases hleaf with
  | rejected k1 q1 tr1 hlt24 hk1 hq1 hh1 =>
    refine .rejected k1 q1 tr1 (fun hcon => ?_) (by omega) (by omega) hh1
    have hle := posRecordOff_mono input.positions (show n + 1 ≤ input.positions.card by omega)
    have := hcon.1; omega
  | continued s1 k1 q1 tr1 hk1 hq1 hst1 hp1 =>
    obtain ⟨hq1_eq, hge24, hpc79, hfix1, hx9_1, hx19_1, hx20_1, hx28_1, hdig1, hfr1, htr1⟩ := hp1
    subst hq1_eq
    have hhigh1 : HighMemPreserved s0 s1 := hinv.high.trans (hfr1.mono (by omega) (by omega))
    have hclimb := check_climb_loop h768 oracle input hvalid (climbStepsFrom i.val) i.val (off + 24) s1
      hi_lt rfl hge24 (by have := posRecordOff_mod8 input.positions n; omega)
      hpc79 hfix1 hhigh1 hx20_1 hx28_1
    cases hclimb with
    | rejected k2 q2 tr2 hlt_c hk2 hq2 hh2 =>
      refine .rejected (k1 + k2) (4 + q2) (tr1 ++ tr2) (fun hcon => ?_) (by omega) (by omega)
        (hst1.halt hh2)
      have hle := posRecordOff_mono input.positions (show n + 1 ≤ input.positions.card by omega)
      have := hcon.1; omega
    | continued s2 k2 q2 tr2 hk2 hq2 hst2 hp2 =>
      obtain ⟨hq2_eq, hge_c, hpc126, hfix2, hx9_2, hx19_2, hx20_2, hx28_2, hdig2, hfr2, htr2⟩ := hp2
      subst hq2_eq
      have hfr_s_s2 : MemEqOutside s s2 256 480 := hfr1.trans hfr2
      have hhigh2 : HighMemPreserved s0 s2 := hinv.high.trans (hfr_s_s2.mono (by omega) (by omega))
      have hx28_c : s2.getReg .x28 = BitVec.ofNat 64 (CAP_LEAF_LO + c) := by
        rw [hx28_2, climbEndFrom_eq_capLeafOf]
      have hmark2 : s2.getByte (BitVec.ofNat 64 (4096 + c)) =
          if posMarked input.positions n c then 1#8 else 0#8 := by
        rw [hfr_s_s2 (4096 + c) (by omega) (by omega), hinv.marks_lo c hc_lt]
      have hdig2_eq : readBuffer s2 448 32 = posCapDigest c96 s0 input n := by
        rw [hdig2, hdig1]; rfl
      have hcap := check_cap_store_or_dup oracle input hc_lt hpc126 hfix2 hx28_c hmark2
      cases hcap with
      | rejected k3 q3 tr3 hfail3 hk3 hq3 hh3 =>
        refine .rejected (k1 + k2 + k3) (4 + climbStepsFrom i.val + q3) (tr1 ++ tr2 ++ tr3)
          (fun hcon => ?_) (by omega) (by omega) ((hst1.trans hst2).halt hh3)
        obtain ⟨hmk, hne_dig⟩ := hfail3
        simp only [posMarked, decide_eq_true_eq] at hmk
        obtain ⟨ord', hord'_lt, _, hord'_c⟩ := hmk
        have hprev := (hinv.pos_done ord' hord'_lt).1
        rw [hdig2_eq, hfr_s_s2.readBuffer_eq (by omega) (by omega), ← hord'_c, hprev] at hne_dig
        exact hne_dig (hcon.2 n hn ord' (by omega) hord'_c.symm)
      | continued s3 k3 q3 tr3 hk3 hq3 hst3 hp3 =>
        obtain ⟨hq3_eq, htr3_eq, hpc155, hfix3, hx9_3, hx19_3, hx20_3, htrue3, hfalse3⟩ := hp3
        subst hq3_eq; subst htr3_eq
        have hx9_fin : s3.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (n + 1)) :=
          hx9_3.trans (hx9_2.trans hx9_1)
        have hx19_fin : s3.getReg .x19 = BitVec.ofNat 64 (6777999392 + 256 * (n + 1)) :=
          hx19_3.trans (hx19_2.trans hx19_1)
        have hx20_fin : s3.getReg .x20 = BitVec.ofNat 64 (11072966688 + posRecordOff input.positions (n + 1)) := by
          rw [hx20_3, hx20_2, hoff_next]
        -- pc[155]: isolated backward branch BNE x9 x18 -> 29
        let s4 := s3.setPC (if n + 1 = input.positions.card then kPcAt 156 else kPcAt 29)
        have h155 : StepsTo oracle s3 s4 1 0 [] := by
          by_cases hend : n + 1 = input.positions.card
          · simpa only [s4, hend, ite_true] using
              k_step_155_done oracle (s := s3) hpc155 hx9_fin (by rw [hfix3.x18, hend])
          · simpa only [s4, hend, ite_false] using
              k_step_155_back oracle (s := s3) hpc155 hx9_fin hfix3.x18 (by omega) (by omega) (by omega)
        -- Unify byte-level properties of s4 from true/false branch
        have hbyte_outside : ∀ a < 2 ^ 64, a ≠ 4096 + c →
            (a < 8192 + 32 * c ∨ 8192 + 32 * c + 32 ≤ a) →
            s4.getByte (BitVec.ofNat 64 a) = s2.getByte (BitVec.ofNat 64 a) := fun a ha hne hout => by
          simp only [s4, k_getByte_setPC]
          cases hmk : posMarked input.positions n c with
          | true =>
            have hmeq := (htrue3 hmk).2
            simp only [MachineState.getByte, MachineState.getMem, hmeq]
          | false =>
            exact (hfalse3 hmk).2.2 a ha hne hout
        have hdig_c : readBuffer s4 (8192 + 32 * c) 32 = posCapDigest c96 s0 input n := by
          change readBuffer s3 (8192 + 32 * c) 32 = _
          cases hmk : posMarked input.positions n c with
          | true =>
            obtain ⟨heq, hmeq⟩ := htrue3 hmk
            rw [(MemEqOutside.of_mem_eq hmeq 0 0).readBuffer_eq (by omega) (by omega), ← heq, hdig2_eq]
          | false =>
            rw [(hfalse3 hmk).2.1, hdig2_eq]
        have hmark_c : s4.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8 := by
          simp only [s4, k_getByte_setPC]
          cases hmk : posMarked input.positions n c with
          | true =>
            have hmeq := (htrue3 hmk).2
            simp only [MachineState.getByte, MachineState.getMem, hmeq]
            change s2.getByte (BitVec.ofNat 64 (4096 + c)) = 1#8
            rw [hmark2, hmk]; rfl
          | false =>
            exact (hfalse3 hmk).1
        have hval_prev : ∀ c' < 286, c' ≠ c →
            readBuffer s4 (8192 + 32 * c') 32 = readBuffer s (8192 + 32 * c') 32 := fun c' hc' hne => by
          apply k_readBuffer_congr2; intro j hj
          rw [hbyte_outside (8192 + 32 * c' + j) (by omega) (by omega) (by omega),
            hfr_s_s2 (8192 + 32 * c' + j) (by omega) (by omega)]
        have hval_eq_if_c : ∀ ord' < n, capLeafOf (posAt input.positions ord') = c →
            posCapDigest c96 s0 input ord' = posCapDigest c96 s0 input n := fun ord' hord' heqc => by
          have hmk : posMarked input.positions n c = true := by
            simp only [posMarked, decide_eq_true_eq]; exact ⟨ord', hord', by omega, heqc⟩
          have heq := (htrue3 hmk).1
          rw [hdig2_eq, hfr_s_s2.readBuffer_eq (by omega) (by omega), ← heqc,
            (hinv.pos_done ord' hord').1] at heq
          exact heq.symm
        refine .continued s4 (k1 + k2 + k3 + 1) (4 + climbStepsFrom i.val + 0 + 0)
          (tr1 ++ tr2 ++ [] ++ []) (by omega) (by omega)
          (((hst1.trans hst2).trans hst3).trans h155)
          ⟨hfix3.of_agree (fun r _ => k_getReg_setPC s3 _ r),
            fun a ha hout => (hbyte_outside a ha (by omega) (by omega)).trans (hhigh2 a ha hout),
            rfl,
            (k_getReg_setPC s3 _ .x9).trans hx9_fin,
            (k_getReg_setPC s3 _ .x19).trans hx19_fin,
            (k_getReg_setPC s3 _ .x20).trans hx20_fin,
            by omega,
            fun c' hc' => by
              rw [posMarked_succ input.positions hn c']
              by_cases heq : c' = c
              · rw [heq]
                change s4.getByte (BitVec.ofNat 64 (4096 + c)) =
                  if (posMarked input.positions n c || decide (c = c)) = true then 1#8 else 0#8
                simp only [decide_true, Bool.or_true, ite_true, hmark_c]
              · rw [show decide (c = c') = false from decide_eq_false (Ne.symm heq), Bool.or_false]
                rw [hbyte_outside (4096 + c') (by omega) (by omega) (by omega),
                  hfr_s_s2 (4096 + c') (by omega) (by omega), hinv.marks_lo c' hc'],
            fun u hu1 hu2 => by
              rw [hbyte_outside (4096 + u) (by omega) (by omega) (by omega),
                hfr_s_s2 (4096 + u) (by omega) (by omega), hinv.marks_hi u hu1 hu2],
            fun a ha1 ha2 => by
              rw [hbyte_outside a (by omega) (by omega) (by omega),
                hfr_s_s2 a (by omega) (by omega), hinv.vals_hi a ha1 ha2],
            fun ord' hord' => by
              by_cases hlt' : ord' < n
              · obtain ⟨hd', hl', hc'⟩ := hinv.pos_done ord' hlt'
                refine ⟨?_, fun x hx => (hl' x hx).append_left, fun x hx => (hc' x hx).append_left⟩
                by_cases heqc : capLeafOf (posAt input.positions ord') = c
                · rw [heqc, hdig_c, ← hval_eq_if_c ord' hlt' heqc]
                · have hc'_lt : capLeafOf (posAt input.positions ord') < 286 := by
                    rw [← capLeaves_eq]; exact capLeafOf_lt _
                  rw [hval_prev _ hc'_lt heqc, hd']
              · have heq : ord' = n := by omega
                subst heq
                refine ⟨hdig_c,
                  fun x hx => by
                    have h := (htr1 x hx).append_left (t2 := tr2 ++ [] ++ [])
                    simpa only [List.append_nil, List.append_assoc] using h.append_right (t1 := tr),
                  fun x hx => by
                    rw [← hdig1] at hx
                    have h := (htr2 x hx).append_right (t1 := tr1)
                    simpa only [List.append_nil, List.append_assoc] using h.append_right (t1 := tr)⟩⟩

theorem check_pos_loop (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.card ≠ 0) (s1 : MachineState)
    (hinit : PosLoopInv h768 oracle input 0 s1 []) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    PhaseOutcome oracle s1 (520 * input.positions.card) (14 * input.positions.card)
      (¬ PosConsistent c96 s0 input input.positions.card)
      (fun s' _ tr => PosLoopInv h768 oracle input input.positions.card s' tr) := by
  intro s0 c96
  suffices h : ∀ n ≤ input.positions.card,
      PhaseOutcome oracle s1 (520 * n) (14 * n)
        (¬ PosConsistent c96 s0 input input.positions.card)
        (fun s' _ tr => PosLoopInv h768 oracle input n s' tr) from
    h input.positions.card le_rfl
  intro n hn
  induction n with
  | zero =>
    exact .continued s1 0 0 [] le_rfl le_rfl (StepsTo.refl oracle s1) hinit
  | succ k ih =>
    have hprev := ih (by omega)
    refine (hprev.bind_dep id (fun sk _ trk hinvk =>
      check_pos_iter h768 oracle input hvalid (by omega) hinvk)).weaken
      (by omega) (by omega) id (fun _ _ _ h => h)

end CommitGolfCandidate
