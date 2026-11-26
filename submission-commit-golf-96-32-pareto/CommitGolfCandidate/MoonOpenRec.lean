import CommitGolfCandidate.MoonOpenSlowTail

/-! Parameterized 8-way cyclic record loop (`rec_r0..rec_r7`, fast 9-tail path, `edge12_14`
8-tail path, `skip12_14` 7-tail path, `slow_stub → slow_body`) and the full multi-record
induction `openRuns_rec_all` proving the exact amortized non-flush bound
`8 * recCycNf + phi8 rEnd ≤ 3453 * positions.card + 16 + (if anySlow then 8 * 168 else 0)`. -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Pure Helpers: `jalOff`, Fast-Class `recordFwd`/`recordTails`, and Record Length Bounds -/

def jalOff (src tgt : Nat) : BitVec 21 :=
  if src ≤ tgt then BitVec.ofNat 21 (4 * (tgt - src))
  else BitVec.ofNat 21 (2097152 - 4 * (src - tgt))

theorem pcAt_add_jalOff (src tgt : Nat) (h1 : src ≤ OPEN_CODE_LEN) (h2 : tgt ≤ OPEN_CODE_LEN) :
    pcAt src + signExtend21 (jalOff src tgt) = pcAt tgt := by
  unfold jalOff; split_ifs with h
  · exact pcAt_add_pos21 src tgt h (by unfold OPEN_CODE_LEN at *; omega)
  · exact pcAt_add_neg21 src tgt (by omega) (by unfold OPEN_CODE_LEN at *; omega)

private theorem l0SiblingsProof_of_lt (nodes : Nat → Nat → Digest) (i : Index) (h : i.val / 3 < FULL_TRIPLETS) :
    l0SiblingsProof nodes i =
      bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32 := by
  unfold l0SiblingsProof l0Sib1Idx l0Sib2Idx
  simp only [show i.val / 3 ≠ FULL_TRIPLETS by omega, ↓reduceIte]
  have hr : i.val % 3 < 3 := Nat.mod_lt _ (by omega)
  generalize i.val % 3 = r at hr
  interval_cases r <;> simp

theorem record_fast_eq (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (i : Index) (hg : i.val / 3 < 5592064) (h13 : (i.val / 3) >>> 12 < 1364) :
    let g := i.val / 3
    recordFwd nodes salts i =
      bitsToBytes (salts i) 24 ++
      bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32 ++
      bitsToBytes (nodes 1 (g ^^^ 1)) 32 ++
      bitsToBytes (nodes 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (nodes 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (nodes 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (nodes 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (nodes 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (nodes 7 ((g >>> 6) ^^^ 1)) 29 ++
      bitsToBytes (nodes 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (nodes 9 ((g >>> 8) ^^^ 1)) 29 ++
      bitsToBytes (nodes 10 ((g >>> 9) ^^^ 1)) 29 ++ bitsToBytes (nodes 11 ((g >>> 10) ^^^ 1)) 29 ++
      bitsToBytes (nodes 12 ((g >>> 11) ^^^ 1)) 29 ++ bitsToBytes (nodes 13 ((g >>> 12) ^^^ 1)) 29 ++
      bitsToBytes (nodes 14 ((g >>> 13) ^^^ 1)) 29 ∧
    recordTails nodes i =
      [tail6 (nodes 6 ((g >>> 5) ^^^ 1)), tail6 (nodes 7 ((g >>> 6) ^^^ 1)),
       tail6 (nodes 8 ((g >>> 7) ^^^ 1)), tail6 (nodes 9 ((g >>> 8) ^^^ 1)),
       tail6 (nodes 10 ((g >>> 9) ^^^ 1)), tail6 (nodes 11 ((g >>> 10) ^^^ 1)),
       tail6 (nodes 12 ((g >>> 11) ^^^ 1)), tail6 (nodes 13 ((g >>> 12) ^^^ 1)),
       tail6 (nodes 14 ((g >>> 13) ^^^ 1))] := by
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have h1214 := level12_14_of_idx13 g hg
  have hl12 : ((g >>> 11) ^^^ 1) < levelSize 12 := h1214.1.mpr (by omega)
  have hl14 : ((g >>> 13) ^^^ 1) < levelSize 14 := h1214.2.mpr h13
  constructor
  · unfold recordFwd; dsimp only
    rw [show i.val / 3 = g from rfl, l0SiblingsProof_of_lt nodes i hf.1, binPathFwd_unfold]
    simp only [hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1,
      hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1,
      hl12, hf.2.2.2.2.2.2.2.2.2.2.2.1, hl14, ↓reduceIte, List.append_assoc]
  · unfold recordTails
    rw [show i.val / 3 = g from rfl, binPathTails_unfold]
    simp only [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1,
      hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1, hl12, hf.2.2.2.2.2.2.2.2.2.2.2.1,
      hl14, ↓reduceIte, List.singleton_append]; rfl

theorem record_skip14_eq (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (i : Index) (hg : i.val / 3 < 5592064) (h13 : (i.val / 3) >>> 12 = 1364) :
    let g := i.val / 3
    recordFwd nodes salts i =
      bitsToBytes (salts i) 24 ++
      bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32 ++
      bitsToBytes (nodes 1 (g ^^^ 1)) 32 ++
      bitsToBytes (nodes 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (nodes 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (nodes 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (nodes 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (nodes 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (nodes 7 ((g >>> 6) ^^^ 1)) 29 ++
      bitsToBytes (nodes 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (nodes 9 ((g >>> 8) ^^^ 1)) 29 ++
      bitsToBytes (nodes 10 ((g >>> 9) ^^^ 1)) 29 ++ bitsToBytes (nodes 11 ((g >>> 10) ^^^ 1)) 29 ++
      bitsToBytes (nodes 12 ((g >>> 11) ^^^ 1)) 29 ++ bitsToBytes (nodes 13 ((g >>> 12) ^^^ 1)) 29 ∧
    recordTails nodes i =
      [tail6 (nodes 6 ((g >>> 5) ^^^ 1)), tail6 (nodes 7 ((g >>> 6) ^^^ 1)),
       tail6 (nodes 8 ((g >>> 7) ^^^ 1)), tail6 (nodes 9 ((g >>> 8) ^^^ 1)),
       tail6 (nodes 10 ((g >>> 9) ^^^ 1)), tail6 (nodes 11 ((g >>> 10) ^^^ 1)),
       tail6 (nodes 12 ((g >>> 11) ^^^ 1)), tail6 (nodes 13 ((g >>> 12) ^^^ 1))] := by
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have h1214 := level12_14_of_idx13 g hg
  have hl12 : ((g >>> 11) ^^^ 1) < levelSize 12 := h1214.1.mpr (by omega)
  have hnl14 : ¬ (((g >>> 13) ^^^ 1) < levelSize 14) := fun h => by have := h1214.2.mp h; omega
  constructor
  · unfold recordFwd; dsimp only
    rw [show i.val / 3 = g from rfl, l0SiblingsProof_of_lt nodes i hf.1, binPathFwd_unfold]
    simp only [hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1,
      hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1,
      hl12, hf.2.2.2.2.2.2.2.2.2.2.2.1, hnl14, ↓reduceIte, List.append_nil, List.append_assoc]
  · unfold recordTails
    rw [show i.val / 3 = g from rfl, binPathTails_unfold]
    simp only [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1,
      hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1, hl12, hf.2.2.2.2.2.2.2.2.2.2.2.1,
      hnl14, ↓reduceIte, List.append_nil, List.singleton_append]; rfl

theorem record_skip1214_eq (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (i : Index) (hg : i.val / 3 < 5592064) (h13 : (i.val / 3) >>> 12 = 1365) :
    let g := i.val / 3
    recordFwd nodes salts i =
      bitsToBytes (salts i) 24 ++
      bitsToBytes (nodes 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (nodes 0 (l0Sib2Idx i)) 32 ++
      bitsToBytes (nodes 1 (g ^^^ 1)) 32 ++
      bitsToBytes (nodes 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (nodes 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (nodes 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (nodes 5 ((g >>> 4) ^^^ 1)) 30 ++
      bitsToBytes (nodes 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (nodes 7 ((g >>> 6) ^^^ 1)) 29 ++
      bitsToBytes (nodes 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (nodes 9 ((g >>> 8) ^^^ 1)) 29 ++
      bitsToBytes (nodes 10 ((g >>> 9) ^^^ 1)) 29 ++ bitsToBytes (nodes 11 ((g >>> 10) ^^^ 1)) 29 ++
      bitsToBytes (nodes 13 ((g >>> 12) ^^^ 1)) 29 ∧
    recordTails nodes i =
      [tail6 (nodes 6 ((g >>> 5) ^^^ 1)), tail6 (nodes 7 ((g >>> 6) ^^^ 1)),
       tail6 (nodes 8 ((g >>> 7) ^^^ 1)), tail6 (nodes 9 ((g >>> 8) ^^^ 1)),
       tail6 (nodes 10 ((g >>> 9) ^^^ 1)), tail6 (nodes 11 ((g >>> 10) ^^^ 1)),
       tail6 (nodes 13 ((g >>> 12) ^^^ 1))] := by
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have h1214 := level12_14_of_idx13 g hg
  have hnl12 : ¬ (((g >>> 11) ^^^ 1) < levelSize 12) := fun h => by have := h1214.1.mp h; omega
  have hnl14 : ¬ (((g >>> 13) ^^^ 1) < levelSize 14) := fun h => by have := h1214.2.mp h; omega
  constructor
  · unfold recordFwd; dsimp only
    rw [show i.val / 3 = g from rfl, l0SiblingsProof_of_lt nodes i hf.1, binPathFwd_unfold]
    simp only [hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1,
      hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1,
      hnl12, hf.2.2.2.2.2.2.2.2.2.2.2.1, hnl14, ↓reduceIte, List.append_nil, List.append_assoc]
  · unfold recordTails
    rw [show i.val / 3 = g from rfl, binPathTails_unfold]
    simp only [hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.1,
      hf.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2.2.2.2.2.2.2.1, hnl12, hf.2.2.2.2.2.2.2.2.2.2.2.1,
      hnl14, ↓reduceIte, List.append_nil, List.singleton_append]; rfl

/-! ### 2. Parameterized `rec_r0..r7` PCs, Code Layouts, and Amortized Cycle Bounds -/

def pcEdge1214 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => 440 | 1 => 3241 | 2 => 1565 | 3 => 4366 | 4 => 2663 | 5 => 1019 | 6 => 3800 | _ => 2120

def pcSkip1214 (r : Fin 8) : Nat :=
  match r.val with
  | 0 => 514 | 1 => 3311 | 2 => 1628 | 3 => 4440 | 4 => 2737 | 5 => 1080 | 6 => 3868 | _ => 2194

def pcSlowStub (r : Fin 8) : Nat :=
  match r.val with
  | 0 => 561 | 1 => 3358 | 2 => 1662 | 3 => 4485 | 4 => 2782 | 5 => 1125 | 6 => 3909 | _ => 2241

def pcSlowGuard (r : Fin 8) : Nat :=
  pcRec r + 11 + (dwordsCode r 3 .x10 0 0 false (r.val == 4)).length + 4

/-- Advance `(r, dstOff, fl)` through one `copy29` step with `flushR7 = true`. -/
def c29Step (st : Fin 8 × Nat × Bool) : Fin 8 × Nat × Bool :=
  (copy29NextR st.1, copy29NextDstOff st.1 st.2.1, copy29NextFlushedR4 st.1 true)

def recL2State (r : Fin 8) : Fin 8 × Nat := (r, 120)
def recL3State (r : Fin 8) : Fin 8 × Nat := (copy30NextR r, copy30NextDstOff r 120)
def recL4State (r : Fin 8) : Fin 8 × Nat :=
  let s := recL3State r; (copy30NextR s.1, copy30NextDstOff s.1 s.2)
def recL5State (r : Fin 8) : Fin 8 × Nat :=
  let s := recL4State r; (copy30NextR s.1, copy30NextDstOff s.1 s.2)

private theorem recL5_finish (r : Fin 8) :
    copy30NextR (recL5State r).1 = r ∧ copy30NextDstOff (recL5State r).1 (recL5State r).2 = 240 := by
  fin_cases r <;> decide

def recL6St (r : Fin 8) : Fin 8 × Nat × Bool := (r, 240, false)
def recL7St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL6St r)
def recL8St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL7St r)
def recL9St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL8St r)
def recL10St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL9St r)
def recL11St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL10St r)
def recL12St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL11St r)
def recL13St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL12St r)
def recL14St (r : Fin 8) : Fin 8 × Nat × Bool := c29Step (recL13St r)

private theorem recL13_step_eq (r : Fin 8) :
    copy29NextR (recL12St r).1 = (recL13St r).1 ∧
    copy29NextDstOff (recL12St r).1 (recL12St r).2.1 = (recL13St r).2.1 ∧
    copy29NextFlushedR4 (recL12St r).1 true = (recL13St r).2.2 := by
  fin_cases r <;> decide

private theorem recL14_step_eq (r : Fin 8) :
    copy29NextR (recL13St r).1 = (recL14St r).1 ∧
    copy29NextDstOff (recL13St r).1 (recL13St r).2.1 = (recL14St r).2.1 ∧
    copy29NextFlushedR4 (recL13St r).1 true = (recL14St r).2.2 := by
  fin_cases r <;> decide

private theorem recL14_st_eq (r : Fin 8) :
    (recL14St r).1 = r ∧ (recL14St r).2.1 = 472 := by
  fin_cases r <;> decide

def recPrefixCode (r : Fin 8) : List Instruction :=
  saltAddrCode ++
  dwordsCode r 3 .x10 0 0 false (r.val == 4) ++
  l0DivuCode ++
  [.base (.BGEU .x22 .x13 (BitVec.ofNat 13 (4 * (pcSlowStub r - pcSlowGuard r))))]

def slowStubCode (r : Fin 8) : List Instruction :=
  (if r.val == 4 then
    [.base (.LD .x12 .x25 (24#12)), .base (.SLLI .x12 .x12 (32#6)), .base (.SRLI .x12 .x12 (32#6))]
   else []) ++
  [.base (.ADDI .x25 .x25 (24#12)),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r.val))),
   .base (.JAL .x0 (jalOff (pcSlowStub r + (if r.val == 4 then 5 else 2)) PC_slow_body))]

def recL0L5Code (r : Fin 8) : List Instruction :=
  l0SibsCode ++
  dwordsCode r 4 .x10 0 24 (r.val == 4) (r.val == 4) ++
  dwordsCode r 4 .x28 0 56 (r.val == 4) (r.val == 4) ++
  lvlAddrRegCode .x10 .x1 ++
  dwordsCode r 4 .x10 0 88 (r.val == 4) (r.val == 4) ++
  lvlAddrRegCode .x10 .x2 ++ copy30Code r .x10 120 (r.val == 4) ++
  lvlAddrRegCode .x10 .x14 ++ copy30Code (recL3State r).1 .x10 (recL3State r).2 false ++
  lvlAddrRegCode .x10 .x21 ++ copy30Code (recL4State r).1 .x10 (recL4State r).2 false ++
  lvlAddrRegCode .x10 .x26 ++ copy30Code (recL5State r).1 .x10 (recL5State r).2 false

def recL6L11Code (r : Fin 8) : List Instruction :=
  lvlAddrRegCode .x10 .x29 ++ copy29Code (recL6St r).1 .x10 (recL6St r).2.1 .x8 0 true (recL6St r).2.2 true ++
  lvlAddrRegCode .x10 .x30 ++ copy29Code (recL7St r).1 .x10 (recL7St r).2.1 .x8 6 false (recL7St r).2.2 true ++
  lvlAddrRegCode .x10 .x31 ++ copy29Code (recL8St r).1 .x10 (recL8St r).2.1 .x8 12 false (recL8St r).2.2 true ++
  lvlAddrRegCode .x10 .x23 ++ copy29Code (recL9St r).1 .x10 (recL9St r).2.1 .x8 18 false (recL9St r).2.2 true ++
  lvlAddrRegCode .x10 .x7 ++ copy29Code (recL10St r).1 .x10 (recL10St r).2.1 .x8 24 false (recL10St r).2.2 true ++
  lvlAddrRegCode .x10 .x3 ++ copy29Code (recL11St r).1 .x10 (recL11St r).2.1 .x8 30 false (recL11St r).2.2 true

def pcEdgeGuard (r : Fin 8) : Nat :=
  pcSlowGuard r + 1 + (recL0L5Code r).length + (recL6L11Code r).length + 2

def recL12GuardCode (r : Fin 8) : List Instruction :=
  [.base (.XORI .x28 .x22 (1#12)),
   .base (.SRLI .x22 .x22 (1#6)),
   .base (.BGEU .x22 .x19 (BitVec.ofNat 13 (4 * (pcEdge1214 r - pcEdgeGuard r))))]

def l12RestAddrCode : List Instruction :=
  [.base (.ADD .x28 .x28 .x22),
   .base (.SLLI .x28 .x28 (5#6)),
   .base (.LD .x10 .x0 (96#12)),
   .base (.ADD .x10 .x10 .x28)]

def recBeqExitCode (pc0 dstOff : Nat) (rEnd : Fin 8) : List Instruction :=
  [.base (.ADDI .x25 .x25 (BitVec.ofNat 12 dstOff)),
   .base (.SB .x22 .x4 (512#12)),
   .base (.ADDI .x24 .x24 (8#12)),
   .base (.BEQ .x24 .x27 (8#13)),
   .base (.JAL .x0 (jalOff (pc0 + 4) (pcRec rEnd))),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rEnd.val))),
   .base (.JAL .x0 (jalOff (pc0 + 6) PC_cap_pass))]

def recBneExitCode (pc0 dstOff : Nat) (rEnd : Fin 8) : List Instruction :=
  [.base (.ADDI .x25 .x25 (BitVec.ofNat 12 dstOff)),
   .base (.SB .x22 .x4 (512#12)),
   .base (.ADDI .x24 .x24 (8#12)),
   .base (.BNE .x24 .x27 (BitVec.ofNat 13 (4 * (pcRec rEnd - (pc0 + 3))))),
   .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rEnd.val))),
   .base (.JAL .x0 (jalOff (pc0 + 5) PC_cap_pass))]

def recFastTailCode (r : Fin 8) : List Instruction :=
  l12RestAddrCode ++ copy29Code (recL12St r).1 .x10 (recL12St r).2.1 .x8 36 false (recL12St r).2.2 true ++
  lvlAddrMemCode .x10 13 ++ copy29Code (recL13St r).1 .x10 (recL13St r).2.1 .x8 42 false (recL13St r).2.2 true ++
  lvlAddrMemCode .x10 14 ++ copy29Code (recL14St r).1 .x10 (recL14St r).2.1 .x8 48 false (recL14St r).2.2 false ++
  tailMergeCode 54

def pcFastExit (r : Fin 8) : Nat := pcEdgeGuard r + 1 + (recFastTailCode r).length

def recFastExitCode (r : Fin 8) : List Instruction :=
  let rNext := copy29NextR r
  let dstEnd := copy29NextDstOff r 472
  if r.val == 3 then recBeqExitCode (pcFastExit r) dstEnd rNext
  else recBneExitCode (pcFastExit r) dstEnd rNext

def recEdgeBodyCode (r : Fin 8) : List Instruction :=
  [.base (.BNE .x22 .x19 (BitVec.ofNat 13 (4 * (pcSkip1214 r - pcEdge1214 r))))] ++
  l12RestAddrCode ++ copy29Code (recL12St r).1 .x10 (recL12St r).2.1 .x8 36 false (recL12St r).2.2 true ++
  lvlAddrMemCode .x10 13 ++ copy29Code (recL13St r).1 .x10 (recL13St r).2.1 .x8 42 false (recL13St r).2.2 false ++
  [.base (.SRLI .x22 .x22 (1#6))] ++
  tailMergeCode 48

def pcS14Exit (r : Fin 8) : Nat := pcEdge1214 r + (recEdgeBodyCode r).length

def recSkipBodyCode (r : Fin 8) : List Instruction :=
  lvlAddrMemCode .x10 13 ++ copy29Code (recL12St r).1 .x10 (recL12St r).2.1 .x8 36 false (recL12St r).2.2 false ++
  [.base (.SRLI .x22 .x22 (1#6))] ++
  tailMergeCode 42

def pcS1214Exit (r : Fin 8) : Nat := pcSkip1214 r + (recSkipBodyCode r).length

private theorem codeAt_app {pc : Nat} {c1 c2 : List Instruction}
    (h1 : CodeAt pc c1) (h2 : CodeAt (pc + c1.length) c2) : CodeAt pc (c1 ++ c2) := by
  refine ⟨by have := h2.1; simp only [List.length_append]; omega, fun j hj => ?_⟩
  simp only [List.length_append] at hj
  by_cases hlt : j < c1.length
  · rw [List.getElem_append_left hlt]; exact h1.2 j hlt
  · rw [List.getElem_append_right (by omega)]
    have h := h2.2 (j - c1.length) (by omega)
    simpa only [show pc + c1.length + (j - c1.length) = pc + j by omega] using h

private theorem codeAt_recL0L5 (r : Fin 8) : CodeAt (pcSlowGuard r + 1) (recL0L5Code r) := by
  unfold recL0L5Code
  fin_cases r <;> (
    repeat apply codeAt_app
    all_goals (
      simp only [List.length_append]
      exact codeAt_of_list_eq _ _ (by decide) rfl))

private theorem codeAt_recL6L11 (r : Fin 8) :
    CodeAt (pcSlowGuard r + 1 + (recL0L5Code r).length) (recL6L11Code r) := by
  unfold recL6L11Code
  fin_cases r <;> (
    repeat apply codeAt_app
    all_goals (
      simp only [recL0L5Code, List.length_append]
      exact codeAt_of_list_eq _ _ (by decide) rfl))

private theorem codeAt_recFastTail (r : Fin 8) :
    CodeAt (pcSlowGuard r + 1 + (recL0L5Code r).length + (recL6L11Code r).length + (recL12GuardCode r).length)
      (recFastTailCode r) := by
  unfold recFastTailCode
  fin_cases r <;> (
    repeat apply codeAt_app
    all_goals (
      simp only [recL0L5Code, recL6L11Code, recL12GuardCode, List.length_append]
      exact codeAt_of_list_eq _ _ (by decide) rfl))

private theorem codeAt_recEdge (r : Fin 8) :
    CodeAt (pcEdge1214 r) (recEdgeBodyCode r ++ recBeqExitCode (pcS14Exit r) 472 r) := by
  unfold recEdgeBodyCode
  fin_cases r <;> (
    repeat apply codeAt_app
    all_goals (
      simp only [pcS14Exit, recEdgeBodyCode, List.length_append]
      exact codeAt_of_list_eq _ _ (by decide) rfl))

private theorem codeAt_recSkip (r : Fin 8) :
    CodeAt (pcSkip1214 r)
      (recSkipBodyCode r ++ recBeqExitCode (pcS1214Exit r) (copy29NextDstOff (recL12St r).1 (recL12St r).2.1) (copy29NextR (recL12St r).1)) := by
  unfold recSkipBodyCode
  fin_cases r <;> (
    repeat apply codeAt_app
    all_goals (
      simp only [pcS1214Exit, recSkipBodyCode, List.length_append]
      exact codeAt_of_list_eq _ _ (by decide) rfl))

private theorem codeAt_rec_all (r : Fin 8) :
    CodeAt (pcRec r) (recPrefixCode r) ∧
    CodeAt (pcSlowStub r) (slowStubCode r) ∧
    CodeAt (pcSlowGuard r + 1) (recL0L5Code r ++ recL6L11Code r ++ recL12GuardCode r ++ recFastTailCode r ++ recFastExitCode r) ∧
    CodeAt (pcEdge1214 r) (recEdgeBodyCode r ++ recBeqExitCode (pcS14Exit r) 472 r) ∧
    CodeAt (pcSkip1214 r) (recSkipBodyCode r ++ recBeqExitCode (pcS1214Exit r) (copy29NextDstOff (recL12St r).1 (recL12St r).2.1) (copy29NextR (recL12St r).1)) := by
  have h1 : CodeAt (pcRec r) (recPrefixCode r) := by fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl
  have h2 : CodeAt (pcSlowStub r) (slowStubCode r) := by fin_cases r <;> exact codeAt_of_list_eq _ _ (by decide) rfl
  have h3a := codeAt_recL0L5 r
  have h3b := codeAt_recL6L11 r
  have h3c : CodeAt (pcSlowGuard r + 1 + (recL0L5Code r).length + (recL6L11Code r).length) (recL12GuardCode r) := by
    fin_cases r <;> (
      simp only [recL12GuardCode, pcEdgeGuard, recL0L5Code, recL6L11Code, List.length_append]
      exact codeAt_of_list_eq _ _ (by decide) rfl)
  have h3d := codeAt_recFastTail r
  have h3e : CodeAt (pcSlowGuard r + 1 + (recL0L5Code r).length + (recL6L11Code r).length + (recL12GuardCode r).length + (recFastTailCode r).length) (recFastExitCode r) := by
    fin_cases r <;> (
      simp only [recFastExitCode, pcFastExit, pcEdgeGuard, recL0L5Code, recL6L11Code, recL12GuardCode, recFastTailCode, List.length_append]
      exact codeAt_of_list_eq _ _ (by decide) rfl)
  have h3 : CodeAt (pcSlowGuard r + 1) (recL0L5Code r ++ recL6L11Code r ++ recL12GuardCode r ++ recFastTailCode r ++ recFastExitCode r) := by
    have h12 := codeAt_app h3a h3b
    have h123 := codeAt_app h12 (by simpa only [List.length_append, Nat.add_assoc] using h3c)
    have h1234 := codeAt_app h123 (by simpa only [List.length_append, Nat.add_assoc] using h3d)
    exact codeAt_app h1234 (by simpa only [List.length_append, Nat.add_assoc] using h3e)
  exact ⟨h1, h2, h3, codeAt_recEdge r, codeAt_recSkip r⟩

/-- Amortized cycle bounds for all 3 fast/edge branches across all `r : Fin 8` and `last : Bool`. -/
def fastPathMaxNf (r : Fin 8) (last : Bool) : Nat :=
  11 + (dwordsCode r 3 .x10 0 0 false (r.val == 4)).length + 7 + 1 +
  ((recL0L5Code r).length - 2) + (recL6L11Code r).length + 3 +
  ((recFastTailCode r).length - 4) + (if last then 6 else if r.val == 3 then 5 else 4)

def s14PathMaxNf (r : Fin 8) (last : Bool) : Nat :=
  11 + (dwordsCode r 3 .x10 0 0 false (r.val == 4)).length + 7 + 1 +
  ((recL0L5Code r).length - 2) + (recL6L11Code r).length + 3 +
  ((recEdgeBodyCode r).length - 4) + (if last then 6 else 5)

def s1214PathMaxNf (r : Fin 8) (last : Bool) : Nat :=
  11 + (dwordsCode r 3 .x10 0 0 false (r.val == 4)).length + 7 + 1 +
  ((recL0L5Code r).length - 2) + (recL6L11Code r).length + 3 + 1 +
  ((recSkipBodyCode r).length - 4) + (if last then 6 else 5)

private theorem rec_amort_all (r : Fin 8) (last : Bool) :
    8 * fastPathMaxNf r last + phi8 (copy29NextR r) ≤ 3453 + phi8 r + (if last then 16 else 0) ∧
    8 * s14PathMaxNf r last + phi8 r ≤ 3453 + phi8 r + (if last then 16 else 0) ∧
    8 * s1214PathMaxNf r last + phi8 (copy29NextR (recL12St r).1) ≤ 3453 + phi8 r + (if last then 16 else 0) := by
  fin_cases r <;> cases last <;>
    simp only [fastPathMaxNf, s14PathMaxNf, s1214PathMaxNf, recL0L5Code, recL6L11Code,
      recFastTailCode, recEdgeBodyCode, recSkipBodyCode, List.length_append] <;> decide

private theorem recRegs_of_eq {positions : Positions} {ordinal : Nat} {s s' : MachineState}
    (hregs : RecRegs positions ordinal s)
    (heq : RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x15, .x16, .x17, .x22, .x28] s s') :
    RecRegs positions ordinal s' :=
  ⟨(heq .x1 (by decide)).trans hregs.rx1, (heq .x2 (by decide)).trans hregs.rx2,
   (heq .x3 (by decide)).trans hregs.rx3, (heq .x4 (by decide)).trans hregs.rx4,
   (heq .x7 (by decide)).trans hregs.rx7, (heq .x9 (by decide)).trans hregs.rx9,
   (heq .x11 (by decide)).trans hregs.rx11, (heq .x13 (by decide)).trans hregs.rx13,
   (heq .x14 (by decide)).trans hregs.rx14, (heq .x18 (by decide)).trans hregs.rx18,
   (heq .x19 (by decide)).trans hregs.rx19, (heq .x20 (by decide)).trans hregs.rx20,
   (heq .x21 (by decide)).trans hregs.rx21, (heq .x23 (by decide)).trans hregs.rx23,
   (heq .x24 (by decide)).trans hregs.rx24, (heq .x26 (by decide)).trans hregs.rx26,
   (heq .x27 (by decide)).trans hregs.rx27, (heq .x29 (by decide)).trans hregs.rx29,
   (heq .x30 (by decide)).trans hregs.rx30, (heq .x31 (by decide)).trans hregs.rx31⟩

/-! ### 3. Modular Execution Lemmas for `slow_stub`, `l12RestAddr`, `exit`, and `L0..L11` -/

/-- Execute `slow_stub_r{r0}` (`3` cyc for `r0 ≠ 4`, `6` cyc for `r0 = 4`), reloading `x12` when `r0 = 4`. -/
private theorem openRuns_slow_stub {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {tblInit : Bool} {s : MachineState}
    (hord : ordinal < positions.card) (hbd_w : base + 40 ≤ 8556390424)
    (hpc : s.pc = pcAt (pcSlowStub r0))
    (hregs : RecRegs positions ordinal s)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (3 * (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)))
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val % 3))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hbt : BaseTableReady s)
    (hcm : CapMarks15State s positions ordinal)
    (htbl : SlowTablesState s tblInit)
    (hw : WriterState (CleanTrapdoor trapdoor) s r0 (r0.val == 4) base 24
            (written ++ bitsToBytes (tdSalt trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord]))) 24))
    (ht : TailState (CleanTrapdoor trapdoor) s tails flushes) :
    ∃ s' : MachineState,
      OpenRuns s (if r0.val == 4 then 6 else 3) (if r0.val == 4 then 6 else 3) s' ∧
      SlowEntryInv trapdoor positions ordinal r0 base written tails flushes tblInit
        ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  have hcode := (codeAt_rec_all r0).2.1
  have hbase8 := hw.hbase8
  -- Reload x12 when r0 = 4 (3 cyc), no-op otherwise (0 cyc)
  have hpre : ∃ (k : Nat) (sa : MachineState),
      k = (if r0.val == 4 then 3 else 0) ∧
      OpenRuns s k k sa ∧
      sa.pc = pcAt (pcSlowStub r0 + k) ∧
      RegsEqExcept [.x12] s sa ∧
      (∀ a, sa.getMem a = s.getMem a) ∧
      WriterState (CleanTrapdoor trapdoor) sa r0 false base 24 (written ++ bitsToBytes (tdSalt trapdoor i) 24) := by
    by_cases hr4 : r0.val = 4
    · have hbeq : (r0.val == 4) = true := by simp [hr4]
      have hstub4 : pcSlowStub r0 = 2782 := by rcases r0 with ⟨rv, hrv⟩; dsimp at hr4; subst hr4; rfl
      have hpc' : s.pc = pcAt 2782 := by rw [hpc, hstub4]
      have haddr24 : s.getReg .x25 + signExtend12 (24#12) = BitVec.ofNat 64 (11341403200 + base + 24) := by
        rw [hw.rx25, signExtend12_nonneg 24 (by omega), ← BitVec.ofNat_add]
      have hval24 : accessValid (s.getReg .x25 + signExtend12 (24#12)) 8 = true := by
        rw [haddr24]; exact accessValid_ofNat _ 8 (by omega) (by omega)
      have h0 := step_LD (s := s) (by decide) hpc' (rfl : openInstr 2782 = .base (.LD .x12 .x25 (24#12))) hval24
      set s1 := (s.setReg .x12 (s.getMem (s.getReg .x25 + signExtend12 (24#12)))).setPC (pcAt 2783)
      have h1 := step_SLLI (s := s1) (by decide) rfl (rfl : openInstr 2783 = .base (.SLLI .x12 .x12 (32#6)))
      set s2 := (s1.setReg .x12 (s1.getReg .x12 <<< (32#6).toNat)).setPC (pcAt 2784)
      have h2 := step_SRLI (s := s2) (by decide) rfl (rfl : openInstr 2784 = .base (.SRLI .x12 .x12 (32#6)))
      set s3 := (s2.setReg .x12 (s2.getReg .x12 >>> (32#6).toNat)).setPC (pcAt 2785)
      refine ⟨3, s3, by simp [hbeq], (h0.trans h1).trans h2, by rw [hstub4]; rfl,
        fun reg hreg => by have h12' : reg ≠ .x12 := fun h => hreg (by simp [h]); simp [s3, s2, s1, getReg_setReg_ne' .x12 reg h12'.symm],
        fun _ => by simp [s3, s2, s1], ?_⟩
      refine ⟨hbase8, hw.hdst8, hw.hlen, hw.hbound, by simp [s3, s2, s1, getReg_setReg_ne', hw.rx25],
        by simp, fun hcl j hj => by simp only [s3, s2, s1, getByte_setPC, getByte_setReg]; exact hw.hbytes hcl j hj, fun hcl => ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte, show ¬ (r0.val = 0) by omega]
      have hrem := hw.hrem hcl; simp only [hbeq, ↓reduceIte] at hrem
      have hs3_x12 : s3.getReg .x12 = (s.getMem (BitVec.ofNat 64 (11341403200 + base + 24)) <<< (8 * 4)) >>> (8 * 4) := by
        simp [s3, s2, s1, haddr24]
      refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
      · rw [hs3_x12, word_shl_ushr_byte _ 4 4 (by omega) (by omega) j (by omega)]
        simp only [show j + 4 < 8 by omega, show 4 ≤ j + 4 by omega, and_self, ↓reduceIte]
        have hb := getMem_extractByte (s := s) (addr := 11341403200 + base + 24) (j := j) (by omega) (by omega)
        rw [show j + 4 - 4 = j by omega, hb]
        exact hrem j hj
      · rw [hs3_x12, word_shl_ushr_byte _ 4 4 (by omega) (by omega) j hj2]
        simp only [show ¬ (j + 4 < 8 ∧ 4 ≤ j + 4) by omega, ↓reduceIte]
    · have hbeq : (r0.val == 4) = false := beq_false_of_ne hr4
      rw [hbeq] at hw
      exact ⟨0, s, by simp [hbeq], OpenRuns.refl s, by simpa using hpc, fun _ _ => rfl, fun _ => rfl, hw⟩
  obtain ⟨k, sa, hk, hra, hpca, hrega, hmema, hwa⟩ := hpre
  set pc1 := pcSlowStub r0 + k
  have htail_code : CodeAt pc1 [.base (.ADDI .x25 .x25 (24#12)),
      .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r0.val))),
      .base (.JAL .x0 (jalOff (pc1 + 2) PC_slow_body))] := by
    have hsplit := hcode.right
    cases hr4 : (r0.val == 4) <;> simp only [hr4, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, List.length_nil] at hsplit hk ⊢ <;>
      simpa only [pc1, hk, Nat.add_assoc] using hsplit
  have hbd1 : pc1 + 3 ≤ OPEN_CODE_LEN := by have := htail_code.1; simpa using this
  have hi0 : openInstr pc1 = .base (.ADDI .x25 .x25 (24#12)) := by have h := htail_code.2 0 (by simp); simpa using h
  have hi1 : openInstr (pc1 + 1) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * r0.val))) := by have h := htail_code.2 1 (by simp); simpa using h
  have hi2 : openInstr (pc1 + 2) = .base (.JAL .x0 (jalOff (pc1 + 2) PC_slow_body)) := by have h := htail_code.2 2 (by simp); simpa using h
  have hs1 := step_ADDI (s := sa) (by omega) hpca hi0
  set sb := (sa.setReg .x25 (sa.getReg .x25 + signExtend12 (24#12))).setPC (pcAt (pc1 + 1))
  have hs2 := step_ADDI (s := sb) (by omega) rfl hi1
  set sc := (sb.setReg .x14 (sb.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * r0.val)))).setPC (pcAt (pc1 + 1 + 1))
  have hjtgt := pcAt_add_jalOff (pc1 + 2) PC_slow_body (by omega) (by decide)
  have hs3 := step_JAL (s := sc) (by omega) (by congr 1) hi2 hjtgt
  set sd := (sc.setReg .x0 (pcAt (pc1 + 2 + 1))).setPC (pcAt PC_slow_body)
  have hmemd : ∀ a, sd.getMem a = s.getMem a := fun a => by simp [sd, sc, sb, hmema]
  have hregd : ∀ reg, reg ≠ .x12 → reg ≠ .x14 → reg ≠ .x25 → sd.getReg reg = s.getReg reg := fun reg h12 h14 h25 => by
    have h0 : sd.getReg reg = sc.getReg reg := by cases reg <;> simp [sd, setReg_x0_eq]
    exact h0.trans ((by simp [sc, sb, getReg_setReg_ne' .x14 reg h14.symm, getReg_setReg_ne' .x25 reg h25.symm] : sc.getReg reg = sa.getReg reg).trans
      (hrega reg (by simp [h12])))
  have hsb_25 : sb.getReg .x25 = BitVec.ofNat 64 (11341403200 + (base + 24)) := by
    simp [sb, hwa.rx25, signExtend12_nonneg 24 (by omega), ← BitVec.ofNat_add, Nat.add_assoc]
  have hsd_25 : sd.getReg .x25 = BitVec.ofNat 64 (11341403200 + (base + 24)) := by
    simp [sd, sc, getReg_setReg_ne', hsb_25]
  have hsd_14 : sd.getReg .x14 = BitVec.ofNat 64 (8 * r0.val) := by
    have := r0.isLt
    have e : sd.getReg .x14 = sb.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * r0.val)) := by
      simp [sd, sc, setReg_x0_eq]
    rw [e, show sb.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * r0.val) (by omega), BitVec.zero_add]
  have hwd : WriterState (CleanTrapdoor trapdoor) sd r0 false (base + 24) 0 (written ++ bitsToBytes (tdSalt trapdoor i) 24) := by
    have hw_sb : WriterState (CleanTrapdoor trapdoor) sb r0 false (base + 24) 0 (written ++ bitsToBytes (tdSalt trapdoor i) 24) :=
      writerState_advance_base hwa (by omega) (pcAt (pc1 + 1))
    exact writerState_of_mem_eq hw_sb (fun _ => by simp [sd, sc]) (by simp [sd, sc, setReg_x0_eq, getReg_setReg_ne']) (by simp [sd, sc, setReg_x0_eq, getReg_setReg_ne'])
  refine ⟨sd, ?_, rfl,
    (hregd .x1 (by decide) (by decide) (by decide)).trans hregs.rx1,
    (hregd .x2 (by decide) (by decide) (by decide)).trans hregs.rx2,
    (hregd .x3 (by decide) (by decide) (by decide)).trans hregs.rx3,
    (hregd .x4 (by decide) (by decide) (by decide)).trans hregs.rx4,
    (hregd .x6 (by decide) (by decide) (by decide)).trans hx6,
    (hregd .x7 (by decide) (by decide) (by decide)).trans hregs.rx7,
    (hregd .x8 (by decide) (by decide) (by decide)).trans hx8,
    (hregd .x9 (by decide) (by decide) (by decide)).trans hregs.rx9,
    (hregd .x11 (by decide) (by decide) (by decide)).trans hregs.rx11,
    (hregd .x13 (by decide) (by decide) (by decide)).trans hregs.rx13,
    hsd_14,
    (hregd .x18 (by decide) (by decide) (by decide)).trans hregs.rx18,
    (hregd .x19 (by decide) (by decide) (by decide)).trans hregs.rx19,
    (hregd .x20 (by decide) (by decide) (by decide)).trans hregs.rx20,
    (hregd .x21 (by decide) (by decide) (by decide)).trans hregs.rx21,
    (hregd .x22 (by decide) (by decide) (by decide)).trans hx22,
    (hregd .x23 (by decide) (by decide) (by decide)).trans hregs.rx23,
    (hregd .x24 (by decide) (by decide) (by decide)).trans hregs.rx24,
    (hregd .x26 (by decide) (by decide) (by decide)).trans hregs.rx26,
    (hregd .x27 (by decide) (by decide) (by decide)).trans hregs.rx27,
    (hregd .x29 (by decide) (by decide) (by decide)).trans hregs.rx29,
    (hregd .x30 (by decide) (by decide) (by decide)).trans hregs.rx30,
    (hregd .x31 (by decide) (by decide) (by decide)).trans hregs.rx31,
    fun a ha => (hmemd a).trans (hro a ha),
    baseTableReady_of_lowEq hbt (fun a _ => hmemd a),
    capMarks15State_of_lowEq hcm (fun a _ _ => hmemd a),
    slowTablesState_of_eq htbl (fun a _ _ => hmemd a),
    hwd,
    TailState.of_proofWrite ht (fun a _ => hmemd a)
      (hregd .x15 (by decide) (by decide) (by decide))
      (hregd .x16 (by decide) (by decide) (by decide))
      (hregd .x17 (by decide) (by decide) (by decide))⟩
  have hcyc : k + 1 + 1 + 1 = if r0.val == 4 then 6 else 3 := by rw [hk]; cases (r0.val == 4) <;> rfl
  simpa only [hcyc] using ((hra.trans hs1).trans hs2).trans hs3

/-- Shared fast/edge record exit (`ADDI x25 dstOff; SB x22 x4 512; ADDI x24 x24 8` + `BNE` or `BEQ+JAL`). -/
private theorem openRuns_rec_exit {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base dstOff flushes pc0 : Nat} {rEnd : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {tblInit useBne : Bool} {s : MachineState}
    (hord : ordinal < positions.card) (hdst_off : dstOff < 2048) (hdst8 : dstOff % 8 = 0)
    (hcode : CodeAt pc0 (if useBne then recBneExitCode pc0 dstOff rEnd else recBeqExitCode pc0 dstOff rEnd))
    (hbne_ok : useBne = true → pc0 + 3 ≤ pcRec rEnd ∧ 4 * (pcRec rEnd - (pc0 + 3)) < 4096)
    (hpc : s.pc = pcAt pc0)
    (hregs : RecRegs positions ordinal s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (capLeafOf ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord]))))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hbt : BaseTableReady s)
    (hcm : CapMarks15State s positions ordinal)
    (htbl : SlowTablesState s tblInit)
    (hw : WriterState (CleanTrapdoor trapdoor) s rEnd false base dstOff written)
    (ht : TailState (CleanTrapdoor trapdoor) s tails flushes) :
    let cyc := if ordinal + 1 = positions.card then 6 else if useBne then 4 else 5
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd (base + dstOff) written tails flushes s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd (base + dstOff) written tails flushes tblInit s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  have hcard := positions_card_le' positions
  have hcl_lt : capLeafOf i < 342 := by
    unfold capLeafOf; have hi : i.val < 16777216 := i.isLt; simp only [Nat.shiftRight_eq_div_pow]; omega
  have hbd : pc0 + (if useBne then 6 else 7) ≤ OPEN_CODE_LEN := by
    have := hcode.1; cases useBne <;> simpa [recBneExitCode, recBeqExitCode] using this
  have hbd6 : pc0 + 6 ≤ OPEN_CODE_LEN := by
    cases useBne <;> simp only [Bool.false_eq_true, ↓reduceIte] at hbd <;> omega
  have hbd7 : useBne = false → pc0 + 7 ≤ OPEN_CODE_LEN := by
    intro h; simp only [h, Bool.false_eq_true, ↓reduceIte] at hbd; omega
  have hi0 : openInstr pc0 = .base (.ADDI .x25 .x25 (BitVec.ofNat 12 dstOff)) := by
    have h := hcode.2 0 (by cases useBne <;> simp [recBneExitCode, recBeqExitCode])
    cases useBne <;> simpa [recBneExitCode, recBeqExitCode] using h
  have hi1 : openInstr (pc0 + 1) = .base (.SB .x22 .x4 (512#12)) := by
    have h := hcode.2 1 (by cases useBne <;> simp [recBneExitCode, recBeqExitCode])
    cases useBne <;> simpa [recBneExitCode, recBeqExitCode] using h
  have hi2 : openInstr (pc0 + 2) = .base (.ADDI .x24 .x24 (8#12)) := by
    have h := hcode.2 2 (by cases useBne <;> simp [recBneExitCode, recBeqExitCode])
    cases useBne <;> simpa [recBneExitCode, recBeqExitCode] using h
  have h0 := step_ADDI (s := s) (by omega) hpc hi0
  set s1 := (s.setReg .x25 (s.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff))).setPC (pcAt (pc0 + 1))
  have hs1_25 : s1.getReg .x25 = BitVec.ofNat 64 (11341403200 + (base + dstOff)) := by
    simp [s1, hw.rx25, signExtend12_nonneg dstOff hdst_off, ← BitVec.ofNat_add, Nat.add_assoc]
  have hs1_22 : s1.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) := by simp [s1, getReg_setReg_ne', hx22]
  have hs1_4 : s1.getReg .x4 = 1#64 := by simp [s1, getReg_setReg_ne', hregs.rx4]
  have hsb_addr : s1.getReg .x22 + signExtend12 (512#12) = BitVec.ofNat 64 (512 + capLeafOf i) := by
    rw [hs1_22, signExtend12_nonneg 512 (by omega), ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega
  have hsb_val : accessValid (s1.getReg .x22 + signExtend12 (512#12)) 1 = true := by
    rw [hsb_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
  have h1 := step_SB (s := s1) (by omega) rfl hi1 hsb_val
  set s2 := (s1.setByte (s1.getReg .x22 + signExtend12 (512#12)) ((s1.getReg .x4).truncate 8)).setPC (pcAt (pc0 + 1 + 1))
  have h2 := step_ADDI (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x24 (s2.getReg .x24 + signExtend12 (8#12))).setPC (pcAt (pc0 + 2 + 1))
  have hs3_24 : s3.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * (ordinal + 1)) := by
    simp only [s3, s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      getReg_setByte, getReg_setReg_ne', hregs.rx24, signExtend12_nonneg 8 (by omega), ← BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64); omega
  have hs3_27 : s3.getReg .x27 = BitVec.ofNat 64 (6912218176 + 8 * positions.card) := by
    simp [s3, s2, s1, getReg_setReg_ne', hregs.rx27]
  have hmem3 : ∀ a : Word, ¬ (512 ≤ a.toNat ∧ a.toNat < 1344) → s3.getMem a = s.getMem a := by
    intro a ha
    simp only [s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsb_addr, hs1_4,
      show (1#64 : Word).truncate 8 = 1#8 from rfl]
    exact setByte_cap_pres hcl_lt a ha
  have hro3 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s3 :=
    fun a ha => (hmem3 a (by omega)).trans (hro a ha)
  have hbt3 : BaseTableReady s3 := baseTableReady_of_lowEq hbt (fun a ha => hmem3 a (by omega))
  have htbl3 : SlowTablesState s3 tblInit := slowTablesState_of_eq htbl (fun a _ _ => hmem3 a (by omega))
  have hcm3 : CapMarks15State s3 positions (ordinal + 1) := by
    have hc := capMarks15_set_mark hord hcm
    refine ⟨fun c hcl => ?_, fun q hq1 hq2 => ?_⟩
    · simp only [s3, s2, s1, getByte_setPC, getByte_setReg, hsb_addr, hs1_4, show (1#64 : Word).truncate 8 = 1#8 from rfl]
      exact hc.l15 c hcl
    · simp only [s3, s2, s1, getByte_setPC, getByte_setReg, hsb_addr, hs1_4, show (1#64 : Word).truncate 8 = 1#8 from rfl]
      exact hc.hiZero q hq1 hq2
  have hw3 : WriterState (CleanTrapdoor trapdoor) s3 rEnd false (base + dstOff) 0 written := by
    have hw1 := writerState_advance_base hw hdst_off (pcAt (pc0 + 1))
    have hbyte : ∀ q < 8556390424, s3.getByte (BitVec.ofNat 64 (11341403200 + q)) = s1.getByte (BitVec.ofNat 64 (11341403200 + q)) := by
      intro q hq; simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
      have hal := alignToDword_ofNat_eq (8 * ((11341403200 + q) / 8)) ((11341403200 + q) % 8) (by omega) (by omega)
      rw [show 8 * ((11341403200 + q) / 8) + (11341403200 + q) % 8 = 11341403200 + q by omega] at hal
      have hs1_m : s1.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + q))) = s.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + q))) := by simp [s1]
      rw [hs1_m]; apply hmem3; rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    refine ⟨hw1.hbase8, hw1.hdst8, hw1.hlen, hw1.hbound, by simp [s3, s2, getReg_setReg_ne', hs1_25], by simp,
      fun hcl j hj => by have h1 := hw1.hlen; have h2 := hw1.hbound; rw [hbyte j (by omega)]; exact hw1.hbytes hcl j hj, fun hcl => ?_⟩
    have hrem := hw1.hrem hcl; simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
    by_cases hr0 : rEnd.val = 0
    · simp only [hr0, ↓reduceIte]
    · simp only [hr0, ↓reduceIte] at hrem ⊢
      have h12 : s3.getReg .x12 = s1.getReg .x12 := by simp [s3, s2, getReg_setReg_ne']
      rw [h12]; exact hrem
  have ht3 : TailState (CleanTrapdoor trapdoor) s3 tails flushes := by
    refine ⟨ht.hbits, ht.hbound, by simp [s3, s2, s1, getReg_setReg_ne', ht.rx15], by simp [s3, s2, s1, getReg_setReg_ne', ht.rx17], fun hcl => ?_⟩
    obtain ⟨tBuf, hlt, hx16', hsum⟩ := ht.hdata hcl
    refine ⟨tBuf, hlt, by simp [s3, s2, s1, getReg_setReg_ne', hx16'], ?_⟩
    have hmap : ((List.range (8 * flushes)).map fun j => s3.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
        ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) := by
      apply List.map_congr_left; intro j hj; have hjlt := List.mem_range.mp hj
      have htbb : tailBufBase = 20000000000 := rfl; have hbd' := ht.hbound
      simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
      have hal := alignToDword_ofNat_eq (8 * ((tailBufBase + j) / 8)) ((tailBufBase + j) % 8) (by omega) (by omega)
      rw [show 8 * ((tailBufBase + j) / 8) + (tailBufBase + j) % 8 = tailBufBase + j by omega] at hal
      apply hmem3; rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hmap]; exact hsum
  have hregs3 : RecRegs positions (ordinal + 1) s3 :=
    ⟨by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx1], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx2],
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx3], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx4],
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx7], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx9],
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx11], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx13],
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx14], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx18],
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx19], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx20],
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx21], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx23],
     hs3_24, by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx26], hs3_27,
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx29], by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx30],
     by simp [s3, s2, s1, getReg_setReg_ne', hregs.rx31]⟩
  cases useBne with
  | true =>
    have hbne_hi := hbne_ok rfl
    have hi3 : openInstr (pc0 + 3) = .base (.BNE .x24 .x27 (BitVec.ofNat 13 (4 * (pcRec rEnd - (pc0 + 3))))) := by
      have h := hcode.2 3 (by simp [recBneExitCode]); simpa [recBneExitCode] using h
    have hi4 : openInstr (pc0 + 4) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rEnd.val))) := by
      have h := hcode.2 4 (by simp [recBneExitCode]); simpa [recBneExitCode] using h
    have hi5 : openInstr (pc0 + 5) = .base (.JAL .x0 (jalOff (pc0 + 5) PC_cap_pass)) := by
      have h := hcode.2 5 (by simp [recBneExitCode]); simpa [recBneExitCode] using h
    by_cases hlast : ordinal + 1 = positions.card
    · have h3 := step_BNE_not_taken (s := s3) (by omega) (by congr 1) hi3 (by rw [hs3_24, hs3_27, hlast])
      set s4 := s3.setPC (pcAt (pc0 + 3 + 1))
      have h4 := step_ADDI (s := s4) (by omega) (by congr 1) hi4
      set s5 := (s4.setReg .x14 (s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * rEnd.val)))).setPC (pcAt (pc0 + 4 + 1))
      have h5 := step_JAL (s := s5) (by omega) (by congr 1) hi5 (pcAt_add_jalOff (pc0 + 5) PC_cap_pass (by omega) (by decide))
      set s6 := (s5.setReg .x0 (pcAt (pc0 + 5 + 1))).setPC (pcAt PC_cap_pass)
      simp only [hlast, ↓reduceIte, ↓reduceDIte]
      have hrEnd_lt := rEnd.isLt
      refine ⟨s6, ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5, rfl,
        by simp [s6, s5, s4, getReg_setReg_ne', hregs3.rx4],
        by simp [s6, s5, s4, getReg_setReg_ne', hregs3.rx11],
        by
          have e : s6.getReg .x14 = s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * rEnd.val)) := by simp [s6, s5, setReg_x0_eq]
          rw [e, show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * rEnd.val) (by omega), BitVec.zero_add],
        fun a ha => (by simp [s6, s5, s4] : s6.getMem a = s3.getMem a).trans (hro3 a ha),
        baseTableReady_of_lowEq hbt3 (fun a _ => by simp [s6, s5, s4]),
        by rw [← hlast]; exact capMarks15State_of_lowEq hcm3 (fun a _ _ => by simp [s6, s5, s4]),
        writerState_of_mem_eq hw3 (fun _ => by simp [s6, s5, s4]) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']),
        TailState.of_proofWrite ht3 (fun _ _ => by simp [s6, s5, s4]) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne'])⟩
    · have hne : s3.getReg .x24 ≠ s3.getReg .x27 := by
        rw [hs3_24, hs3_27]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 6912218176 + 8 * (ordinal + 1) < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 6912218176 + 8 * positions.card < 2 ^ 64)] at hn; omega
      have h3 := step_BNE_taken (s := s3) (by omega) (by congr 1) hi3 hne (pcAt_add_pos13 (pc0 + 3) (pcRec rEnd) hbne_hi.1 hbne_hi.2)
      set s4 := s3.setPC (pcAt (pcRec rEnd))
      simp only [hlast, ↓reduceIte, ↓reduceDIte]
      refine ⟨s4, ((h0.trans h1).trans h2).trans h3, rfl,
        recRegs_of_eq hregs3 (fun _ _ => by simp [s4]),
        fun a ha => (by simp [s4] : s4.getMem a = s3.getMem a).trans (hro3 a ha),
        baseTableReady_of_lowEq hbt3 (fun a _ => by simp [s4]),
        capMarks15State_of_lowEq hcm3 (fun a _ _ => by simp [s4]),
        slowTablesState_of_eq htbl3 (fun a _ _ => by simp [s4]),
        writerState_of_mem_eq hw3 (fun _ => by simp [s4]) (by simp [s4]) (by simp [s4]),
        TailState.of_proofWrite ht3 (fun _ _ => by simp [s4]) (by simp [s4]) (by simp [s4]) (by simp [s4])⟩
  | false =>
    have hbd7' := hbd7 rfl
    have hi3 : openInstr (pc0 + 3) = .base (.BEQ .x24 .x27 (8#13)) := by
      have h := hcode.2 3 (by simp [recBeqExitCode]); simpa [recBeqExitCode] using h
    have hi4 : openInstr (pc0 + 4) = .base (.JAL .x0 (jalOff (pc0 + 4) (pcRec rEnd))) := by
      have h := hcode.2 4 (by simp [recBeqExitCode]); simpa [recBeqExitCode] using h
    have hi5 : openInstr (pc0 + 5) = .base (.ADDI .x14 .x0 (BitVec.ofNat 12 (8 * rEnd.val))) := by
      have h := hcode.2 5 (by simp [recBeqExitCode]); simpa [recBeqExitCode] using h
    have hi6 : openInstr (pc0 + 6) = .base (.JAL .x0 (jalOff (pc0 + 6) PC_cap_pass)) := by
      have h := hcode.2 6 (by simp [recBeqExitCode]); simpa [recBeqExitCode] using h
    by_cases hlast : ordinal + 1 = positions.card
    · have hbr3 : pcAt (pc0 + 3) + signExtend13 (8#13) = pcAt (pc0 + 5) := by
        simpa only [show 4 * (pc0 + 5 - (pc0 + 3)) = 8 by omega] using pcAt_add_pos13 (pc0 + 3) (pc0 + 5) (by omega) (by omega)
      have h3 := step_BEQ_taken (s := s3) (by omega) (by congr 1) hi3 (by rw [hs3_24, hs3_27, hlast]) hbr3
      set s4 := s3.setPC (pcAt (pc0 + 5))
      have h4 := step_ADDI (s := s4) (by omega) rfl hi5
      set s5 := (s4.setReg .x14 (s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * rEnd.val)))).setPC (pcAt (pc0 + 5 + 1))
      have h5 := step_JAL (s := s5) (by omega) (by congr 1) hi6 (pcAt_add_jalOff (pc0 + 6) PC_cap_pass (by omega) (by decide))
      set s6 := (s5.setReg .x0 (pcAt (pc0 + 6 + 1))).setPC (pcAt PC_cap_pass)
      simp only [hlast, ↓reduceIte, ↓reduceDIte]
      have hrEnd_lt := rEnd.isLt
      refine ⟨s6, ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5, rfl,
        by simp [s6, s5, s4, getReg_setReg_ne', hregs3.rx4],
        by simp [s6, s5, s4, getReg_setReg_ne', hregs3.rx11],
        by
          have e : s6.getReg .x14 = s4.getReg .x0 + signExtend12 (BitVec.ofNat 12 (8 * rEnd.val)) := by simp [s6, s5, setReg_x0_eq]
          rw [e, show s4.getReg .x0 = 0#64 from rfl, signExtend12_nonneg (8 * rEnd.val) (by omega), BitVec.zero_add],
        fun a ha => (by simp [s6, s5, s4] : s6.getMem a = s3.getMem a).trans (hro3 a ha),
        baseTableReady_of_lowEq hbt3 (fun a _ => by simp [s6, s5, s4]),
        by rw [← hlast]; exact capMarks15State_of_lowEq hcm3 (fun a _ _ => by simp [s6, s5, s4]),
        writerState_of_mem_eq hw3 (fun _ => by simp [s6, s5, s4]) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']),
        TailState.of_proofWrite ht3 (fun _ _ => by simp [s6, s5, s4]) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne']) (by simp [s6, s5, s4, setReg_x0_eq, getReg_setReg_ne'])⟩
    · have hne : s3.getReg .x24 ≠ s3.getReg .x27 := by
        rw [hs3_24, hs3_27]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 6912218176 + 8 * (ordinal + 1) < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : 6912218176 + 8 * positions.card < 2 ^ 64)] at hn; omega
      have h3 := step_BEQ_not_taken (s := s3) (by omega) (by congr 1) hi3 hne
      set s4 := s3.setPC (pcAt (pc0 + 3 + 1))
      have hrc_le : pcRec rEnd ≤ OPEN_CODE_LEN := by fin_cases rEnd <;> decide
      have h4 := step_JAL (s := s4) (by omega) (by congr 1) hi4 (pcAt_add_jalOff (pc0 + 4) (pcRec rEnd) (by omega) hrc_le)
      set s5 := (s4.setReg .x0 (pcAt (pc0 + 4 + 1))).setPC (pcAt (pcRec rEnd))
      simp only [hlast, ↓reduceIte, ↓reduceDIte, Bool.false_eq_true]
      refine ⟨s5, (((h0.trans h1).trans h2).trans h3).trans h4, rfl,
        by
          have heq : ∀ reg, s5.getReg reg = s3.getReg reg := fun reg => by cases reg <;> simp [s5, s4, setReg_x0_eq]
          exact ⟨(heq _).trans hregs3.rx1, (heq _).trans hregs3.rx2, (heq _).trans hregs3.rx3, (heq _).trans hregs3.rx4,
            (heq _).trans hregs3.rx7, (heq _).trans hregs3.rx9, (heq _).trans hregs3.rx11, (heq _).trans hregs3.rx13,
            (heq _).trans hregs3.rx14, (heq _).trans hregs3.rx18, (heq _).trans hregs3.rx19, (heq _).trans hregs3.rx20,
            (heq _).trans hregs3.rx21, (heq _).trans hregs3.rx23, (heq _).trans hregs3.rx24, (heq _).trans hregs3.rx26,
            (heq _).trans hregs3.rx27, (heq _).trans hregs3.rx29, (heq _).trans hregs3.rx30, (heq _).trans hregs3.rx31⟩,
        fun a ha => (by simp [s5, s4] : s5.getMem a = s3.getMem a).trans (hro3 a ha),
        baseTableReady_of_lowEq hbt3 (fun a _ => by simp [s5, s4]),
        capMarks15State_of_lowEq hcm3 (fun a _ _ => by simp [s5, s4]),
        slowTablesState_of_eq htbl3 (fun a _ _ => by simp [s5, s4]),
        writerState_of_mem_eq hw3 (fun _ => by simp [s5, s4]) (by simp [s5, s4, getReg_setReg_ne']) (by simp [s5, s4, getReg_setReg_ne']),
        TailState.of_proofWrite ht3 (fun _ _ => by simp [s5, s4]) (by simp [s5, s4, getReg_setReg_ne']) (by simp [s5, s4, getReg_setReg_ne']) (by simp [s5, s4, getReg_setReg_ne'])⟩

/-- Execute one inline `lvlAddrReg .x10 baseReg ++ copy29` step for levels `6..11`. -/
private theorem openRuns_fast_c29_reg {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {pc l idx base dstOff k tailShift prevVal : Nat} {baseReg : Reg}
    {r : Fin 8} {tailInit fl : Bool} {written : List Byte} {s : MachineState}
    (hcode : CodeAt pc (lvlAddrRegCode .x10 baseReg ++ copy29Code r .x10 dstOff .x8 tailShift tailInit fl true))
    (hshift : tailShift = 6 * k) (hinit : tailInit = (k == 0))
    (hl6 : 6 ≤ l) (hl11 : l ≤ 11) (hidx : idx < 16777216) (hsib : (idx ^^^ 1) < levelSize l)
    (hk : k < 6) (hdst_off : dstOff + 32 < 2048) (hdst_bd : base + dstOff + 40 ≤ 8556390424)
    (hbreg_ne : baseReg ≠ .x10 ∧ baseReg ≠ .x22 ∧ baseReg ≠ .x28)
    (hpc : s.pc = pcAt pc)
    (hx11 : s.getReg .x11 = mask40Word)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hbreg : s.getReg baseReg = BitVec.ofNat 64 (4294971424 + levelBase l))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState (CleanTrapdoor trapdoor) s r fl base dstOff written)
    (hpre : TailAccumPre (CleanTrapdoor trapdoor) s .x8 tailShift tailInit prevVal) :
    let d := tdNode trapdoor l (idx ^^^ 1)
    ∃ s' : MachineState,
      OpenRuns s (5 + (copy29Code r .x10 dstOff .x8 tailShift tailInit fl true).length)
        (5 + (copy29Code r .x10 dstOff .x8 tailShift tailInit fl true).length) s' ∧
      s'.pc = pcAt (pc + (5 + (copy29Code r .x10 dstOff .x8 tailShift tailInit fl true).length)) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x22, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' (copy29NextR r) (copy29NextFlushedR4 r true)
        base (copy29NextDstOff r dstOff) (written ++ bitsToBytes d 29) ∧
      (CleanTrapdoor trapdoor → s'.getReg .x8 = BitVec.ofNat 64 (if k = 0 then (tail6 d).toNat else prevVal + (tail6 d).toNat * 2 ^ (6 * k))) := by
  subst hshift; subst hinit
  obtain ⟨s1, hr1, hpc1, hs1_22, hs1_10, hreg1, hmem1⟩ :=
    openRuns_lvl_addr_reg hcode.left hpc (by omega) (by omega) hidx (by decide) ⟨hbreg_ne.2.1, hbreg_ne.2.2⟩ hx22 hbreg
  have hro1 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s1 :=
    fun a ha => (hmem1 a).trans (hro a ha)
  have hw1 := writerState_of_mem_eq hw hmem1 (hreg1 .x25 (by simp)) (hreg1 .x12 (by simp))
  have hpre1 : TailAccumPre (CleanTrapdoor trapdoor) s1 .x8 (6 * k) (k == 0) prevVal := fun hcl => by
    have hp := hpre hcl
    by_cases hk0 : k = 0
    · subst hk0; simp
    · have hb : (k == 0) = false := beq_false_of_ne hk0
      have hb6 : (6 * k == 0) = false := beq_false_of_ne (by omega)
      simp only [hb, hb6, Bool.false_eq_true, ↓reduceIte] at hp ⊢
      exact ⟨hp.1, (hreg1 .x8 (by simp)).trans hp.2⟩
  obtain ⟨s2, hr2, hpc2, hreg2, hp2, hw2, hpost2⟩ := openRuns_copy29 hcode.right hpc1
    (by decide) (by decide) (fun _ _ => by decide) (by omega)
    ((hreg1 .x11 (by simp)).trans hx11) hs1_10
    (by have h1 := levelBase_align8' l (by omega); have h2 := nodeOffset_align8' l (idx ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' l _ (by omega) hsib; omega)
    (fun _ q hq => readOnly_getMem_tdNode hro1 l _ q (by omega) hsib hq)
    (fun hcl => hcl.2 l hl6 (by omega) _ hsib) hdst_off hdst_bd hw1 hpre1
  refine ⟨s2, hr1.trans hr2,
    by rw [hpc2]; simp only [lvlAddrRegCode, List.length_cons, List.length_nil]; apply congrArg pcAt; omega,
    (hreg2 .x22 (by simp)).trans hs1_22, ?_,
    ProofWritePreserves.trans (fun a _ => hmem1 a) hp2, hw2, fun hcl => ?_⟩
  · intro reg hreg
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg2 reg (by simp [h5', h6', h10', h12', h8'])).trans (hreg1 reg (by simp [h10', h22', h28']))
  · have hp := hpost2 hcl
    by_cases hk0 : k = 0
    · subst hk0; simpa using hp
    · have hb : (k == 0) = false := beq_false_of_ne hk0
      have hb6 : (6 * k == 0) = false := beq_false_of_ne (by omega)
      simp only [hb, hb6, Bool.false_eq_true, ↓reduceIte] at hp
      simpa [hk0] using hp

/-- Execute one inline `lvlAddrMem .x10 l ++ copy29` step for levels `13..14`. -/
private theorem openRuns_fast_c29_mem {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {pc l idx base dstOff k tailShift prevVal : Nat}
    {r : Fin 8} {fl flushR7 : Bool} {written : List Byte} {s : MachineState}
    (hcode : CodeAt pc (lvlAddrMemCode .x10 l ++ copy29Code r .x10 dstOff .x8 tailShift false fl flushR7))
    (hshift : tailShift = 6 * k)
    (hl6 : 6 ≤ l) (hl14 : l ≤ 14) (hidx : idx < 16777216) (hsib : (idx ^^^ 1) < levelSize l)
    (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (hdst_off : dstOff + 32 < 2048) (hdst_bd : base + dstOff + 40 ≤ 8556390424)
    (hpc : s.pc = pcAt pc)
    (hx11 : s.getReg .x11 = mask40Word)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hbt : BaseTableReady s)
    (hw : WriterState (CleanTrapdoor trapdoor) s r fl base dstOff written)
    (hprev : CleanTrapdoor trapdoor → prevVal < 2 ^ (6 * k) ∧ s.getReg .x8 = BitVec.ofNat 64 prevVal) :
    let d := tdNode trapdoor l (idx ^^^ 1)
    ∃ s' : MachineState,
      OpenRuns s (6 + (copy29Code r .x10 dstOff .x8 tailShift false fl flushR7).length)
        (6 + (copy29Code r .x10 dstOff .x8 tailShift false fl flushR7).length) s' ∧
      s'.pc = pcAt (pc + (6 + (copy29Code r .x10 dstOff .x8 tailShift false fl flushR7).length)) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x22, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' (copy29NextR r) (copy29NextFlushedR4 r flushR7)
        base (copy29NextDstOff r dstOff) (written ++ bitsToBytes d 29) ∧
      (CleanTrapdoor trapdoor → s'.getReg .x8 = BitVec.ofNat 64 (prevVal + (tail6 d).toNat * 2 ^ (6 * k))) := by
  subst hshift
  obtain ⟨s1, hr1, hpc1, hs1_22, hs1_10, hreg1, hmem1⟩ :=
    openRuns_lvl_addr_mem hcode.left hpc (by omega) (by omega) hidx (by decide) hx22 hbt
  have hro1 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s1 :=
    fun a ha => (hmem1 a).trans (hro a ha)
  have hw1 := writerState_of_mem_eq hw hmem1 (hreg1 .x25 (by simp)) (hreg1 .x12 (by simp))
  have hb6 : (6 * k == 0) = false := beq_false_of_ne (by omega)
  have hpre1 : TailAccumPre (CleanTrapdoor trapdoor) s1 .x8 (6 * k) false prevVal := fun hcl => by
    simp only [Bool.false_eq_true, hb6, ↓reduceIte]
    exact ⟨(hprev hcl).1, (hreg1 .x8 (by simp)).trans (hprev hcl).2⟩
  obtain ⟨s2, hr2, hpc2, hreg2, hp2, hw2, hpost2⟩ := openRuns_copy29 hcode.right hpc1
    (by decide) (by decide) (fun _ _ => by decide) (by omega)
    ((hreg1 .x11 (by simp)).trans hx11) hs1_10
    (by have h1 := levelBase_align8' l (by omega); have h2 := nodeOffset_align8' l (idx ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' l _ (by omega) hsib; omega)
    (fun _ q hq => readOnly_getMem_tdNode hro1 l _ q (by omega) hsib hq)
    (fun hcl => hcl.2 l hl6 (by omega) _ hsib) hdst_off hdst_bd hw1 hpre1
  refine ⟨s2, hr1.trans hr2,
    by rw [hpc2]; simp only [lvlAddrMemCode, List.length_cons, List.length_nil]; apply congrArg pcAt; omega,
    (hreg2 .x22 (by simp)).trans hs1_22, ?_,
    ProofWritePreserves.trans (fun a _ => hmem1 a) hp2, hw2, fun hcl => by
      have hp := hpost2 hcl; simp only [Bool.false_eq_true, hb6, ↓reduceIte] at hp; exact hp⟩
  intro reg hreg
  have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
  have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
  have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
  have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
  have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
  have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
  have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
  exact (hreg2 reg (by simp [h5', h6', h10', h12', h8'])).trans (hreg1 reg (by simp [h10', h22', h28']))

/-- Execute `l12RestAddrCode ++ copy29` (`4 + len(copy29)` cyc) given `x28 = (g>>>11) ^^^ 1` and `x22 = g>>>12`. -/
private theorem openRuns_fast_l12 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {pc idx11 base dstOff prevVal : Nat}
    {r : Fin 8} {fl : Bool} {written : List Byte} {s : MachineState}
    (hcode : CodeAt pc (l12RestAddrCode ++ copy29Code r .x10 dstOff .x8 36 false fl true))
    (_hidx : idx11 < 16777216) (hsib : (idx11 ^^^ 1) < levelSize 12)
    (hdst_off : dstOff + 32 < 2048) (hdst_bd : base + dstOff + 40 ≤ 8556390424)
    (hpc : s.pc = pcAt pc)
    (hx11 : s.getReg .x11 = mask40Word)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (idx11 / 2))
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 (idx11 ^^^ 1))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hbt : BaseTableReady s)
    (hw : WriterState (CleanTrapdoor trapdoor) s r fl base dstOff written)
    (hprev : CleanTrapdoor trapdoor → prevVal < 2 ^ 36 ∧ s.getReg .x8 = BitVec.ofNat 64 prevVal) :
    let d := tdNode trapdoor 12 (idx11 ^^^ 1)
    ∃ s' : MachineState,
      OpenRuns s (4 + (copy29Code r .x10 dstOff .x8 36 false fl true).length)
        (4 + (copy29Code r .x10 dstOff .x8 36 false fl true).length) s' ∧
      s'.pc = pcAt (pc + (4 + (copy29Code r .x10 dstOff .x8 36 false fl true).length)) ∧
      RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' (copy29NextR r) (copy29NextFlushedR4 r true)
        base (copy29NextDstOff r dstOff) (written ++ bitsToBytes d 29) ∧
      (CleanTrapdoor trapdoor → s'.getReg .x8 = BitVec.ofNat 64 (prevVal + (tail6 d).toNat * 2 ^ 36)) := by
  have hcL := hcode.left
  have hbd : pc + 4 ≤ OPEN_CODE_LEN := by have := hcL.1; simpa [l12RestAddrCode] using this
  have hi0 : openInstr pc = .base (.ADD .x28 .x28 .x22) := by have h := hcL.2 0 (by simp [l12RestAddrCode]); simpa [l12RestAddrCode] using h
  have hi1 : openInstr (pc + 1) = .base (.SLLI .x28 .x28 (5#6)) := by have h := hcL.2 1 (by simp [l12RestAddrCode]); simpa [l12RestAddrCode] using h
  have hi2 : openInstr (pc + 2) = .base (.LD .x10 .x0 (96#12)) := by have h := hcL.2 2 (by simp [l12RestAddrCode]); simpa [l12RestAddrCode] using h
  have hi3 : openInstr (pc + 3) = .base (.ADD .x10 .x10 .x28) := by have h := hcL.2 3 (by simp [l12RestAddrCode]); simpa [l12RestAddrCode] using h
  have h0 := step_ADD (s := s) (by omega) hpc hi0
  set s1 := (s.setReg .x28 (s.getReg .x28 + s.getReg .x22)).setPC (pcAt (pc + 1))
  have h1 := step_SLLI (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x28 (s1.getReg .x28 <<< (5#6).toNat)).setPC (pcAt (pc + 1 + 1))
  have hld_val : accessValid (s2.getReg .x0 + signExtend12 (96#12)) 8 = true := by
    rw [show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 96 (by omega), BitVec.zero_add]
    exact accessValid_ofNat 96 8 (by decide) (by decide)
  have h2 := step_LD (s := s2) (by omega) (by congr 1) hi2 hld_val
  set s3 := (s2.setReg .x10 (s2.getMem (s2.getReg .x0 + signExtend12 (96#12)))).setPC (pcAt (pc + 2 + 1))
  have h3 := step_ADD (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg .x10 (s3.getReg .x10 + s3.getReg .x28)).setPC (pcAt (pc + 3 + 1))
  have hs4_10 : s4.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 12 + nodeOffset 12 (idx11 ^^^ 1)) := by
    have hsum : (idx11 ^^^ 1) + idx11 / 2 = (idx11 ^^^ 1) + (idx11 ^^^ 1) / 2 := by
      have : (idx11 ^^^ 1) / 2 = idx11 / 2 := by
        have := @Nat.shiftRight_xor_distrib 1 idx11 1
        simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one, show (1 : Nat) / 2 = 0 by decide, Nat.xor_zero] at this
        exact this
      omega
    have h2_28 : s2.getReg .x28 = BitVec.ofNat 64 (nodeOffset 12 (idx11 ^^^ 1)) := by
      have h1_28 : s1.getReg .x28 = BitVec.ofNat 64 ((idx11 ^^^ 1) + idx11 / 2) := by
        simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq,
          not_false_eq_true, hx28, hx22, ← BitVec.ofNat_add]
      simp [s2, h1_28, bv64_shl, nodeOffset, gapOffset, hsum]; apply congrArg (BitVec.ofNat 64); omega
    have h3_10 : s3.getReg .x10 = BitVec.ofNat 64 (4294971424 + levelBase 12) := by
      have e : s3.getReg .x10 = s2.getMem (s2.getReg .x0 + signExtend12 (96#12)) := by simp [s3]
      rw [e, show s2.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 96 (by omega), BitVec.zero_add]
      have hm : s2.getMem (BitVec.ofNat 64 96) = s.getMem (BitVec.ofNat 64 96) := by simp [s2, s1]
      rw [hm]; exact hbt.lvlBase 12 (by omega) (by omega)
    simp [s4, h3_10, show s3.getReg .x28 = s2.getReg .x28 by simp [s3, getReg_setReg_ne'], h2_28, ← BitVec.ofNat_add]
  have hmem4 : ∀ a, s4.getMem a = s.getMem a := fun a => by simp [s4, s3, s2, s1]
  have hro4 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s4 := fun a ha => (hmem4 a).trans (hro a ha)
  have hw4 := writerState_of_mem_eq hw hmem4 (by simp [s4, s3, s2, s1, getReg_setReg_ne']) (by simp [s4, s3, s2, s1, getReg_setReg_ne'])
  have hpre4 : TailAccumPre (CleanTrapdoor trapdoor) s4 .x8 36 false prevVal := fun hcl => by
    simp only [Bool.false_eq_true, show (36 == 0) = false by decide, ↓reduceIte]
    exact ⟨(hprev hcl).1, by simp [s4, s3, s2, s1, getReg_setReg_ne', (hprev hcl).2]⟩
  obtain ⟨s5, hr5, hpc5, hreg5, hp5, hw5, hpost5⟩ := openRuns_copy29 hcode.right
    (by dsimp only [s4, MachineState.setPC]; simp only [l12RestAddrCode, List.length_cons, List.length_nil])
    (by decide) (by decide) (fun _ _ => by decide) (by omega)
    (by simp [s4, s3, s2, s1, getReg_setReg_ne', hx11]) hs4_10
    (by have h1 := levelBase_align8' 12 (by omega); have h2 := nodeOffset_align8' 12 (idx11 ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' 12 _ (by omega) hsib; omega)
    (fun _ q hq => readOnly_getMem_tdNode hro4 12 _ q (by omega) hsib hq)
    (fun hcl => hcl.2 12 (by omega) (by omega) _ hsib) hdst_off hdst_bd hw4 hpre4
  refine ⟨s5, (((h0.trans h1).trans h2).trans h3).trans hr5,
    by rw [hpc5]; simp only [l12RestAddrCode, List.length_cons, List.length_nil]; apply congrArg pcAt; omega, ?_,
    ProofWritePreserves.trans (fun a _ => hmem4 a) hp5, hw5, fun hcl => by
      have hp := hpost5 hcl; simp only [Bool.false_eq_true, show (36 == 0) = false by decide, ↓reduceIte] at hp; exact hp⟩
  intro reg hreg
  have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
  have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
  have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
  have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
  have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
  have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
  exact (hreg5 reg (by simp [h5', h6', h10', h12', h8'])).trans
    (by simp [s4, s3, s2, s1, getReg_setReg_ne' .x10 reg h10'.symm, getReg_setReg_ne' .x28 reg h28'.symm])

/-- Execute one inline `lvlAddrReg .x10 baseReg ++ copy30` step for levels `2..5`. -/
private theorem openRuns_fast_c30_reg {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {pc l idx base dstOff : Nat} {baseReg : Reg}
    {r : Fin 8} {fl : Bool} {written : List Byte} {s : MachineState}
    (hcode : CodeAt pc (lvlAddrRegCode .x10 baseReg ++ copy30Code r .x10 dstOff fl))
    (hl2 : 2 ≤ l) (hl5 : l ≤ 5) (hidx : idx < 16777216) (hsib : (idx ^^^ 1) < levelSize l)
    (hdst_off : dstOff + 32 < 2048) (hdst_bd : base + dstOff + 40 ≤ 8556390424)
    (hbreg_ne : baseReg ≠ .x10 ∧ baseReg ≠ .x22 ∧ baseReg ≠ .x28)
    (hpc : s.pc = pcAt pc)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 idx)
    (hbreg : s.getReg baseReg = BitVec.ofNat 64 (4294971424 + levelBase l))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState (CleanTrapdoor trapdoor) s r fl base dstOff written) :
    let d := tdNode trapdoor l (idx ^^^ 1)
    ∃ s' : MachineState,
      OpenRuns s (5 + (copy30Code r .x10 dstOff fl).length) (5 + (copy30Code r .x10 dstOff fl).length) s' ∧
      s'.pc = pcAt (pc + (5 + (copy30Code r .x10 dstOff fl).length)) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (idx / 2) ∧
      RegsEqExcept [.x5, .x6, .x10, .x12, .x22, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' (copy30NextR r) false base (copy30NextDstOff r dstOff)
        (written ++ bitsToBytes d 30) := by
  obtain ⟨s1, hr1, hpc1, hs1_22, hs1_10, hreg1, hmem1⟩ :=
    openRuns_lvl_addr_reg hcode.left hpc (by omega) (by omega) hidx (by decide) ⟨hbreg_ne.2.1, hbreg_ne.2.2⟩ hx22 hbreg
  have hro1 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s1 :=
    fun a ha => (hmem1 a).trans (hro a ha)
  have hw1 := writerState_of_mem_eq hw hmem1 (hreg1 .x25 (by simp)) (hreg1 .x12 (by simp))
  obtain ⟨s2, hr2, hpc2, hreg2, hp2, hw2⟩ := openRuns_copy30 hcode.right hpc1
    (by decide) hs1_10
    (by have h1 := levelBase_align8' l (by omega); have h2 := nodeOffset_align8' l (idx ^^^ 1); omega)
    (by have := nodeOffset_lt_treeBytes' l _ (by omega) hsib; omega)
    (fun _ q hq => readOnly_getMem_tdNode hro1 l _ q (by omega) hsib hq)
    (fun hcl => hcl.1 l hl2 hl5 _ hsib) hdst_off hdst_bd hw1
  refine ⟨s2, hr1.trans hr2,
    by rw [hpc2]; simp only [lvlAddrRegCode, List.length_cons, List.length_nil]; apply congrArg pcAt; omega,
    (hreg2 .x22 (by simp)).trans hs1_22, ?_,
    ProofWritePreserves.trans (fun a _ => hmem1 a) hp2, hw2⟩
  intro reg hreg
  have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
  have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
  have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
  have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
  have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
  have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
  exact (hreg2 reg (by simp [h5', h6', h12'])).trans (hreg1 reg (by simp [h10', h22', h28']))

private theorem bitsOf6_snoc (ts : List (BitVec 6)) (t : BitVec 6) :
    bitsOf6 (ts ++ [t]) = bitsOf6 ts + t.toNat * 2 ^ (6 * ts.length) := by
  rw [bitsOf6_append]; simp only [bitsOf6, List.foldr_cons, List.foldr_nil, Nat.zero_mul, Nat.add_zero, Nat.mul_comm]

private theorem recL3_bd (r : Fin 8) : (recL3State r).2 + 32 < 2048 ∧ (recL3State r).2 ≤ 152 := by
  fin_cases r <;> decide

private theorem recL4_bd (r : Fin 8) : (recL4State r).2 + 32 < 2048 ∧ (recL4State r).2 ≤ 184 := by
  fin_cases r <;> decide

private theorem recL5_bd (r : Fin 8) : (recL5State r).2 + 32 < 2048 ∧ (recL5State r).2 ≤ 216 := by
  fin_cases r <;> decide

private theorem recC29_bds (r : Fin 8) :
    (recL7St r).2.1 ≤ 272 ∧ (recL8St r).2.1 ≤ 304 ∧ (recL9St r).2.1 ≤ 336 ∧
    (recL10St r).2.1 ≤ 368 ∧ (recL11St r).2.1 ≤ 400 ∧ (recL12St r).2.1 ≤ 432 ∧
    (recL13St r).2.1 ≤ 464 ∧ (recL12St r).2.1 % 8 = 0 ∧
    copy29NextDstOff (recL12St r).1 (recL12St r).2.1 < 2048 ∧
    copy29NextDstOff (recL12St r).1 (recL12St r).2.1 % 8 = 0 ∧
    copy29NextDstOff r 472 < 2048 ∧ copy29NextDstOff r 472 % 8 = 0 := by
  fin_cases r <;> decide

/-- Execute `recL0L5Code r0` (`L0a, L0b, L1, L2..L5`) from `pcSlowGuard r0 + 1`! -/
private theorem openRuns_rec_l0_l5 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base : Nat} {r0 : Fin 8} {written : List Byte} {s : MachineState}
    (hord : ordinal < positions.card) (hbd_w : base + 528 ≤ 8556390424)
    (hg : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592064)
    (hcode : CodeAt (pcSlowGuard r0 + 1) (recL0L5Code r0))
    (hpc : s.pc = pcAt (pcSlowGuard r0 + 1))
    (hregs : RecRegs positions ordinal s)
    (hx6 : s.getReg .x6 = BitVec.ofNat 64 (3 * (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3)))
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val % 3))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState (CleanTrapdoor trapdoor) s r0 (r0.val == 4) base 24
            (written ++ bitsToBytes (tdSalt trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord]))) 24)) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let g := i.val / 3
    let l0l5 := bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx i)) 32 ++
      bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32 ++
      bitsToBytes (tdNode trapdoor 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 3 ((g >>> 2) ^^^ 1)) 30 ++
      bitsToBytes (tdNode trapdoor 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 5 ((g >>> 4) ^^^ 1)) 30
    ∃ cyc s',
      OpenRuns s cyc cyc s' ∧
      cyc ≤ (recL0L5Code r0).length - 2 ∧
      s'.pc = pcAt (pcSlowGuard r0 + 1 + (recL0L5Code r0).length) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (g >>> 5) ∧
      RegsEqExcept [.x5, .x6, .x10, .x12, .x22, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' r0 false base 240
        (written ++ bitsToBytes (tdSalt trapdoor i) 24 ++ l0l5) := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have hl0a_lt : l0Sib1Idx i < levelSize 0 := by unfold l0Sib1Idx; rw [levelSize_0]; split_ifs <;> omega
  have hl0b_lt : l0Sib2Idx i < levelSize 0 := by unfold l0Sib2Idx; rw [levelSize_0]; split_ifs <;> omega
  have hl1_lt : (g ^^^ 1) < levelSize 1 := by rw [levelSize_1]; exact xor_one_lt_even (m := 2796203) (by omega)
  have hcode' : CodeAt (pcSlowGuard r0 + 1) (l0SibsCode ++
      (dwordsCode r0 4 .x10 0 24 (r0.val == 4) (r0.val == 4) ++
      (dwordsCode r0 4 .x28 0 56 (r0.val == 4) (r0.val == 4) ++
      (lvlAddrRegCode .x10 .x1 ++
      (dwordsCode r0 4 .x10 0 88 (r0.val == 4) (r0.val == 4) ++
      ((lvlAddrRegCode .x10 .x2 ++ copy30Code r0 .x10 120 (r0.val == 4)) ++
      ((lvlAddrRegCode .x10 .x14 ++ copy30Code (recL3State r0).1 .x10 (recL3State r0).2 false) ++
      ((lvlAddrRegCode .x10 .x21 ++ copy30Code (recL4State r0).1 .x10 (recL4State r0).2 false) ++
      (lvlAddrRegCode .x10 .x26 ++ copy30Code (recL5State r0).1 .x10 (recL5State r0).2 false))))))))) := by
    simpa only [recL0L5Code, List.append_assoc] using hcode
  have hc_sib := hcode'.left; have hrA := hcode'.right
  have hc_l0a := hrA.left; have hrB := hrA.right
  have hc_l0b := hrB.left; have hrC := hrB.right
  have hc_l1a := hrC.left; have hrD := hrC.right
  have hc_l1d := hrD.left; have hrE := hrD.right
  have hc_l2 := hrE.left; have hrF := hrE.right
  have hc_l3 := hrF.left; have hrG := hrF.right
  have hc_l4 := hrG.left; have hc_l5 := hrG.right
  -- L0 sibs + L0a + L0b
  obtain ⟨cL0, s1, hr1, hcL0, hpc1, hs1_10, hs1_28, hreg1, hmem1⟩ :=
    openRuns_l0_sibs hc_sib hpc hregs.rx4 hx6 hx8 hregs.rx9
  have hro1 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s1 := fun a ha => (hmem1 a).trans (hro a ha)
  have hw1 := writerState_of_mem_eq hw hmem1 (hreg1 .x25 (by simp)) (hreg1 .x12 (by simp))
  obtain ⟨s2, hr2, hpc2, hreg2, hp2, hw2⟩ := openRuns_dwords 4 (s := s1)
    (vals := fun k => (tdNode trapdoor 0 (l0Sib1Idx i)).extractLsb' (64 * k) 64)
    (by omega) hc_l0a hpc1 (by decide) hs1_10
    (by have h1 := levelBase_align8' 0 (by omega); have h2 := nodeOffset_align8' 0 (l0Sib1Idx i); omega) (by omega)
    (by have := nodeOffset_lt_treeBytes' 0 _ (by omega) hl0a_lt; omega)
    (fun _ k hk => by simpa only [Nat.add_zero] using readOnly_getMem_tdNode hro1 0 _ k (by omega) hl0a_lt hk)
    (by omega) (by omega) hw1
  rw [(bitsToBytes_take_dwords _ 4).symm, Bool.and_self] at hw2
  have hro2 := ReadOnlyPreserved.of_proofWrite hro1 hp2
  obtain ⟨s3, hr3, hpc3, hreg3, hp3, hw3⟩ := openRuns_dwords 4 (s := s2)
    (vals := fun k => (tdNode trapdoor 0 (l0Sib2Idx i)).extractLsb' (64 * k) 64)
    (by omega) hc_l0b hpc2 (by decide) ((hreg2 .x28 (by simp)).trans hs1_28)
    (by have h1 := levelBase_align8' 0 (by omega); have h2 := nodeOffset_align8' 0 (l0Sib2Idx i); omega) (by omega)
    (by have := nodeOffset_lt_treeBytes' 0 _ (by omega) hl0b_lt; omega)
    (fun _ k hk => by simpa only [Nat.add_zero] using readOnly_getMem_tdNode hro2 0 _ k (by omega) hl0b_lt hk)
    (by omega) (by omega) hw2
  rw [(bitsToBytes_take_dwords _ 4).symm, Bool.and_self] at hw3
  have hro3 := ReadOnlyPreserved.of_proofWrite hro2 hp3
  -- L1
  obtain ⟨s4a, hr4a, hpc4a, hs4a_22, hs4a_10, hreg4a, hmem4a⟩ := openRuns_lvl_addr_reg hc_l1a hpc3
    (by omega) (by omega) (by omega) (by decide) (by decide)
    ((hreg3 .x22 (by simp)).trans ((hreg2 .x22 (by simp)).trans ((hreg1 .x22 (by simp)).trans hx22)))
    ((hreg3 .x1 (by simp)).trans ((hreg2 .x1 (by simp)).trans ((hreg1 .x1 (by simp)).trans hregs.rx1)))
  have hro4a : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s4a := fun a ha => (hmem4a a).trans (hro3 a ha)
  have hw4a := writerState_of_mem_eq hw3 hmem4a (hreg4a .x25 (by simp)) (hreg4a .x12 (by simp))
  obtain ⟨s4, hr4, hpc4, hreg4, hp4, hw4⟩ := openRuns_dwords 4 (s := s4a)
    (vals := fun k => (tdNode trapdoor 1 (g ^^^ 1)).extractLsb' (64 * k) 64)
    (by omega) hc_l1d hpc4a (by decide) hs4a_10
    (by have h1 := levelBase_align8' 1 (by omega); have h2 := nodeOffset_align8' 1 (g ^^^ 1); omega) (by omega)
    (by have := nodeOffset_lt_treeBytes' 1 _ (by omega) hl1_lt; omega)
    (fun _ k hk => by simpa only [Nat.add_zero] using readOnly_getMem_tdNode hro4a 1 _ k (by omega) hl1_lt hk)
    (by omega) (by omega) hw4a
  rw [(bitsToBytes_take_dwords _ 4).symm, Bool.and_self] at hw4
  have hro4 := ReadOnlyPreserved.of_proofWrite hro4a hp4
  have hs4_22 : s4.getReg .x22 = BitVec.ofNat 64 (g >>> 1) := by
    have h := (hreg4 .x22 (by simp)).trans hs4a_22
    simpa only [show g / 2 = g >>> 1 by simp [Nat.shiftRight_eq_div_pow]] using h
  have hreg40 : RegsEqExcept [.x5, .x6, .x10, .x12, .x22, .x28] s s4 := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg4 reg (by simp [h5', h6', h12'])).trans ((hreg4a reg (by simp [h10', h22', h28'])).trans
      ((hreg3 reg (by simp [h5', h6', h12'])).trans ((hreg2 reg (by simp [h5', h6', h12'])).trans
       (hreg1 reg (by simp [h10', h28'])))))
  -- L2..L5
  obtain ⟨s5, hr5, hpc5, hs5_22, hreg5, hp5, hw5⟩ := openRuns_fast_c30_reg hc_l2 (by omega) (by omega)
    (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.1 (by omega) (by omega) (by decide)
    hpc4 hs4_22 ((hreg40 .x2 (by simp)).trans hregs.rx2) hro4 hw4
  rw [div2_ushr_eq g 1 2] at hs5_22
  have hro5 := ReadOnlyPreserved.of_proofWrite hro4 hp5
  obtain ⟨s6, hr6, hpc6, hs6_22, hreg6, hp6, hw6⟩ := openRuns_fast_c30_reg hc_l3 (by omega) (by omega)
    (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.1 (recL3_bd r0).1 (by have := (recL3_bd r0).2; omega) (by decide)
    (by rw [hpc5]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    hs5_22 ((hreg5 .x14 (by simp)).trans ((hreg40 .x14 (by simp)).trans hregs.rx14)) hro5 hw5
  rw [div2_ushr_eq g 2 3] at hs6_22
  have hro6 := ReadOnlyPreserved.of_proofWrite hro5 hp6
  obtain ⟨s7, hr7, hpc7, hs7_22, hreg7, hp7, hw7⟩ := openRuns_fast_c30_reg hc_l4 (by omega) (by omega)
    (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.1 (recL4_bd r0).1 (by have := (recL4_bd r0).2; omega) (by decide)
    (by rw [hpc6]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    hs6_22 ((hreg6 .x21 (by simp)).trans ((hreg5 .x21 (by simp)).trans ((hreg40 .x21 (by simp)).trans hregs.rx21))) hro6 hw6
  rw [div2_ushr_eq g 3 4] at hs7_22
  have hro7 := ReadOnlyPreserved.of_proofWrite hro6 hp7
  obtain ⟨s8, hr8, hpc8, hs8_22, hreg8, hp8, hw8⟩ := openRuns_fast_c30_reg hc_l5 (by omega) (by omega)
    (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.1 (recL5_bd r0).1 (by have := (recL5_bd r0).2; omega) (by decide)
    (by rw [hpc7]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    hs7_22 ((hreg7 .x26 (by simp)).trans ((hreg6 .x26 (by simp)).trans ((hreg5 .x26 (by simp)).trans ((hreg40 .x26 (by simp)).trans hregs.rx26)))) hro7 hw7
  rw [div2_ushr_eq g 4 5] at hs8_22
  have hfin := recL5_finish r0
  rw [hfin.1, hfin.2] at hw8
  refine ⟨_, s8, (((((((hr1.trans hr2).trans hr3).trans hr4a).trans hr4).trans hr5).trans hr6).trans hr7).trans hr8,
    by simp only [recL0L5Code, List.length_append, l0SibsCode, lvlAddrRegCode, List.length_cons, List.length_nil]; omega,
    by rw [hpc8]; simp only [recL0L5Code, List.length_append, l0SibsCode, lvlAddrRegCode, List.length_cons, List.length_nil]; apply congrArg pcAt; omega,
    hs8_22,
    fun reg hreg => (hreg8 reg hreg).trans ((hreg7 reg hreg).trans ((hreg6 reg hreg).trans ((hreg5 reg hreg).trans (hreg40 reg hreg)))),
    ProofWritePreserves.trans (fun a _ => hmem1 a) <| hp2.trans <| hp3.trans <| ProofWritePreserves.trans (fun a _ => hmem4a a) <| hp4.trans <| hp5.trans <| hp6.trans <| hp7.trans hp8,
    by simpa only [List.append_assoc] using hw8⟩

/-- Execute `recL6L11Code r0` (`L6..L11`, 6 × `lvlAddrReg + copy29`) starting from `r0, dstOff=240, fl=false`. -/
private theorem openRuns_rec_l6_l11 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal pc base : Nat} {r0 : Fin 8} {written : List Byte} {s : MachineState}
    (hord : ordinal < positions.card) (hbd_w : base + 528 ≤ 8556390424)
    (hg : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592064)
    (hcode : CodeAt pc (recL6L11Code r0))
    (hpc : s.pc = pcAt pc)
    (hregs : RecRegs positions ordinal s)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 5))
    (hro : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState (CleanTrapdoor trapdoor) s r0 false base 240 written) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let g := i.val / 3
    let l6l11 := bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 10 ((g >>> 9) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29
    let ts6 := [tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)),
      tail6 (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)),
      tail6 (tdNode trapdoor 10 ((g >>> 9) ^^^ 1)), tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1))]
    ∃ s',
      OpenRuns s (recL6L11Code r0).length (recL6L11Code r0).length s' ∧
      s'.pc = pcAt (pc + (recL6L11Code r0).length) ∧
      s'.getReg .x22 = BitVec.ofNat 64 (g >>> 11) ∧
      (CleanTrapdoor trapdoor → s'.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts6)) ∧
      RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x22, .x28] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState (CleanTrapdoor trapdoor) s' (recL12St r0).1 (recL12St r0).2.2 base (recL12St r0).2.1
        (written ++ l6l11) := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have hbds := recC29_bds r0
  have hcode' : CodeAt pc ((lvlAddrRegCode .x10 .x29 ++ copy29Code (recL6St r0).1 .x10 (recL6St r0).2.1 .x8 0 true (recL6St r0).2.2 true) ++
      ((lvlAddrRegCode .x10 .x30 ++ copy29Code (recL7St r0).1 .x10 (recL7St r0).2.1 .x8 6 false (recL7St r0).2.2 true) ++
      ((lvlAddrRegCode .x10 .x31 ++ copy29Code (recL8St r0).1 .x10 (recL8St r0).2.1 .x8 12 false (recL8St r0).2.2 true) ++
      ((lvlAddrRegCode .x10 .x23 ++ copy29Code (recL9St r0).1 .x10 (recL9St r0).2.1 .x8 18 false (recL9St r0).2.2 true) ++
      ((lvlAddrRegCode .x10 .x7 ++ copy29Code (recL10St r0).1 .x10 (recL10St r0).2.1 .x8 24 false (recL10St r0).2.2 true) ++
      (lvlAddrRegCode .x10 .x3 ++ copy29Code (recL11St r0).1 .x10 (recL11St r0).2.1 .x8 30 false (recL11St r0).2.2 true)))))) := by
    simpa only [recL6L11Code, List.append_assoc] using hcode
  have hc6 := hcode'.left; have hr1 := hcode'.right
  have hc7 := hr1.left; have hr2 := hr1.right
  have hc8 := hr2.left; have hr3 := hr2.right
  have hc9 := hr3.left; have hr4 := hr3.right
  have hc10 := hr4.left; have hc11 := hr4.right
  set t6 := tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1))
  set t7 := tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1))
  set t8 := tail6 (tdNode trapdoor 8 ((g >>> 7) ^^^ 1))
  set t9 := tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1))
  set t10 := tail6 (tdNode trapdoor 10 ((g >>> 9) ^^^ 1))
  set t11 := tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1))
  obtain ⟨s1, hr1', hpc1, hs1_22, hreg1, hp1, hw1, hx8_1⟩ := openRuns_fast_c29_reg (k := 0) (prevVal := 0) hc6 rfl rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.1 (by omega)
    (by dsimp only [recL6St]; omega) (by dsimp only [recL6St]; omega)
    (by decide) hpc hregs.rx11 hx22 hregs.rx29 hro hw (fun _ => by simp)
  rw [div2_ushr_eq g 5 6] at hs1_22
  have hro1 := ReadOnlyPreserved.of_proofWrite hro hp1
  have hx8_1' : CleanTrapdoor trapdoor → s1.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [t6]) := fun hcl => by
    simpa [bitsOf6] using hx8_1 hcl
  obtain ⟨s2, hr2', hpc2, hs2_22, hreg2, hp2, hw2, hx8_2⟩ := openRuns_fast_c29_reg (k := 1) (prevVal := bitsOf6 [t6]) hc7 rfl rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.1 (by omega)
    (by have := hbds.1; omega) (by have := hbds.1; omega)
    (by decide)
    (by rw [hpc1]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg1 .x11 (by simp)).trans hregs.rx11) hs1_22 ((hreg1 .x30 (by simp)).trans hregs.rx30) hro1 hw1
    (fun hcl => ⟨bitsOf6_lt [t6], hx8_1' hcl⟩)
  rw [div2_ushr_eq g 6 7] at hs2_22
  have hro2 := ReadOnlyPreserved.of_proofWrite hro1 hp2
  have hx8_2' : CleanTrapdoor trapdoor → s2.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [t6, t7]) := fun hcl => by
    have h := hx8_2 hcl; simp only [show ¬ (1 = 0) by decide, ↓reduceIte] at h
    simpa only [show [t6, t7] = [t6] ++ [t7] from rfl, bitsOf6_snoc, List.length_singleton] using h
  obtain ⟨s3, hr3', hpc3, hs3_22, hreg3, hp3, hw3, hx8_3⟩ := openRuns_fast_c29_reg (k := 2) (prevVal := bitsOf6 [t6, t7]) hc8 rfl rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.2.1 (by omega)
    (by have := hbds.2.1; omega) (by have := hbds.2.1; omega)
    (by decide)
    (by rw [hpc2]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg2 .x11 (by simp)).trans ((hreg1 .x11 (by simp)).trans hregs.rx11)) hs2_22
    ((hreg2 .x31 (by simp)).trans ((hreg1 .x31 (by simp)).trans hregs.rx31)) hro2 hw2
    (fun hcl => ⟨bitsOf6_lt [t6, t7], hx8_2' hcl⟩)
  rw [div2_ushr_eq g 7 8] at hs3_22
  have hro3 := ReadOnlyPreserved.of_proofWrite hro2 hp3
  have hx8_3' : CleanTrapdoor trapdoor → s3.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [t6, t7, t8]) := fun hcl => by
    have h := hx8_3 hcl; simp only [show ¬ (2 = 0) by decide, ↓reduceIte] at h
    simpa only [show [t6, t7, t8] = [t6, t7] ++ [t8] from rfl, bitsOf6_snoc, List.length_cons, List.length_nil] using h
  obtain ⟨s4, hr4', hpc4, hs4_22, hreg4, hp4, hw4, hx8_4⟩ := openRuns_fast_c29_reg (k := 3) (prevVal := bitsOf6 [t6, t7, t8]) hc9 rfl rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.2.2.1 (by omega)
    (by have := hbds.2.2.1; omega) (by have := hbds.2.2.1; omega)
    (by decide)
    (by rw [hpc3]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg3 .x11 (by simp)).trans ((hreg2 .x11 (by simp)).trans ((hreg1 .x11 (by simp)).trans hregs.rx11))) hs3_22
    ((hreg3 .x23 (by simp)).trans ((hreg2 .x23 (by simp)).trans ((hreg1 .x23 (by simp)).trans hregs.rx23))) hro3 hw3
    (fun hcl => ⟨bitsOf6_lt [t6, t7, t8], hx8_3' hcl⟩)
  rw [div2_ushr_eq g 8 9] at hs4_22
  have hro4 := ReadOnlyPreserved.of_proofWrite hro3 hp4
  have hx8_4' : CleanTrapdoor trapdoor → s4.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [t6, t7, t8, t9]) := fun hcl => by
    have h := hx8_4 hcl; simp only [show ¬ (3 = 0) by decide, ↓reduceIte] at h
    simpa only [show [t6, t7, t8, t9] = [t6, t7, t8] ++ [t9] from rfl, bitsOf6_snoc, List.length_cons, List.length_nil] using h
  obtain ⟨s5, hr5', hpc5, hs5_22, hreg5, hp5, hw5, hx8_5⟩ := openRuns_fast_c29_reg (k := 4) (prevVal := bitsOf6 [t6, t7, t8, t9]) hc10 rfl rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.2.2.2.1 (by omega)
    (by have := hbds.2.2.2.1; omega) (by have := hbds.2.2.2.1; omega)
    (by decide)
    (by rw [hpc4]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg4 .x11 (by simp)).trans ((hreg3 .x11 (by simp)).trans ((hreg2 .x11 (by simp)).trans ((hreg1 .x11 (by simp)).trans hregs.rx11)))) hs4_22
    ((hreg4 .x7 (by simp)).trans ((hreg3 .x7 (by simp)).trans ((hreg2 .x7 (by simp)).trans ((hreg1 .x7 (by simp)).trans hregs.rx7)))) hro4 hw4
    (fun hcl => ⟨bitsOf6_lt [t6, t7, t8, t9], hx8_4' hcl⟩)
  rw [div2_ushr_eq g 9 10] at hs5_22
  have hro5 := ReadOnlyPreserved.of_proofWrite hro4 hp5
  have hx8_5' : CleanTrapdoor trapdoor → s5.getReg .x8 = BitVec.ofNat 64 (bitsOf6 [t6, t7, t8, t9, t10]) := fun hcl => by
    have h := hx8_5 hcl; simp only [show ¬ (4 = 0) by decide, ↓reduceIte] at h
    simpa only [show [t6, t7, t8, t9, t10] = [t6, t7, t8, t9] ++ [t10] from rfl, bitsOf6_snoc, List.length_cons, List.length_nil] using h
  obtain ⟨s6, hr6', hpc6, hs6_22, hreg6, hp6, hw6, hx8_6⟩ := openRuns_fast_c29_reg (k := 5) (prevVal := bitsOf6 [t6, t7, t8, t9, t10]) hc11 rfl rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.2.2.2.2.1 (by omega)
    (by have := hbds.2.2.2.2.1; omega) (by have := hbds.2.2.2.2.1; omega)
    (by decide)
    (by rw [hpc5]; simp only [lvlAddrRegCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg5 .x11 (by simp)).trans ((hreg4 .x11 (by simp)).trans ((hreg3 .x11 (by simp)).trans ((hreg2 .x11 (by simp)).trans ((hreg1 .x11 (by simp)).trans hregs.rx11))))) hs5_22
    ((hreg5 .x3 (by simp)).trans ((hreg4 .x3 (by simp)).trans ((hreg3 .x3 (by simp)).trans ((hreg2 .x3 (by simp)).trans ((hreg1 .x3 (by simp)).trans hregs.rx3))))) hro5 hw5
    (fun hcl => ⟨bitsOf6_lt [t6, t7, t8, t9, t10], hx8_5' hcl⟩)
  rw [div2_ushr_eq g 10 11] at hs6_22
  have hlen_eq : (5 + (copy29Code (recL6St r0).1 .x10 (recL6St r0).2.1 .x8 0 true (recL6St r0).2.2 true).length) +
      (5 + (copy29Code (recL7St r0).1 .x10 (recL7St r0).2.1 .x8 6 false (recL7St r0).2.2 true).length) +
      (5 + (copy29Code (recL8St r0).1 .x10 (recL8St r0).2.1 .x8 12 false (recL8St r0).2.2 true).length) +
      (5 + (copy29Code (recL9St r0).1 .x10 (recL9St r0).2.1 .x8 18 false (recL9St r0).2.2 true).length) +
      (5 + (copy29Code (recL10St r0).1 .x10 (recL10St r0).2.1 .x8 24 false (recL10St r0).2.2 true).length) +
      (5 + (copy29Code (recL11St r0).1 .x10 (recL11St r0).2.1 .x8 30 false (recL11St r0).2.2 true).length) =
      (recL6L11Code r0).length := by
    simp only [recL6L11Code, List.length_append, lvlAddrRegCode, List.length_cons, List.length_nil]; omega
  have hr12_eq : copy29NextR (recL11St r0).1 = (recL12St r0).1 ∧
      copy29NextDstOff (recL11St r0).1 (recL11St r0).2.1 = (recL12St r0).2.1 ∧
      copy29NextFlushedR4 (recL11St r0).1 true = (recL12St r0).2.2 := by
    fin_cases r0 <;> decide
  have hw6' : WriterState (CleanTrapdoor trapdoor) s6 (recL12St r0).1 (recL12St r0).2.2 base (recL12St r0).2.1
      (written ++ (bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 10 ((g >>> 9) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29)) := by
    rw [hr12_eq.1, hr12_eq.2.1, hr12_eq.2.2] at hw6
    have hfwd : written ++ bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 10 ((g >>> 9) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29 =
      written ++ (bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++
        bitsToBytes (tdNode trapdoor 10 ((g >>> 9) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29) := by
      simp only [List.append_assoc]
    rw [hfwd] at hw6; exact hw6
  refine ⟨s6, by have htot := ((((hr1'.trans hr2').trans hr3').trans hr4').trans hr5').trans hr6'; rw [hlen_eq] at htot; exact htot,
    by rw [hpc6]; simp only [recL6L11Code, List.length_append, lvlAddrRegCode, List.length_cons, List.length_nil]; apply congrArg pcAt; omega,
    hs6_22,
    fun hcl => by
      have h := hx8_6 hcl; simp only [show ¬ (5 = 0) by decide, ↓reduceIte] at h
      simpa only [show [t6, t7, t8, t9, t10, t11] = [t6, t7, t8, t9, t10] ++ [t11] from rfl,
        bitsOf6_snoc, List.length_cons, List.length_nil, t6, t7, t8, t9, t10, t11, g] using h,
    fun reg hreg => (hreg6 reg hreg).trans ((hreg5 reg hreg).trans ((hreg4 reg hreg).trans ((hreg3 reg hreg).trans ((hreg2 reg hreg).trans (hreg1 reg hreg))))),
    hp1.trans <| hp2.trans <| hp3.trans <| hp4.trans <| hp5.trans hp6,
    hw6'⟩

/-! ### 4. Split Fast/Edge Tail Helpers and Single Record Step (`openRuns_rec_step`) -/

private def l0l11Fwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) (written : List Byte) : List Byte :=
  let g := i.val / 3
  written ++ bitsToBytes (tdSalt trapdoor i) 24 ++
    (bitsToBytes (tdNode trapdoor 0 (l0Sib1Idx i)) 32 ++ bitsToBytes (tdNode trapdoor 0 (l0Sib2Idx i)) 32 ++
     bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32 ++
     bitsToBytes (tdNode trapdoor 2 ((g >>> 1) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 3 ((g >>> 2) ^^^ 1)) 30 ++
     bitsToBytes (tdNode trapdoor 4 ((g >>> 3) ^^^ 1)) 30 ++ bitsToBytes (tdNode trapdoor 5 ((g >>> 4) ^^^ 1)) 30) ++
    (bitsToBytes (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)) 29 ++
     bitsToBytes (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)) 29 ++
     bitsToBytes (tdNode trapdoor 10 ((g >>> 9) ^^^ 1)) 29 ++ bitsToBytes (tdNode trapdoor 11 ((g >>> 10) ^^^ 1)) 29)

private def ts6Of (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) : List (BitVec 6) :=
  let g := i.val / 3
  [tail6 (tdNode trapdoor 6 ((g >>> 5) ^^^ 1)), tail6 (tdNode trapdoor 7 ((g >>> 6) ^^^ 1)),
   tail6 (tdNode trapdoor 8 ((g >>> 7) ^^^ 1)), tail6 (tdNode trapdoor 9 ((g >>> 8) ^^^ 1)),
   tail6 (tdNode trapdoor 10 ((g >>> 9) ^^^ 1)), tail6 (tdNode trapdoor 11 ((g >>> 10) ^^^ 1))]

private theorem pcEdgeGuard_br_ok (r0 : Fin 8) :
    pcEdgeGuard r0 ≤ pcEdge1214 r0 ∧ 4 * (pcEdge1214 r0 - pcEdgeGuard r0) < 4096 := by
  fin_cases r0 <;> (simp only [pcEdgeGuard, recL0L5Code, recL6L11Code, List.length_append]; decide)

private theorem pcFastExit_bne_ok (r0 : Fin 8) :
    (!(r0.val == 3)) = true → pcFastExit r0 + 3 ≤ pcRec (copy29NextR r0) ∧
      4 * (pcRec (copy29NextR r0) - (pcFastExit r0 + 3)) < 4096 := by
  fin_cases r0 <;> (simp only [pcFastExit, pcEdgeGuard, recL0L5Code, recL6L11Code, recFastTailCode, List.length_append]; decide)

/-- Fast 9-tail suffix from `pcEdgeGuard r0` (`idx13 = g >>> 12 < 1364`). -/
private theorem openRuns_rec_fast9 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {tblInit : Bool} {s7 : MachineState}
    (hord : ordinal < positions.card) (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592064)
    (h13_lt : (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 12 < 1364)
    (heg_bd : pcEdgeGuard r0 < OPEN_CODE_LEN)
    (heg2 : openInstr (pcEdgeGuard r0) = .base (.BGEU .x22 .x19 (BitVec.ofNat 13 (4 * (pcEdge1214 r0 - pcEdgeGuard r0)))))
    (hc_ft : CodeAt (pcEdgeGuard r0 + 1) (recFastTailCode r0))
    (hc_fe : CodeAt (pcFastExit r0) (recFastExitCode r0))
    (hs7_pc : s7.pc = pcAt (pcEdgeGuard r0))
    (hregs7 : RecRegs positions ordinal s7)
    (hs7_28 : s7.getReg .x28 = BitVec.ofNat 64 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 11) ^^^ 1))
    (hs7_22 : s7.getReg .x22 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 12))
    (hs7_19 : s7.getReg .x19 = BitVec.ofNat 64 1364)
    (hs7_8 : CleanTrapdoor trapdoor → s7.getReg .x8 = BitVec.ofNat 64 (bitsOf6 (ts6Of trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])))))
    (hro7 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7)
    (hbt7 : BaseTableReady s7)
    (hcm7 : CapMarks15State s7 positions ordinal)
    (htbl7 : SlowTablesState s7 tblInit)
    (hw7 : WriterState (CleanTrapdoor trapdoor) s7 (recL12St r0).1 (recL12St r0).2.2 base (recL12St r0).2.1
            (l0l11Fwd trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) written))
    (ht7 : TailState (CleanTrapdoor trapdoor) s7 tails flushes) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    let cycTail := 1 +
      (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
      (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 true).length) +
      (6 + (copy29Code (recL14St r0).1 .x10 (recL14St r0).2.1 .x8 48 false (recL14St r0).2.2 false).length) +
      5 + (if ordinal + 1 = positions.card then 6 else if !(r0.val == 3) then 4 else 5)
    ∃ sEnd : MachineState,
      OpenRuns s7 (cycTail + 4 * fl) (cycTail + 4 * fl) sEnd ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions (copy29NextR r0) (base + copy29NextDstOff r0 472) (written ++ rFwd) (tails ++ rTails) (flushes + fl) sEnd
      else
        RecInv trapdoor positions (ordinal + 1) (copy29NextR r0) (base + copy29NextDstOff r0 472) (written ++ rFwd) (tails ++ rTails) (flushes + fl) tblInit sEnd := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have h1214 := level12_14_of_idx13 g hg
  have hcbds := recC29_bds r0
  have hrec_eq := record_fast_eq (tdNode trapdoor) (tdSalt trapdoor) i hg h13_lt
  have hl12 : ((g >>> 11) ^^^ 1) < levelSize 12 := h1214.1.mpr (by omega)
  have hl14 : ((g >>> 13) ^^^ 1) < levelSize 14 := h1214.2.mpr h13_lt
  have hlt13 : (s7.getReg .x22).toNat < (s7.getReg .x19).toNat := by
    rw [hs7_22, hs7_19, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Nat.shiftRight_eq_div_pow]; omega : g >>> 12 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1364 < 2 ^ 64)]; omega
  have hg2 := step_BGEU_not_taken (s := s7) heg_bd hs7_pc heg2 hlt13
  set s8 := s7.setPC (pcAt (pcEdgeGuard r0 + 1))
  have hft' : CodeAt (pcEdgeGuard r0 + 1) ((l12RestAddrCode ++ copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true) ++
      ((lvlAddrMemCode .x10 13 ++ copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 true) ++
      ((lvlAddrMemCode .x10 14 ++ copy29Code (recL14St r0).1 .x10 (recL14St r0).2.1 .x8 48 false (recL14St r0).2.2 false) ++
      tailMergeCode 54))) := by
    simpa only [recFastTailCode, List.append_assoc] using hc_ft
  have hc12 := hft'.left; have hrT1 := hft'.right
  have hc13 := hrT1.left; have hrT2 := hrT1.right
  have hc14 := hrT2.left; have hcTM := hrT2.right
  set ts6 := ts6Of trapdoor i
  obtain ⟨s9, hr9, hpc9, hreg9, hp9, hw9, hx8_9⟩ := openRuns_fast_l12 (prevVal := bitsOf6 ts6) hc12
    (by simp [Nat.shiftRight_eq_div_pow]; omega) hl12
    (by have := hcbds.2.2.2.2.2.1; omega) (by have := hcbds.2.2.2.2.2.1; omega)
    (rfl : s8.pc = pcAt (pcEdgeGuard r0 + 1)) (by simpa [s8] using hregs7.rx11)
    (by simpa [s8, show (g >>> 11) / 2 = g >>> 12 from div2_ushr_eq g 11 12] using hs7_22) (by simpa [s8] using hs7_28)
    (fun a ha => (by simp [s8] : s8.getMem a = s7.getMem a).trans (hro7 a ha))
    (baseTableReady_of_lowEq hbt7 (fun _ _ => by simp [s8]))
    (writerState_of_mem_eq hw7 (fun _ => by simp [s8]) (by simp [s8]) (by simp [s8]))
    (fun hcl => ⟨by have h := bitsOf6_lt ts6; rw [show ts6.length = 6 from rfl] at h; exact h, by simpa [s8] using hs7_8 hcl⟩)
  have h13s := recL13_step_eq r0
  rw [h13s.1, h13s.2.1, h13s.2.2] at hw9
  have hro9 := ReadOnlyPreserved.of_proofWrite (fun a ha => (by simp [s8] : s8.getMem a = s7.getMem a).trans (hro7 a ha)) hp9
  have hbt9 := baseTableReady_of_lowEq hbt7 (fun a ha => (hp9 a (by omega)).trans (by simp [s8]))
  set ts7 := ts6 ++ [tail6 (tdNode trapdoor 12 ((g >>> 11) ^^^ 1))]
  have hx8_9' : CleanTrapdoor trapdoor → s9.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts7) := fun hcl => by
    simpa only [ts7, bitsOf6_snoc, show ts6.length = 6 from rfl] using hx8_9 hcl
  obtain ⟨s10, hr10, hpc10, hs10_22, hreg10, hp10, hw10, hx8_10⟩ := openRuns_fast_c29_mem (k := 7) (prevVal := bitsOf6 ts7) hc13 rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    (by have := hcbds.2.2.2.2.2.2.1; omega) (by have := hcbds.2.2.2.2.2.2.1; omega)
    (by rw [hpc9]; simp only [l12RestAddrCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg9 .x11 (by simp)).trans (by simpa [s8] using hregs7.rx11))
    ((hreg9 .x22 (by simp)).trans (by simpa [s8] using hs7_22)) hro9 hbt9 hw9
    (fun hcl => ⟨by have h := bitsOf6_lt ts7; rw [show ts7.length = 7 by simp [ts7, ts6, ts6Of]] at h; exact h, hx8_9' hcl⟩)
  rw [div2_ushr_eq g 12 13] at hs10_22
  have h14s := recL14_step_eq r0
  rw [h14s.1, h14s.2.1, h14s.2.2] at hw10
  have hro10 := ReadOnlyPreserved.of_proofWrite hro9 hp10
  have hbt10 := baseTableReady_of_lowEq hbt9 (fun a ha => hp10 a (by omega))
  set ts8 := ts7 ++ [tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))]
  have hx8_10' : CleanTrapdoor trapdoor → s10.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts8) := fun hcl => by
    simpa only [ts8, bitsOf6_snoc, show ts7.length = 7 by simp [ts7, ts6, ts6Of]] using hx8_10 hcl
  obtain ⟨s11, hr11, hpc11, hs11_22, hreg11, hp11, hw11, hx8_11⟩ := openRuns_fast_c29_mem (k := 8) (prevVal := bitsOf6 ts8) hc14 rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hl14 (by omega) (by omega)
    (by rw [(recL14_st_eq r0).2]; omega) (by rw [(recL14_st_eq r0).2]; omega)
    (by rw [hpc10]; simp only [lvlAddrMemCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg10 .x11 (by simp)).trans ((hreg9 .x11 (by simp)).trans (by simpa [s8] using hregs7.rx11)))
    hs10_22 hro10 hbt10 hw10
    (fun hcl => ⟨by have h := bitsOf6_lt ts8; rw [show ts8.length = 8 by simp [ts8, ts7, ts6, ts6Of]] at h; exact h, hx8_10' hcl⟩)
  rw [div2_ushr_eq g 13 14] at hs11_22
  have h14e := recL14_st_eq r0
  rw [h14e.1, h14e.2, copy29NextFlushedR4, Bool.and_false] at hw11
  set ts9 := ts8 ++ [tail6 (tdNode trapdoor 14 ((g >>> 13) ^^^ 1))]
  have hts9_eq : ts9 = recordTails (tdNode trapdoor) i := by
    rw [hrec_eq.2]; simp only [ts9, ts8, ts7, ts6, ts6Of, List.cons_append, List.nil_append, g]
  have hx8_11' : CleanTrapdoor trapdoor → s11.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts9) := fun hcl => by
    simpa only [ts9, bitsOf6_snoc, show ts8.length = 8 by simp [ts8, ts7, ts6, ts6Of]] using hx8_11 hcl
  have hp11_7 : ProofWritePreserves s7 s11 := ProofWritePreserves.trans (fun a _ => by simp [s8]) <| hp9.trans <| hp10.trans hp11
  have hreg11_7 : RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x22, .x28] s7 s11 := fun reg h => by
    have h5' : reg ≠ .x5 := fun hm => h (by simp [hm])
    have h6' : reg ≠ .x6 := fun hm => h (by simp [hm])
    have h8' : reg ≠ .x8 := fun hm => h (by simp [hm])
    have h10' : reg ≠ .x10 := fun hm => h (by simp [hm])
    have h12' : reg ≠ .x12 := fun hm => h (by simp [hm])
    have h22' : reg ≠ .x22 := fun hm => h (by simp [hm])
    have h28' : reg ≠ .x28 := fun hm => h (by simp [hm])
    exact (hreg11 reg h).trans ((hreg10 reg h).trans ((hreg9 reg (by simp [h5', h6', h8', h10', h12', h28'])).trans (by simp [s8])))
  have ht11 : TailState (CleanTrapdoor trapdoor) s11 tails flushes :=
    TailState.of_proofWrite ht7 hp11_7 (hreg11_7 .x15 (by decide)) (hreg11_7 .x16 (by decide)) (hreg11_7 .x17 (by decide))
  obtain ⟨s12, hr12, hpc12, hreg12, htw12, ht12⟩ := openRuns_tailMerge_neg (ts := ts9)
    (by simp [ts9, ts8, ts7, ts6, ts6Of]) (by simp [ts9, ts8, ts7, ts6, ts6Of]) hcTM
    (by rw [hpc11]; simp only [lvlAddrMemCode, List.length_append, List.length_cons, List.length_nil])
    hx8_11' ht11 hbd_t
  have hpc12_eq : s12.pc = pcAt (pcFastExit r0) := by
    rw [hpc12]; apply congrArg pcAt
    simp only [pcFastExit, recFastTailCode, l12RestAddrCode, lvlAddrMemCode, tailMergeCode,
      List.length_append, List.length_cons, List.length_nil]; omega
  have hc_fe' : CodeAt (pcFastExit r0) (if !(r0.val == 3) then recBneExitCode (pcFastExit r0) (copy29NextDstOff r0 472) (copy29NextR r0)
      else recBeqExitCode (pcFastExit r0) (copy29NextDstOff r0 472) (copy29NextR r0)) := by
    unfold recFastExitCode at hc_fe
    cases h3 : (r0.val == 3) <;> simp only [h3, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hc_fe ⊢ <;> exact hc_fe
  have hro12 := readOnlyPreserved_of_tailWrite (ReadOnlyPreserved.of_proofWrite hro7 hp11_7) htw12
  have hbt12 := baseTableReady_of_lowEq hbt7 (fun a ha => ((tailWrite_pres_low htw12).1 a ha).trans ((proofWrite_pres_low hp11_7).1 a ha))
  have hcm12 := capMarks15State_of_lowEq hcm7 (fun a h1 h2 => ((tailWrite_pres_low htw12).2.1 a h1 h2).trans ((proofWrite_pres_low hp11_7).2.1 a h1 h2))
  have htbl12 := slowTablesState_of_eq htbl7 (fun a h1 h2 => ((tailWrite_pres_low htw12).2.2 a h1 h2).trans ((proofWrite_pres_low hp11_7).2.2 a h1 h2))
  have hregs12 := recRegs_of_eq hregs7 (fun reg h =>
    (hreg12 reg (reg_not_mem_sub (by decide) h)).trans (hreg11_7 reg (reg_not_mem_sub (by decide) h)))
  have hfwd_eq : l0l11Fwd trapdoor i written ++
      bitsToBytes (tdNode trapdoor 12 ((g >>> 11) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 14 ((g >>> 13) ^^^ 1)) 29 =
      written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i := by
    rw [hrec_eq.1]; simp only [l0l11Fwd, List.append_assoc, g]
  have hw12 : WriterState (CleanTrapdoor trapdoor) s12 (copy29NextR r0) false base (copy29NextDstOff r0 472)
      (written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i) := by
    rw [← hfwd_eq]
    exact writerState_of_tailWrite hw11 htw12 (hreg12 .x25 (by simp)) (hreg12 .x12 (by simp))
  have ht12' : TailState (CleanTrapdoor trapdoor) s12 (tails ++ recordTails (tdNode trapdoor) i)
      (flushes + if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
    rw [← hts9_eq]; exact ht12
  have hbne_ok := pcFastExit_bne_ok r0
  obtain ⟨sEnd, hrEnd, hpost⟩ := openRuns_rec_exit (useBne := !(r0.val == 3)) hord hcbds.2.2.2.2.2.2.2.2.2.2.1
    hcbds.2.2.2.2.2.2.2.2.2.2.2 hc_fe' hbne_ok hpc12_eq hregs12
    (by have h := (hreg12 .x22 (by simp)).trans hs11_22; rw [capLeafOf_eq_div16384]; exact h)
    hro12 hbt12 hcm12 htbl12 hw12 ht12'
  have htot := ((((hg2.trans hr9).trans hr10).trans hr11).trans hr12).trans hrEnd
  have heq_c : 1 + (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
      (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 true).length) +
      (6 + (copy29Code (recL14St r0).1 .x10 (recL14St r0).2.1 .x8 48 false (recL14St r0).2.2 false).length) +
      (5 + 4 * if 6 * tails.length % 64 + 6 * ts9.length < 64 then 0 else 1) +
      (if ordinal + 1 = positions.card then 6 else if !(r0.val == 3) then 4 else 5) =
      (1 + (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
        (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 true).length) +
        (6 + (copy29Code (recL14St r0).1 .x10 (recL14St r0).2.1 .x8 48 false (recL14St r0).2.2 false).length) +
        5 + (if ordinal + 1 = positions.card then 6 else if !(r0.val == 3) then 4 else 5)) +
      4 * if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1 := by
    rw [hts9_eq]; omega
  rw [heq_c] at htot
  exact ⟨sEnd, htot, hpost⟩

/-- Edge `skip14` 8-tail suffix from `pcEdgeGuard r0` (`idx13 = g >>> 12 = 1364`). -/
private theorem openRuns_rec_skip14 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {tblInit : Bool} {s7 : MachineState}
    (hord : ordinal < positions.card) (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592064)
    (h13_eq : (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 12 = 1364)
    (heg_bd : pcEdgeGuard r0 < OPEN_CODE_LEN)
    (heg2 : openInstr (pcEdgeGuard r0) = .base (.BGEU .x22 .x19 (BitVec.ofNat 13 (4 * (pcEdge1214 r0 - pcEdgeGuard r0)))))
    (hc_edge : CodeAt (pcEdge1214 r0) (recEdgeBodyCode r0 ++ recBeqExitCode (pcS14Exit r0) 472 r0))
    (hs7_pc : s7.pc = pcAt (pcEdgeGuard r0))
    (hregs7 : RecRegs positions ordinal s7)
    (hs7_28 : s7.getReg .x28 = BitVec.ofNat 64 (((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 11) ^^^ 1))
    (hs7_22 : s7.getReg .x22 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 12))
    (hs7_19 : s7.getReg .x19 = BitVec.ofNat 64 1364)
    (hs7_8 : CleanTrapdoor trapdoor → s7.getReg .x8 = BitVec.ofNat 64 (bitsOf6 (ts6Of trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])))))
    (hro7 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7)
    (hbt7 : BaseTableReady s7)
    (hcm7 : CapMarks15State s7 positions ordinal)
    (htbl7 : SlowTablesState s7 tblInit)
    (hw7 : WriterState (CleanTrapdoor trapdoor) s7 (recL12St r0).1 (recL12St r0).2.2 base (recL12St r0).2.1
            (l0l11Fwd trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) written))
    (ht7 : TailState (CleanTrapdoor trapdoor) s7 tails flushes) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    let cycTail := 1 + 1 +
      (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
      (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 false).length) +
      1 + 5 + (if ordinal + 1 = positions.card then 6 else 5)
    ∃ sEnd : MachineState,
      OpenRuns s7 (cycTail + 4 * fl) (cycTail + 4 * fl) sEnd ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions r0 (base + 472) (written ++ rFwd) (tails ++ rTails) (flushes + fl) sEnd
      else
        RecInv trapdoor positions (ordinal + 1) r0 (base + 472) (written ++ rFwd) (tails ++ rTails) (flushes + fl) tblInit sEnd := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have h1214 := level12_14_of_idx13 g hg
  have hcbds := recC29_bds r0
  have hrec_eq := record_skip14_eq (tdNode trapdoor) (tdSalt trapdoor) i hg h13_eq
  have hl12 : ((g >>> 11) ^^^ 1) < levelSize 12 := h1214.1.mpr (by omega)
  have hge13 : (s7.getReg .x19).toNat ≤ (s7.getReg .x22).toNat := by
    rw [hs7_22, hs7_19, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Nat.shiftRight_eq_div_pow]; omega : g >>> 12 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1364 < 2 ^ 64)]; omega
  have heg_br_ok := pcEdgeGuard_br_ok r0
  have hg2 := step_BGEU_taken (s := s7) heg_bd hs7_pc heg2 hge13 (pcAt_add_pos13 _ _ heg_br_ok.1 heg_br_ok.2)
  set s8 := s7.setPC (pcAt (pcEdge1214 r0))
  have hedge' : CodeAt (pcEdge1214 r0) ([.base (.BNE .x22 .x19 (BitVec.ofNat 13 (4 * (pcSkip1214 r0 - pcEdge1214 r0))))] ++
      ((l12RestAddrCode ++ copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true) ++
      ((lvlAddrMemCode .x10 13 ++ copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 false) ++
      ([.base (.SRLI .x22 .x22 (1#6))] ++ (tailMergeCode 48 ++ recBeqExitCode (pcS14Exit r0) 472 r0))))) := by
    simpa only [recEdgeBodyCode, List.append_assoc] using hc_edge
  have hc_bne := hedge'.left; have hrE1 := hedge'.right
  have hc_e12 := hrE1.left; have hrE2 := hrE1.right
  have hc_e13 := hrE2.left; have hrE3 := hrE2.right
  have hc_esr := hrE3.left; have hrE4 := hrE3.right
  have hc_etm := hrE4.left; have hc_eex := hrE4.right
  have hbne_ins : openInstr (pcEdge1214 r0) = .base (.BNE .x22 .x19 (BitVec.ofNat 13 (4 * (pcSkip1214 r0 - pcEdge1214 r0)))) := by
    have h := hc_bne.2 0 (by simp); simpa using h
  have hedge_bd : pcEdge1214 r0 < OPEN_CODE_LEN := by fin_cases r0 <;> decide
  have h8_eq : s8.getReg .x22 = s8.getReg .x19 := by simp [s8, hs7_22, hs7_19, h13_eq]
  have hbne := step_BNE_not_taken (s := s8) hedge_bd rfl hbne_ins h8_eq
  set s8a := s8.setPC (pcAt (pcEdge1214 r0 + 1))
  set ts6 := ts6Of trapdoor i
  obtain ⟨s9, hr9, hpc9, hreg9, hp9, hw9, hx8_9⟩ := openRuns_fast_l12 (prevVal := bitsOf6 ts6) hc_e12
    (by simp [Nat.shiftRight_eq_div_pow]; omega) hl12
    (by have := hcbds.2.2.2.2.2.1; omega) (by have := hcbds.2.2.2.2.2.1; omega)
    (rfl : s8a.pc = pcAt (pcEdge1214 r0 + 1)) (by simpa [s8a, s8] using hregs7.rx11)
    (by simpa [s8a, s8, show (g >>> 11) / 2 = g >>> 12 from div2_ushr_eq g 11 12] using hs7_22) (by simpa [s8a, s8] using hs7_28)
    (fun a ha => (by simp [s8a, s8] : s8a.getMem a = s7.getMem a).trans (hro7 a ha))
    (baseTableReady_of_lowEq hbt7 (fun _ _ => by simp [s8a, s8]))
    (writerState_of_mem_eq hw7 (fun _ => by simp [s8a, s8]) (by simp [s8a, s8]) (by simp [s8a, s8]))
    (fun hcl => ⟨by have h := bitsOf6_lt ts6; rw [show ts6.length = 6 from rfl] at h; exact h, by simpa [s8a, s8] using hs7_8 hcl⟩)
  have h13s := recL13_step_eq r0
  rw [h13s.1, h13s.2.1, h13s.2.2] at hw9
  have hro9 := ReadOnlyPreserved.of_proofWrite (fun a ha => (by simp [s8a, s8] : s8a.getMem a = s7.getMem a).trans (hro7 a ha)) hp9
  have hbt9 := baseTableReady_of_lowEq hbt7 (fun a ha => (hp9 a (by omega)).trans (by simp [s8a, s8]))
  set ts7 := ts6 ++ [tail6 (tdNode trapdoor 12 ((g >>> 11) ^^^ 1))]
  have hx8_9' : CleanTrapdoor trapdoor → s9.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts7) := fun hcl => by
    simpa only [ts7, bitsOf6_snoc, show ts6.length = 6 from rfl] using hx8_9 hcl
  obtain ⟨s10, hr10, hpc10, hs10_22, hreg10, hp10, hw10, hx8_10⟩ := openRuns_fast_c29_mem (k := 7) (prevVal := bitsOf6 ts7) hc_e13 rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    (by have := hcbds.2.2.2.2.2.2.1; omega) (by have := hcbds.2.2.2.2.2.2.1; omega)
    (by rw [hpc9]; simp only [l12RestAddrCode, List.length_append, List.length_cons, List.length_nil])
    ((hreg9 .x11 (by simp)).trans (by simpa [s8a, s8] using hregs7.rx11))
    ((hreg9 .x22 (by simp)).trans (by simpa [s8a, s8] using hs7_22)) hro9 hbt9 hw9
    (fun hcl => ⟨by have h := bitsOf6_lt ts7; rw [show ts7.length = 7 by simp [ts7, ts6, ts6Of]] at h; exact h, hx8_9' hcl⟩)
  rw [div2_ushr_eq g 12 13] at hs10_22
  set ts8 := ts7 ++ [tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))]
  have hts8_eq : ts8 = recordTails (tdNode trapdoor) i := by
    rw [hrec_eq.2]; simp only [ts8, ts7, ts6, ts6Of, List.cons_append, List.nil_append, g]
  have hx8_10' : CleanTrapdoor trapdoor → s10.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts8) := fun hcl => by
    simpa only [ts8, bitsOf6_snoc, show ts7.length = 7 by simp [ts7, ts6, ts6Of]] using hx8_10 hcl
  set pcSr := pcEdge1214 r0 + 1 + (l12RestAddrCode ++ copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length +
      (lvlAddrMemCode .x10 13 ++ copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 false).length
  have hsr_ins : openInstr pcSr = .base (.SRLI .x22 .x22 (1#6)) := by
    have h := hc_esr.2 0 (by simp)
    simpa only [pcSr, List.length_cons, List.length_nil, List.getElem_cons_zero, Nat.add_zero] using h
  have hsr := step_SRLI (s := s10) (by have := hc_esr.1; simp only [List.length_cons, List.length_nil] at this; unfold pcSr; omega)
    (by rw [hpc10]; simp only [pcSr, lvlAddrMemCode, List.length_append, List.length_cons, List.length_nil])
    hsr_ins
  set s11 := (s10.setReg .x22 (s10.getReg .x22 >>> (1#6).toNat)).setPC (pcAt (pcSr + 1))
  have hs11_22 : s11.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) := by
    simp only [s11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hs10_22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 13) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega), capLeafOf_eq_div16384]
    rw [show (g >>> 13) >>> 1 = g >>> 14 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hp11_7 : ProofWritePreserves s7 s11 := ProofWritePreserves.trans (fun a _ => by simp [s8a, s8]) <| hp9.trans <| hp10.trans (fun _ _ => by simp [s11])
  have hreg11_7 : RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x22, .x28] s7 s11 := fun reg h => by
    have h5' : reg ≠ .x5 := fun hm => h (by simp [hm])
    have h6' : reg ≠ .x6 := fun hm => h (by simp [hm])
    have h8' : reg ≠ .x8 := fun hm => h (by simp [hm])
    have h10' : reg ≠ .x10 := fun hm => h (by simp [hm])
    have h12' : reg ≠ .x12 := fun hm => h (by simp [hm])
    have h22' : reg ≠ .x22 := fun hm => h (by simp [hm])
    have h28' : reg ≠ .x28 := fun hm => h (by simp [hm])
    exact (by simp [s11, getReg_setReg_ne' .x22 reg h22'.symm] : s11.getReg reg = s10.getReg reg).trans
      ((hreg10 reg h).trans ((hreg9 reg (by simp [h5', h6', h8', h10', h12', h28'])).trans (by simp [s8a, s8])))
  have ht11 : TailState (CleanTrapdoor trapdoor) s11 tails flushes :=
    TailState.of_proofWrite ht7 hp11_7 (hreg11_7 .x15 (by decide)) (hreg11_7 .x16 (by decide)) (hreg11_7 .x17 (by decide))
  obtain ⟨s12, hr12, hpc12, hreg12, htw12, ht12⟩ := openRuns_tailMerge_neg (ts := ts8)
    (by simp [ts8, ts7, ts6, ts6Of]) (by simp [ts8, ts7, ts6, ts6Of]) hc_etm
    (by dsimp only [s11, MachineState.setPC]; apply congrArg pcAt; simp only [pcSr, List.length_cons, List.length_nil])
    (fun hcl => by simp [s11, getReg_setReg_ne', hx8_10' hcl]) ht11 hbd_t
  have hpc12_eq : s12.pc = pcAt (pcS14Exit r0) := by
    rw [hpc12]; apply congrArg pcAt
    simp only [pcS14Exit, recEdgeBodyCode, l12RestAddrCode, lvlAddrMemCode, tailMergeCode,
      List.length_append, List.length_cons, List.length_nil]; omega
  have hc_eex' : CodeAt (pcS14Exit r0) (recBeqExitCode (pcS14Exit r0) 472 r0) := by
    simpa only [pcS14Exit, recEdgeBodyCode, l12RestAddrCode, lvlAddrMemCode, tailMergeCode,
      List.length_append, List.length_cons, List.length_nil, Nat.add_assoc] using hc_eex
  have hro12 := readOnlyPreserved_of_tailWrite (ReadOnlyPreserved.of_proofWrite hro7 hp11_7) htw12
  have hbt12 := baseTableReady_of_lowEq hbt7 (fun a ha => ((tailWrite_pres_low htw12).1 a ha).trans ((proofWrite_pres_low hp11_7).1 a ha))
  have hcm12 := capMarks15State_of_lowEq hcm7 (fun a h1 h2 => ((tailWrite_pres_low htw12).2.1 a h1 h2).trans ((proofWrite_pres_low hp11_7).2.1 a h1 h2))
  have htbl12 := slowTablesState_of_eq htbl7 (fun a h1 h2 => ((tailWrite_pres_low htw12).2.2 a h1 h2).trans ((proofWrite_pres_low hp11_7).2.2 a h1 h2))
  have hregs12 := recRegs_of_eq hregs7 (fun reg h =>
    (hreg12 reg (reg_not_mem_sub (by decide) h)).trans (hreg11_7 reg (reg_not_mem_sub (by decide) h)))
  have hfwd_eq : l0l11Fwd trapdoor i written ++
      bitsToBytes (tdNode trapdoor 12 ((g >>> 11) ^^^ 1)) 29 ++
      bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29 =
      written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i := by
    rw [hrec_eq.1]; simp only [l0l11Fwd, List.append_assoc, g]
  have hw12 : WriterState (CleanTrapdoor trapdoor) s12 r0 false base 472 (written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i) := by
    rw [← hfwd_eq]
    have hw10' : WriterState (CleanTrapdoor trapdoor) s10 r0 false base 472
        (l0l11Fwd trapdoor i written ++ bitsToBytes (tdNode trapdoor 12 ((g >>> 11) ^^^ 1)) 29 ++
         bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29) := by
      have h14 := recL14_st_eq r0
      simp only [recL14St, c29Step, copy29NextFlushedR4] at h14
      simpa only [h14.1, h14.2, copy29NextFlushedR4, Bool.and_false] using hw10
    have hw11' := writerState_of_mem_eq hw10' (s' := s11) (fun _ => by simp [s11]) (by simp [s11, getReg_setReg_ne']) (by simp [s11, getReg_setReg_ne'])
    exact writerState_of_tailWrite hw11' htw12 (hreg12 .x25 (by simp)) (hreg12 .x12 (by simp))
  have ht12' : TailState (CleanTrapdoor trapdoor) s12 (tails ++ recordTails (tdNode trapdoor) i)
      (flushes + if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
    rw [← hts8_eq]; exact ht12
  obtain ⟨sEnd, hrEnd, hpost⟩ := openRuns_rec_exit (useBne := false) hord (by omega) (by omega)
    hc_eex' (fun h => absurd h (by decide)) hpc12_eq hregs12
    ((hreg12 .x22 (by simp)).trans hs11_22) hro12 hbt12 hcm12 htbl12 hw12 ht12'
  simp only [Bool.false_eq_true, ↓reduceIte] at hrEnd
  have htot := (((((hg2.trans hbne).trans hr9).trans hr10).trans hsr).trans hr12).trans hrEnd
  have heq_c : 1 + 1 + (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
      (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 false).length) + 1 +
      (5 + 4 * if 6 * tails.length % 64 + 6 * ts8.length < 64 then 0 else 1) +
      (if ordinal + 1 = positions.card then 6 else 5) =
      (1 + 1 + (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
        (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 false).length) +
        1 + 5 + (if ordinal + 1 = positions.card then 6 else 5)) +
      4 * if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1 := by
    rw [hts8_eq]; omega
  rw [heq_c] at htot
  exact ⟨sEnd, htot, hpost⟩

/-- Edge `skip12+14` 7-tail suffix from `pcEdgeGuard r0` (`idx13 = g >>> 12 = 1365`). -/
private theorem openRuns_rec_skip1214 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {tblInit : Bool} {s7 : MachineState}
    (hord : ordinal < positions.card) (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hg : ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3 < 5592064)
    (h13_1365 : (((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 12 = 1365)
    (heg_bd : pcEdgeGuard r0 < OPEN_CODE_LEN)
    (heg2 : openInstr (pcEdgeGuard r0) = .base (.BGEU .x22 .x19 (BitVec.ofNat 13 (4 * (pcEdge1214 r0 - pcEdgeGuard r0)))))
    (hc_edge : CodeAt (pcEdge1214 r0) (recEdgeBodyCode r0 ++ recBeqExitCode (pcS14Exit r0) 472 r0))
    (hc_skip : CodeAt (pcSkip1214 r0) (recSkipBodyCode r0 ++ recBeqExitCode (pcS1214Exit r0)
      (copy29NextDstOff (recL12St r0).1 (recL12St r0).2.1) (copy29NextR (recL12St r0).1)))
    (hs7_pc : s7.pc = pcAt (pcEdgeGuard r0))
    (hregs7 : RecRegs positions ordinal s7)
    (hs7_22 : s7.getReg .x22 = BitVec.ofNat 64 ((((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])).val / 3) >>> 12))
    (hs7_19 : s7.getReg .x19 = BitVec.ofNat 64 1364)
    (hs7_8 : CleanTrapdoor trapdoor → s7.getReg .x8 = BitVec.ofNat 64 (bitsOf6 (ts6Of trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])))))
    (hro7 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7)
    (hbt7 : BaseTableReady s7)
    (hcm7 : CapMarks15State s7 positions ordinal)
    (htbl7 : SlowTablesState s7 tblInit)
    (hw7 : WriterState (CleanTrapdoor trapdoor) s7 (recL12St r0).1 (recL12St r0).2.2 base (recL12St r0).2.1
            (l0l11Fwd trapdoor ((positions.sort (· ≤ ·))[ordinal]'(by simp [hord])) written))
    (ht7 : TailState (CleanTrapdoor trapdoor) s7 tails flushes) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    let rEnd := copy29NextR (recL12St r0).1
    let dstEnd := copy29NextDstOff (recL12St r0).1 (recL12St r0).2.1
    let cycTail := 1 + 1 +
      (6 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 false).length) +
      1 + 5 + (if ordinal + 1 = positions.card then 6 else 5)
    ∃ sEnd : MachineState,
      OpenRuns s7 (cycTail + 4 * fl) (cycTail + 4 * fl) sEnd ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd (base + dstEnd) (written ++ rFwd) (tails ++ rTails) (flushes + fl) sEnd
      else
        RecInv trapdoor positions (ordinal + 1) rEnd (base + dstEnd) (written ++ rFwd) (tails ++ rTails) (flushes + fl) tblInit sEnd := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hf := level_sib_lt_of_fast g hg
  have hcbds := recC29_bds r0
  have hrec_eq := record_skip1214_eq (tdNode trapdoor) (tdSalt trapdoor) i hg h13_1365
  have hge13 : (s7.getReg .x19).toNat ≤ (s7.getReg .x22).toNat := by
    rw [hs7_22, hs7_19, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Nat.shiftRight_eq_div_pow]; omega : g >>> 12 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 1364 < 2 ^ 64)]; omega
  have heg_br_ok := pcEdgeGuard_br_ok r0
  have hg2 := step_BGEU_taken (s := s7) heg_bd hs7_pc heg2 hge13 (pcAt_add_pos13 _ _ heg_br_ok.1 heg_br_ok.2)
  set s8 := s7.setPC (pcAt (pcEdge1214 r0))
  have hbne_ins : openInstr (pcEdge1214 r0) = .base (.BNE .x22 .x19 (BitVec.ofNat 13 (4 * (pcSkip1214 r0 - pcEdge1214 r0)))) := by
    have h := hc_edge.2 0 (by simp [recEdgeBodyCode])
    simpa only [recEdgeBodyCode, List.cons_append, List.getElem_cons_zero, Nat.add_zero] using h
  have hedge_bd : pcEdge1214 r0 < OPEN_CODE_LEN := by fin_cases r0 <;> decide
  have h8_ne : s8.getReg .x22 ≠ s8.getReg .x19 := by
    simp only [s8, MachineState.getReg_setPC, hs7_22, hs7_19, h13_1365]; decide
  have hsk_ok : pcEdge1214 r0 ≤ pcSkip1214 r0 ∧ 4 * (pcSkip1214 r0 - pcEdge1214 r0) < 4096 := by fin_cases r0 <;> decide
  have hbne := step_BNE_taken (s := s8) hedge_bd rfl hbne_ins h8_ne (pcAt_add_pos13 _ _ hsk_ok.1 hsk_ok.2)
  set s8a := s8.setPC (pcAt (pcSkip1214 r0))
  have hskip' : CodeAt (pcSkip1214 r0) ((lvlAddrMemCode .x10 13 ++ copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 false) ++
      ([.base (.SRLI .x22 .x22 (1#6))] ++ (tailMergeCode 42 ++
      recBeqExitCode (pcS1214Exit r0) (copy29NextDstOff (recL12St r0).1 (recL12St r0).2.1) (copy29NextR (recL12St r0).1)))) := by
    simpa only [recSkipBodyCode, List.append_assoc] using hc_skip
  have hc_s13 := hskip'.left; have hrS1 := hskip'.right
  have hc_ssr := hrS1.left; have hrS2 := hrS1.right
  have hc_stm := hrS2.left; have hc_sex := hrS2.right
  set ts6 := ts6Of trapdoor i
  obtain ⟨s10, hr10, hpc10, hs10_22, hreg10, hp10, hw10, hx8_10⟩ := openRuns_fast_c29_mem (k := 6) (prevVal := bitsOf6 ts6) hc_s13 rfl
    (by omega) (by omega) (by simp [Nat.shiftRight_eq_div_pow]; omega) hf.2.2.2.2.2.2.2.2.2.2.2.1 (by omega) (by omega)
    (by have := hcbds.2.2.2.2.2.1; omega) (by have := hcbds.2.2.2.2.2.1; omega)
    (rfl : s8a.pc = pcAt (pcSkip1214 r0)) (by simpa [s8a, s8] using hregs7.rx11)
    (by simpa [s8a, s8] using hs7_22)
    (fun a ha => (by simp [s8a, s8] : s8a.getMem a = s7.getMem a).trans (hro7 a ha))
    (baseTableReady_of_lowEq hbt7 (fun _ _ => by simp [s8a, s8]))
    (writerState_of_mem_eq hw7 (fun _ => by simp [s8a, s8]) (by simp [s8a, s8]) (by simp [s8a, s8]))
    (fun hcl => ⟨by have h := bitsOf6_lt ts6; rw [show ts6.length = 6 from rfl] at h; exact h, by simpa [s8a, s8] using hs7_8 hcl⟩)
  rw [div2_ushr_eq g 12 13] at hs10_22
  set ts7 := ts6 ++ [tail6 (tdNode trapdoor 13 ((g >>> 12) ^^^ 1))]
  have hts7_eq : ts7 = recordTails (tdNode trapdoor) i := by
    rw [hrec_eq.2]; simp only [ts7, ts6, ts6Of, List.cons_append, List.nil_append, g]
  have hx8_10' : CleanTrapdoor trapdoor → s10.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts7) := fun hcl => by
    simpa only [ts7, bitsOf6_snoc, show ts6.length = 6 from rfl] using hx8_10 hcl
  set pcSr := pcSkip1214 r0 + (lvlAddrMemCode .x10 13 ++ copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 false).length
  have hsr_ins : openInstr pcSr = .base (.SRLI .x22 .x22 (1#6)) := by
    have h := hc_ssr.2 0 (by simp)
    simpa only [pcSr, List.getElem_cons_zero, Nat.add_zero] using h
  have hsr := step_SRLI (s := s10) (by have := hc_ssr.1; simp at this; omega)
    (by rw [hpc10]; simp only [pcSr, lvlAddrMemCode, List.length_append, List.length_cons, List.length_nil])
    hsr_ins
  set s11 := (s10.setReg .x22 (s10.getReg .x22 >>> (1#6).toNat)).setPC (pcAt (pcSr + 1))
  have hs11_22 : s11.getReg .x22 = BitVec.ofNat 64 (capLeafOf i) := by
    simp only [s11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      hs10_22, show (1#6 : BitVec 6).toNat = 1 from rfl, bv64_ushr (g >>> 13) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega), capLeafOf_eq_div16384]
    rw [show (g >>> 13) >>> 1 = g >>> 14 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]]
  have hp11_7 : ProofWritePreserves s7 s11 := ProofWritePreserves.trans (fun a _ => by simp [s8a, s8]) <| hp10.trans (fun _ _ => by simp [s11])
  have hreg11_7 : RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x22, .x28] s7 s11 := fun reg h => by
    have h22' : reg ≠ .x22 := fun hm => h (by simp [hm])
    exact (by simp [s11, getReg_setReg_ne' .x22 reg h22'.symm] : s11.getReg reg = s10.getReg reg).trans
      ((hreg10 reg h).trans (by simp [s8a, s8]))
  have ht11 : TailState (CleanTrapdoor trapdoor) s11 tails flushes :=
    TailState.of_proofWrite ht7 hp11_7 (hreg11_7 .x15 (by decide)) (hreg11_7 .x16 (by decide)) (hreg11_7 .x17 (by decide))
  obtain ⟨s12, hr12, hpc12, hreg12, htw12, ht12⟩ := openRuns_tailMerge_neg (ts := ts7)
    (by simp [ts7, ts6, ts6Of]) (by simp [ts7, ts6, ts6Of]) hc_stm
    (by dsimp only [s11, MachineState.setPC]; apply congrArg pcAt; simp only [pcSr, List.length_cons, List.length_nil])
    (fun hcl => by simp [s11, getReg_setReg_ne', hx8_10' hcl]) ht11 hbd_t
  have hpc12_eq : s12.pc = pcAt (pcS1214Exit r0) := by
    rw [hpc12]; apply congrArg pcAt
    simp only [pcSr, pcS1214Exit, recSkipBodyCode, lvlAddrMemCode, tailMergeCode,
      List.length_append, List.length_cons, List.length_nil]; omega
  have hc_sex' : CodeAt (pcS1214Exit r0) (recBeqExitCode (pcS1214Exit r0)
      (copy29NextDstOff (recL12St r0).1 (recL12St r0).2.1) (copy29NextR (recL12St r0).1)) := by
    have hpc_sex : pcSkip1214 r0 + (lvlAddrMemCode .x10 13 ++ copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 false).length +
        ([.base (.SRLI .x22 .x22 (1#6))] : List Instruction).length + (tailMergeCode 42).length = pcS1214Exit r0 := by
      simp only [pcS1214Exit, recSkipBodyCode, List.length_append, List.length_cons, List.length_nil]; omega
    rw [hpc_sex] at hc_sex; exact hc_sex
  have hro12 := readOnlyPreserved_of_tailWrite (ReadOnlyPreserved.of_proofWrite hro7 hp11_7) htw12
  have hbt12 := baseTableReady_of_lowEq hbt7 (fun a ha => ((tailWrite_pres_low htw12).1 a ha).trans ((proofWrite_pres_low hp11_7).1 a ha))
  have hcm12 := capMarks15State_of_lowEq hcm7 (fun a h1 h2 => ((tailWrite_pres_low htw12).2.1 a h1 h2).trans ((proofWrite_pres_low hp11_7).2.1 a h1 h2))
  have htbl12 := slowTablesState_of_eq htbl7 (fun a h1 h2 => ((tailWrite_pres_low htw12).2.2 a h1 h2).trans ((proofWrite_pres_low hp11_7).2.2 a h1 h2))
  have hregs12 := recRegs_of_eq hregs7 (fun reg h =>
    (hreg12 reg (reg_not_mem_sub (by decide) h)).trans (hreg11_7 reg (reg_not_mem_sub (by decide) h)))
  have hfwd_eq : l0l11Fwd trapdoor i written ++
      bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29 =
      written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i := by
    rw [hrec_eq.1]; simp only [l0l11Fwd, List.append_assoc, g]
  have hw12 : WriterState (CleanTrapdoor trapdoor) s12 (copy29NextR (recL12St r0).1) false base
      (copy29NextDstOff (recL12St r0).1 (recL12St r0).2.1) (written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i) := by
    rw [← hfwd_eq]
    have hw10' : WriterState (CleanTrapdoor trapdoor) s10 (copy29NextR (recL12St r0).1) false base
        (copy29NextDstOff (recL12St r0).1 (recL12St r0).2.1)
        (l0l11Fwd trapdoor i written ++ bitsToBytes (tdNode trapdoor 13 ((g >>> 12) ^^^ 1)) 29) := by
      simpa only [copy29NextFlushedR4, Bool.and_false] using hw10
    have hw11' := writerState_of_mem_eq hw10' (s' := s11) (fun _ => by simp [s11]) (by simp [s11, getReg_setReg_ne']) (by simp [s11, getReg_setReg_ne'])
    exact writerState_of_tailWrite hw11' htw12 (hreg12 .x25 (by simp)) (hreg12 .x12 (by simp))
  have ht12' : TailState (CleanTrapdoor trapdoor) s12 (tails ++ recordTails (tdNode trapdoor) i)
      (flushes + if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1) := by
    rw [← hts7_eq]; exact ht12
  obtain ⟨sEnd, hrEnd, hpost⟩ := openRuns_rec_exit (useBne := false) hord
    hcbds.2.2.2.2.2.2.2.2.1 hcbds.2.2.2.2.2.2.2.2.2.1 hc_sex' (fun h => absurd h (by decide))
    hpc12_eq hregs12 ((hreg12 .x22 (by simp)).trans hs11_22) hro12 hbt12 hcm12 htbl12 hw12 ht12'
  simp only [Bool.false_eq_true, ↓reduceIte] at hrEnd
  have htot := ((((hg2.trans hbne).trans hr10).trans hsr).trans hr12).trans hrEnd
  have heq_c : 1 + 1 + (6 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 false).length) + 1 +
      (5 + 4 * if 6 * tails.length % 64 + 6 * ts7.length < 64 then 0 else 1) +
      (if ordinal + 1 = positions.card then 6 else 5) =
      (1 + 1 + (6 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 false).length) +
        1 + 5 + (if ordinal + 1 = positions.card then 6 else 5)) +
      4 * if 6 * tails.length % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1 := by
    rw [hts7_eq]; omega
  rw [heq_c] at htot
  exact ⟨sEnd, htot, hpost⟩

/-- Execute one full record iteration from `RecInv ... r0` at `pcRec r0` (all 4 branches:
slow, fast 9-tail, skip14 8-tail, skip12+14 7-tail), maintaining exact amortized bound! -/
theorem openRuns_rec_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {ordinal base flushes : Nat} {r0 : Fin 8}
    {written : List Byte} {tails : List (BitVec 6)} {tblInit : Bool} {s : MachineState}
    (hord : ordinal < positions.card)
    (hbd_w : base + 528 ≤ 8556390424)
    (hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936)
    (hinv : RecInv trapdoor positions ordinal r0 base written tails flushes tblInit s) :
    let i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    let rFwd := recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let rTails := recordTails (tdNode trapdoor) i
    let fl := if (6 * tails.length) % 64 + 6 * rTails.length < 64 then 0 else 1
    let last : Bool := decide (ordinal + 1 = positions.card)
    ∃ recSteps cycNf rEnd baseEnd tblInit' s',
      recSteps ≤ cycNf + (if tblInit = false ∧ tblInit' = true then 168 else 0) + 4 * fl ∧
      OpenRuns s recSteps (cycNf + (if tblInit = false ∧ tblInit' = true then 168 else 0) + 4 * fl) s' ∧
      (tblInit = true → tblInit' = true) ∧
      8 * cycNf + phi8 rEnd ≤ 3453 + phi8 r0 + (if last then 16 else 0) ∧
      baseEnd ≤ base + 504 ∧
      if _hlast : ordinal + 1 = positions.card then
        CapEntryInv trapdoor positions rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) s'
      else
        RecInv trapdoor positions (ordinal + 1) rEnd baseEnd (written ++ rFwd) (tails ++ rTails) (flushes + fl) tblInit' s' := by
  set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
  set g := i.val / 3
  have hi_lt : i.val < 16777216 := i.isLt
  have hcodes := codeAt_rec_all r0
  -- Split recPrefixCode r0
  have hpre' : CodeAt (pcRec r0) (saltAddrCode ++ (dwordsCode r0 3 .x10 0 0 false (r0.val == 4) ++
      (l0DivuCode ++ [.base (.BGEU .x22 .x13 (BitVec.ofNat 13 (4 * (pcSlowStub r0 - pcSlowGuard r0))))]))) := by
    simpa only [recPrefixCode, List.append_assoc] using hcodes.1
  have hc_sa := hpre'.left; have hrP1 := hpre'.right
  have hc_sd := hrP1.left; have hrP2 := hrP1.right
  have hc_dv := hrP2.left; have hc_bg := hrP2.right
  -- Step 1: saltAddr (11 cyc) + salt copy (24 B = 3 dw) + l0Divu (4 ins, 7 cyc)
  obtain ⟨s1, hr1, hpc1, hs1_8, hs1_10, hreg1, hmem1⟩ :=
    openRuns_salt_addr hc_sa hinv.hpc hord hinv.regs.rx24 hinv.regs.rx18 hinv.hro
  have hro1 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s1 := fun a ha => (hmem1 a).trans (hinv.hro a ha)
  have hw1 := writerState_of_mem_eq hinv.hw hmem1 (hreg1 .x25 (by simp)) (hreg1 .x12 (by simp))
  have hs_al : saltOff i % 8 = 0 := saltOff_align8' i
  have hs_bd : saltOff i + 24 ≤ 7046431776 := by rw [saltOff_formula']; omega
  obtain ⟨s2, hr2, hpc2, hreg2, hp2, hw2⟩ := openRuns_dwords 3 (s := s1)
    (vals := fun k => (tdSalt trapdoor i).extractLsb' (64 * k) 64)
    (by omega) hc_sd hpc1 (by decide) hs1_10
    (by dsimp only [i] at hs_al; omega) (by omega)
    (by dsimp only [i] at hs_bd; omega)
    (fun _ k hk => by simpa only [Nat.add_zero] using readOnly_getMem_tdSalt hro1 i k hk)
    (by omega) (by omega) hw1
  rw [(bitsToBytes_take_dwords _ 3).symm, Bool.and_self] at hw2
  have hs2_8 : s2.getReg .x8 = BitVec.ofNat 64 i.val := (hreg2 .x8 (by simp)).trans hs1_8
  have hs2_20 : s2.getReg .x20 = BitVec.ofNat 64 3 := (hreg2 .x20 (by simp)).trans ((hreg1 .x20 (by simp)).trans hinv.regs.rx20)
  obtain ⟨s3, hr3, hpc3, hs3_22, hs3_6, hs3_8, hreg3, hmem3⟩ := openRuns_l0_divu hc_dv hpc2 hs2_8 hs2_20
  have hpc_bg_eq : pcRec r0 + saltAddrCode.length + (dwordsCode r0 3 .x10 0 0 false (r0.val == 4)).length + l0DivuCode.length = pcSlowGuard r0 := by
    simp only [pcSlowGuard, saltAddrCode, l0DivuCode, List.length_cons, List.length_nil]
  have hpc3_eq : s3.pc = pcAt (pcSlowGuard r0) := by
    rw [hpc3]; apply congrArg pcAt; simp only [saltAddrCode, l0DivuCode, List.length_cons, List.length_nil] at hpc_bg_eq ⊢; omega
  have hbg_ins : openInstr (pcSlowGuard r0) = .base (.BGEU .x22 .x13 (BitVec.ofNat 13 (4 * (pcSlowStub r0 - pcSlowGuard r0)))) := by
    have h := hc_bg.2 0 (by simp)
    rw [Nat.add_zero, hpc_bg_eq] at h; exact h
  have hbg_bd : pcSlowGuard r0 < OPEN_CODE_LEN := by fin_cases r0 <;> decide
  have hs3_13 : s3.getReg .x13 = BitVec.ofNat 64 5592064 :=
    (hreg3 .x13 (by simp)).trans ((hreg2 .x13 (by simp)).trans ((hreg1 .x13 (by simp)).trans hinv.regs.rx13))
  have hreg30 : RegsEqExcept [.x5, .x6, .x8, .x10, .x12, .x22, .x28] s s3 := fun reg hreg => by
    have h5' : reg ≠ .x5 := fun h => hreg (by simp [h])
    have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
    have h8' : reg ≠ .x8 := fun h => hreg (by simp [h])
    have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
    have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
    have h22' : reg ≠ .x22 := fun h => hreg (by simp [h])
    have h28' : reg ≠ .x28 := fun h => hreg (by simp [h])
    exact (hreg3 reg (by simp [h6', h8', h22'])).trans ((hreg2 reg (by simp [h5', h6', h12'])).trans (hreg1 reg (by simp [h6', h8', h10', h28'])))
  have hp30 : ProofWritePreserves s s3 := ProofWritePreserves.trans (fun a _ => hmem1 a) <| hp2.trans (fun a _ => hmem3 a)
  have hro3 := ReadOnlyPreserved.of_proofWrite hinv.hro hp30
  have hbt3 : BaseTableReady s3 := baseTableReady_of_lowEq hinv.hbt (fun a ha => (proofWrite_pres_low hp30).1 a ha)
  have hcm3 : CapMarks15State s3 positions ordinal := capMarks15State_of_lowEq hinv.hcm (fun a h1 h2 => (proofWrite_pres_low hp30).2.1 a h1 h2)
  have htbl3 : SlowTablesState s3 tblInit := slowTablesState_of_eq hinv.htbl (fun a h1 h2 => (proofWrite_pres_low hp30).2.2 a h1 h2)
  have hw3 := writerState_of_mem_eq hw2 hmem3 (hreg3 .x25 (by simp)) (hreg3 .x12 (by simp))
  have ht3 : TailState (CleanTrapdoor trapdoor) s3 tails flushes :=
    TailState.of_proofWrite hinv.ht hp30 (hreg30 .x15 (by decide)) (hreg30 .x16 (by decide)) (hreg30 .x17 (by decide))
  have hregs3 : RecRegs positions ordinal s3 := recRegs_of_eq hinv.regs (fun reg h => hreg30 reg (reg_not_mem_sub (by decide) h))
  -- Branch 1: Slow path (`g ≥ 5,592,064`)
  by_cases hslow : 5592064 ≤ g
  · have hge_s : (s3.getReg .x13).toNat ≤ (s3.getReg .x22).toNat := by
      rw [hs3_22, hs3_13, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : g < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 5592064 < 2 ^ 64)]; omega
    have hbr_ok : pcSlowGuard r0 ≤ pcSlowStub r0 ∧ 4 * (pcSlowStub r0 - pcSlowGuard r0) < 4096 := by fin_cases r0 <;> decide
    have hbg := step_BGEU_taken (s := s3) hbg_bd hpc3_eq hbg_ins hge_s (pcAt_add_pos13 _ _ hbr_ok.1 hbr_ok.2)
    set s4 := s3.setPC (pcAt (pcSlowStub r0))
    obtain ⟨s5, hr5, hsinv⟩ := openRuns_slow_stub hord (by omega) (rfl : s4.pc = pcAt (pcSlowStub r0))
      (recRegs_of_eq hregs3 (fun _ _ => by simp [s4])) (by simpa [s4] using hs3_6) (by simpa [s4] using hs3_8) (by simpa [s4] using hs3_22)
      (fun a ha => (by simp [s4] : s4.getMem a = s3.getMem a).trans (hro3 a ha))
      (baseTableReady_of_lowEq hbt3 (fun _ _ => by simp [s4]))
      (capMarks15State_of_lowEq hcm3 (fun _ _ _ => by simp [s4]))
      (slowTablesState_of_eq htbl3 (fun _ _ _ => by simp [s4]))
      (writerState_of_mem_eq hw3 (fun _ => by simp [s4]) (by simp [s4]) (by simp [s4]))
      (TailState.of_proofWrite ht3 (fun _ _ => by simp [s4]) (by simp [s4]) (by simp [s4]) (by simp [s4]))
    obtain ⟨cycSlow, rEnd, baseEnd, sEnd, hrSlow, hamort, hpost⟩ := openRuns_slow_body hord hbd_w hbd_t hslow hsinv
    have hbaseEnd_le : baseEnd ≤ base + 504 := by
      have hb8 := hinv.hw.hbase8
      have hlen_w : written.length = base + r0.val := by simpa using hinv.hw.hlen
      have hlen_r := recordFwd_length_le_501 (tdNode trapdoor) (tdSalt trapdoor) i
      have hlen_e : (written ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i).length = baseEnd + rEnd.val ∧ baseEnd % 8 = 0 := by
        by_cases hlast : ordinal + 1 = positions.card
        · simp only [hlast, ↓reduceDIte] at hpost; exact ⟨by simpa using hpost.hw.hlen, hpost.hw.hbase8⟩
        · simp only [hlast, ↓reduceDIte] at hpost; exact ⟨by simpa using hpost.hw.hlen, hpost.hw.hbase8⟩
      have hr0_lt := r0.isLt; have hrE_lt := rEnd.isLt
      have hlen_e1 := hlen_e.1; have hbE8 := hlen_e.2
      simp only [List.length_append] at hlen_e1; omega
    have htot := ((((hr1.trans hr2).trans hr3).trans hbg).trans hr5).trans hrSlow
    set fl := if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1
    set slowSteps := 11 + (dwordsCode r0 3 .x10 0 0 false (r0.val == 4)).length + 4 + 1 + (if r0.val == 4 then 6 else 3) +
        (cycSlow + (if tblInit then 0 else 168) + 4 * fl)
    have hse : 11 + (dwordsCode r0 3 .x10 0 0 false (r0.val == 4)).length + 7 + 1 + (if r0.val == 4 then 6 else 3) = slowEntryCyc r0 := rfl
    have htb : (if tblInit then 0 else 168) = (if tblInit = false ∧ true = true then 168 else 0) := by cases tblInit <;> rfl
    have heq_c : 11 + (dwordsCode r0 3 .x10 0 0 false (r0.val == 4)).length + 7 + 1 + (if r0.val == 4 then 6 else 3) +
        (cycSlow + (if tblInit then 0 else 168) + 4 * fl) =
        slowEntryCyc r0 + cycSlow + (if tblInit = false ∧ true = true then 168 else 0) + 4 * fl := by
      rw [hse, htb]; omega
    rw [heq_c] at htot
    refine ⟨slowSteps, slowEntryCyc r0 + cycSlow, rEnd, baseEnd, true, sEnd,
      by unfold slowSteps; rw [← hse, ← htb]; omega,
      htot, fun _ => rfl, le_trans hamort (by split_ifs <;> omega), hbaseEnd_le, hpost⟩
  · -- Branch 2: Fast / Edge path (`g < 5,592,064`)
    have hg : g < 5592064 := by omega
    have hf := level_sib_lt_of_fast g hg
    have hlt_s : (s3.getReg .x22).toNat < (s3.getReg .x13).toNat := by
      rw [hs3_22, hs3_13, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : g < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 5592064 < 2 ^ 64)]; omega
    have hbg := step_BGEU_not_taken (s := s3) hbg_bd hpc3_eq hbg_ins hlt_s
    set s4 := s3.setPC (pcAt (pcSlowGuard r0 + 1))
    have hbody' : CodeAt (pcSlowGuard r0 + 1) (recL0L5Code r0 ++ (recL6L11Code r0 ++ (recL12GuardCode r0 ++ (recFastTailCode r0 ++ recFastExitCode r0)))) := by
      simpa only [List.append_assoc] using hcodes.2.2.1
    have hc_l05 := hbody'.left; have hrB1 := hbody'.right
    have hc_l611 := hrB1.left; have hrB2 := hrB1.right
    have hc_eg := hrB2.left; have hrB3 := hrB2.right
    have hc_ft := hrB3.left; have hc_fe := hrB3.right
    have hregs4 : RecRegs positions ordinal s4 := recRegs_of_eq hregs3 (fun _ _ => by simp [s4])
    obtain ⟨c05, s5, hr5, hc05, hpc5, hs5_22, hreg5, hp5, hw5⟩ := openRuns_rec_l0_l5 hord hbd_w hg hc_l05
      (rfl : s4.pc = pcAt (pcSlowGuard r0 + 1)) hregs4
      (by simpa [s4] using hs3_6) (by simpa [s4] using hs3_8) (by simpa [s4] using hs3_22)
      (fun a ha => (by simp [s4] : s4.getMem a = s3.getMem a).trans (hro3 a ha))
      (writerState_of_mem_eq hw3 (fun _ => by simp [s4]) (by simp [s4]) (by simp [s4]))
    have hro5 := ReadOnlyPreserved.of_proofWrite (fun a ha => (by simp [s4] : s4.getMem a = s3.getMem a).trans (hro3 a ha)) hp5
    have hregs5 := recRegs_of_eq hregs4 (fun reg h => hreg5 reg (reg_not_mem_sub (by decide) h))
    obtain ⟨s6, hr6, hpc6, hs6_22, hs6_8, hreg6, hp6, hw6⟩ := openRuns_rec_l6_l11 hord hbd_w hg hc_l611 hpc5 hregs5 hs5_22 hro5 hw5
    change s6.getReg .x22 = BitVec.ofNat 64 (g >>> 11) at hs6_22
    change CleanTrapdoor trapdoor → s6.getReg .x8 = BitVec.ofNat 64 (bitsOf6 (ts6Of trapdoor i)) at hs6_8
    have hp63 : ProofWritePreserves s3 s6 := ProofWritePreserves.trans (fun a _ => by simp [s4]) <| hp5.trans hp6
    have hro6 := ReadOnlyPreserved.of_proofWrite hro3 hp63
    have hbt6 : BaseTableReady s6 := baseTableReady_of_lowEq hbt3 (fun a ha => (proofWrite_pres_low hp63).1 a ha)
    have hcm6 : CapMarks15State s6 positions ordinal := capMarks15State_of_lowEq hcm3 (fun a h1 h2 => (proofWrite_pres_low hp63).2.1 a h1 h2)
    have htbl6 : SlowTablesState s6 tblInit := slowTablesState_of_eq htbl3 (fun a h1 h2 => (proofWrite_pres_low hp63).2.2 a h1 h2)
    have hregs6 := recRegs_of_eq hregs5 (fun reg h => hreg6 reg (reg_not_mem_sub (by decide) h))
    have ht6 : TailState (CleanTrapdoor trapdoor) s6 tails flushes :=
      TailState.of_proofWrite ht3 hp63
        ((hreg6 .x15 (by simp)).trans ((hreg5 .x15 (by simp)).trans (by simp [s4])))
        ((hreg6 .x16 (by simp)).trans ((hreg5 .x16 (by simp)).trans (by simp [s4])))
        ((hreg6 .x17 (by simp)).trans ((hreg5 .x17 (by simp)).trans (by simp [s4])))
    set pcEG := pcSlowGuard r0 + 1 + (recL0L5Code r0).length + (recL6L11Code r0).length
    have hpcEG_eq : pcEG + 2 = pcEdgeGuard r0 := rfl
    have heg_bd : pcEG + 3 ≤ OPEN_CODE_LEN := by have := hc_eg.1; simp only [recL12GuardCode, List.length_cons, List.length_nil] at this; exact this
    have heg0 : openInstr pcEG = .base (.XORI .x28 .x22 (1#12)) := by
      have h := hc_eg.2 0 (by simp [recL12GuardCode]); simpa only [recL12GuardCode, List.getElem_cons_zero, Nat.add_zero] using h
    have heg1 : openInstr (pcEG + 1) = .base (.SRLI .x22 .x22 (1#6)) := by
      have h := hc_eg.2 1 (by simp [recL12GuardCode]); simpa only [recL12GuardCode, List.getElem_cons_succ, List.getElem_cons_zero] using h
    have heg2 : openInstr (pcEdgeGuard r0) = .base (.BGEU .x22 .x19 (BitVec.ofNat 13 (4 * (pcEdge1214 r0 - pcEdgeGuard r0)))) := by
      have h := hc_eg.2 2 (by simp [recL12GuardCode]); simpa only [recL12GuardCode, List.getElem_cons_succ, List.getElem_cons_zero, hpcEG_eq] using h
    have hg0 := step_XORI (s := s6) (by omega) hpc6 heg0
    set s7a := (s6.setReg .x28 (s6.getReg .x22 ^^^ signExtend12 (1#12))).setPC (pcAt (pcEG + 1))
    have hg1 := step_SRLI (s := s7a) (by omega) rfl heg1
    set s7 := (s7a.setReg .x22 (s7a.getReg .x22 >>> (1#6).toNat)).setPC (pcAt (pcEG + 1 + 1))
    have hs7_pc : s7.pc = pcAt (pcEdgeGuard r0) := by dsimp only [s7, MachineState.setPC]; apply congrArg pcAt; omega
    have hs7_28 : s7.getReg .x28 = BitVec.ofNat 64 ((g >>> 11) ^^^ 1) := by
      simp [s7, s7a, getReg_setReg_ne', hs6_22, bv64_xor1 (g >>> 11) (by simp [Nat.shiftRight_eq_div_pow]; omega)]
    have hs7_22 : s7.getReg .x22 = BitVec.ofNat 64 (g >>> 12) := by
      have h : s7.getReg .x22 = BitVec.ofNat 64 ((g >>> 11) >>> 1) := by
        simp [s7, s7a, getReg_setReg_ne', hs6_22, show (1#6 : BitVec 6).toNat = 1 from rfl,
          bv64_ushr (g >>> 11) 1 (by simp [Nat.shiftRight_eq_div_pow]; omega)]
      simpa only [show (g >>> 11) >>> 1 = g >>> 12 by simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]] using h
    have hs7_19 : s7.getReg .x19 = BitVec.ofNat 64 1364 := by simp [s7, s7a, getReg_setReg_ne', hregs6.rx19]
    have hs7_mem : ∀ a, s7.getMem a = s6.getMem a := fun a => by simp [s7, s7a]
    have hro7 : ReadOnlyPreserved (openSub.initialState .opening (trapdoor, positions)) s7 := fun a ha => (hs7_mem a).trans (hro6 a ha)
    have hbt7 : BaseTableReady s7 := baseTableReady_of_lowEq hbt6 (fun a _ => hs7_mem a)
    have hcm7 : CapMarks15State s7 positions ordinal := capMarks15State_of_lowEq hcm6 (fun a _ _ => hs7_mem a)
    have htbl7 : SlowTablesState s7 tblInit := slowTablesState_of_eq htbl6 (fun a _ _ => hs7_mem a)
    have hw7 : WriterState (CleanTrapdoor trapdoor) s7 (recL12St r0).1 (recL12St r0).2.2 base (recL12St r0).2.1 (l0l11Fwd trapdoor i written) :=
      writerState_of_mem_eq hw6 hs7_mem (by simp [s7, s7a, getReg_setReg_ne']) (by simp [s7, s7a, getReg_setReg_ne'])
    have ht7 : TailState (CleanTrapdoor trapdoor) s7 tails flushes :=
      TailState.of_proofWrite ht6 (fun a _ => hs7_mem a) (by simp [s7, s7a, getReg_setReg_ne']) (by simp [s7, s7a, getReg_setReg_ne']) (by simp [s7, s7a, getReg_setReg_ne'])
    have hregs7 : RecRegs positions ordinal s7 := recRegs_of_eq hregs6 (fun reg h => by
      have h22' : reg ≠ .x22 := fun hm => h (by simp [hm])
      have h28' : reg ≠ .x28 := fun hm => h (by simp [hm])
      simp [s7, s7a, getReg_setReg_ne' .x22 reg h22'.symm, getReg_setReg_ne' .x28 reg h28'.symm])
    have hs7_8 : CleanTrapdoor trapdoor → s7.getReg .x8 = BitVec.ofNat 64 (bitsOf6 (ts6Of trapdoor i)) := fun hcl => by
      simp [s7, s7a, getReg_setReg_ne', hs6_8 hcl]
    have hpre_run := ((((((hr1.trans hr2).trans hr3).trans hbg).trans hr5).trans hr6).trans hg0).trans hg1
    have hno_tbl : (if tblInit = false ∧ tblInit = true then 168 else 0) = 0 := by cases tblInit <;> simp
    set fl := if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1
    set preSteps := 11 + (dwordsCode r0 3 .x10 0 0 false (r0.val == 4)).length + 4 + 1 + c05 + (recL6L11Code r0).length + 1 + 1
    set preCyc := 11 + (dwordsCode r0 3 .x10 0 0 false (r0.val == 4)).length + 7 + 1 + c05 + (recL6L11Code r0).length + 1 + 1
    by_cases h13_lt : g >>> 12 < 1364
    · have hc_ft' : CodeAt (pcEdgeGuard r0 + 1) (recFastTailCode r0) := by
        simpa only [pcEdgeGuard, recL12GuardCode, List.length_cons, List.length_nil,
          show pcSlowGuard r0 + 1 + (recL0L5Code r0).length + (recL6L11Code r0).length + 3 =
            pcSlowGuard r0 + 1 + (recL0L5Code r0).length + (recL6L11Code r0).length + 2 + 1 by omega] using hc_ft
      have hc_fe' : CodeAt (pcFastExit r0) (recFastExitCode r0) := by
        have heq_p : pcSlowGuard r0 + 1 + (recL0L5Code r0).length + (recL6L11Code r0).length +
            (recL12GuardCode r0).length + (recFastTailCode r0).length = pcFastExit r0 := by
          simp only [pcFastExit, pcEdgeGuard, recL12GuardCode, List.length_cons, List.length_nil]
        rw [heq_p] at hc_fe; exact hc_fe
      obtain ⟨sEnd, hrTail, hpost⟩ := openRuns_rec_fast9 hord hbd_w hbd_t hg h13_lt (by omega) heg2 hc_ft' hc_fe'
        hs7_pc hregs7 hs7_28 hs7_22 hs7_19 hs7_8 hro7 hbt7 hcm7 htbl7 hw7 ht7
      set cycTail := 1 +
        (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
        (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 true).length) +
        (6 + (copy29Code (recL14St r0).1 .x10 (recL14St r0).2.1 .x8 48 false (recL14St r0).2.2 false).length) +
        5 + (if ordinal + 1 = positions.card then 6 else if !(r0.val == 3) then 4 else 5)
      have htot := hpre_run.trans hrTail
      have heq_c : preCyc + (cycTail + 4 * fl) = (preCyc + cycTail) + (if tblInit = false ∧ tblInit = true then 168 else 0) + 4 * fl := by
        rw [hno_tbl]; omega
      rw [heq_c] at htot
      refine ⟨preSteps + (cycTail + 4 * fl), preCyc + cycTail, copy29NextR r0, base + copy29NextDstOff r0 472, tblInit, sEnd,
        by rw [hno_tbl]; unfold preSteps preCyc; omega, htot, id, ?_,
        by unfold copy29NextDstOff; split_ifs <;> omega, hpost⟩
      · have ha := (rec_amort_all r0 (decide (ordinal + 1 = positions.card))).1
        have hle : preCyc + cycTail ≤ fastPathMaxNf r0 (decide (ordinal + 1 = positions.card)) := by
          unfold fastPathMaxNf preCyc cycTail
          simp only [recFastTailCode, l12RestAddrCode, lvlAddrMemCode, tailMergeCode, List.length_append, List.length_cons, List.length_nil]
          by_cases hlast : ordinal + 1 = positions.card <;> cases h3 : (r0.val == 3) <;> simp [hlast] <;> omega
        exact le_trans (by omega) ha
    · by_cases h13_eq : g >>> 12 = 1364
      · obtain ⟨sEnd, hrTail, hpost⟩ := openRuns_rec_skip14 hord hbd_w hbd_t hg h13_eq (by omega) heg2 hcodes.2.2.2.1
          hs7_pc hregs7 hs7_28 hs7_22 hs7_19 hs7_8 hro7 hbt7 hcm7 htbl7 hw7 ht7
        set cycTail := 1 + 1 +
          (4 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 true).length) +
          (6 + (copy29Code (recL13St r0).1 .x10 (recL13St r0).2.1 .x8 42 false (recL13St r0).2.2 false).length) +
          1 + 5 + (if ordinal + 1 = positions.card then 6 else 5)
        have htot := hpre_run.trans hrTail
        have heq_c : preCyc + (cycTail + 4 * fl) = (preCyc + cycTail) + (if tblInit = false ∧ tblInit = true then 168 else 0) + 4 * fl := by
          rw [hno_tbl]; omega
        rw [heq_c] at htot
        refine ⟨preSteps + (cycTail + 4 * fl), preCyc + cycTail, r0, base + 472, tblInit, sEnd,
          by rw [hno_tbl]; unfold preSteps preCyc; omega, htot, id, ?_, by omega, hpost⟩
        · have ha := (rec_amort_all r0 (decide (ordinal + 1 = positions.card))).2.1
          have hle : preCyc + cycTail ≤ s14PathMaxNf r0 (decide (ordinal + 1 = positions.card)) := by
            unfold s14PathMaxNf preCyc cycTail
            simp only [recEdgeBodyCode, l12RestAddrCode, lvlAddrMemCode, tailMergeCode, List.length_append, List.length_cons, List.length_nil]
            by_cases hlast : ordinal + 1 = positions.card <;> simp [hlast] <;> omega
          exact le_trans (by omega) ha
      · have h13_1365 : g >>> 12 = 1365 := by have := hf.2.2.2.2.2.2.2.2.2.2.2.2; omega
        obtain ⟨sEnd, hrTail, hpost⟩ := openRuns_rec_skip1214 hord hbd_w hbd_t hg h13_1365 (by omega) heg2
          hcodes.2.2.2.1 hcodes.2.2.2.2 hs7_pc hregs7 hs7_22 hs7_19 hs7_8 hro7 hbt7 hcm7 htbl7 hw7 ht7
        set cycTail := 1 + 1 +
          (6 + (copy29Code (recL12St r0).1 .x10 (recL12St r0).2.1 .x8 36 false (recL12St r0).2.2 false).length) +
          1 + 5 + (if ordinal + 1 = positions.card then 6 else 5)
        have htot := hpre_run.trans hrTail
        have heq_c : preCyc + (cycTail + 4 * fl) = (preCyc + cycTail) + (if tblInit = false ∧ tblInit = true then 168 else 0) + 4 * fl := by
          rw [hno_tbl]; omega
        rw [heq_c] at htot
        refine ⟨preSteps + (cycTail + 4 * fl), preCyc + cycTail, copy29NextR (recL12St r0).1,
          base + copy29NextDstOff (recL12St r0).1 (recL12St r0).2.1, tblInit, sEnd,
          by rw [hno_tbl]; unfold preSteps preCyc; omega, htot, id, ?_,
          by have := (recC29_bds r0).2.2.2.2.2.1; unfold copy29NextDstOff; split_ifs <;> omega, hpost⟩
        · have ha := (rec_amort_all r0 (decide (ordinal + 1 = positions.card))).2.2
          have hle : preCyc + cycTail ≤ s1214PathMaxNf r0 (decide (ordinal + 1 = positions.card)) := by
            unfold s1214PathMaxNf preCyc cycTail
            simp only [recSkipBodyCode, lvlAddrMemCode, tailMergeCode, List.length_append, List.length_cons, List.length_nil]
            by_cases hlast : ordinal + 1 = positions.card <;> simp [hlast] <;> omega
          exact le_trans (by omega) ha

/-- Induction across remaining records `ordinal .. positions.card - 1` landing at `PC_cap_pass`! -/
private theorem openRuns_rec_loop {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} (rem : Nat) (hrem : 1 ≤ rem) :
    ∀ {ordinal base flushes : Nat} {r0 : Fin 8} {written : List Byte} {tails : List (BitVec 6)}
      {tblInit : Bool} {s : MachineState},
    ordinal + rem = positions.card →
    base ≤ 504 * ordinal →
    tails.length ≤ 9 * ordinal →
    RecInv trapdoor positions ordinal r0 base written tails flushes tblInit s →
    let rest := (positions.sort (· ≤ ·)).drop ordinal
    let addFwd := rest.flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    let addTails := rest.flatMap (recordTails (tdNode trapdoor))
    ∃ recSteps cycNf flNew rEnd baseEnd s',
      recSteps ≤ cycNf + 4 * flNew ∧
      OpenRuns s recSteps (cycNf + 4 * flNew) s' ∧
      8 * cycNf + phi8 rEnd ≤ 3453 * rem + phi8 r0 + 16 + (if tblInit then 0 else 8 * 168) ∧
      64 * (flushes + flNew) ≤ 6 * (tails ++ addTails).length ∧
      CapEntryInv trapdoor positions rEnd baseEnd (written ++ addFwd) (tails ++ addTails) (flushes + flNew) s' := by
  induction rem with
  | zero => omega
  | succ rem ih =>
    intro ordinal base flushes r0 written tails tblInit s hsum hbase_le htails_le hinv
    have hcard := positions_card_le' positions
    have hord : ordinal < positions.card := by omega
    have hbd_w : base + 528 ≤ 8556390424 := by omega
    have hfl_le : 64 * flushes ≤ 6 * tails.length := by have := hinv.ht.hbits; omega
    have hbd_t : 8 * (flushes + 1) + 16 ≤ 48719475936 := by omega
    set i := (positions.sort (· ≤ ·))[ordinal]'(by simp [hord])
    have hdrop : (positions.sort (· ≤ ·)).drop ordinal = i :: (positions.sort (· ≤ ·)).drop (ordinal + 1) :=
      List.drop_eq_getElem_cons (by simp [hord])
    obtain ⟨recSteps1, cycNf1, r1, base1, tblInit1, s1, hst1_le, hr1, htbl_mono, hamort1, hbase1_le, hpost1⟩ :=
      openRuns_rec_step hord hbd_w hbd_t hinv
    set fl1 := if (6 * tails.length) % 64 + 6 * (recordTails (tdNode trapdoor) i).length < 64 then 0 else 1
    set tblCyc1 := if tblInit = false ∧ tblInit1 = true then 168 else 0
    cases rem with
    | zero =>
      have hlast : ordinal + 1 = positions.card := by omega
      simp only [hlast, ↓reduceDIte] at hpost1
      have hdrop_empty : (positions.sort (· ≤ ·)).drop (ordinal + 1) = [] := by
        rw [List.drop_eq_nil_iff]; simp; omega
      have hrest : (positions.sort (· ≤ ·)).drop ordinal = [i] := by rw [hdrop, hdrop_empty]
      refine ⟨recSteps1, cycNf1 + tblCyc1, fl1, r1, base1, s1, hst1_le, hr1, ?_, ?_, ?_⟩
      · have h1 : decide (ordinal + 1 = positions.card) = true := decide_eq_true hlast
        simp only [h1, ↓reduceIte] at hamort1
        unfold tblCyc1; cases tblInit <;> cases tblInit1 <;> simp at hamort1 ⊢ <;> omega
      · have hbits : 64 * (flushes + fl1) + (6 * (tails ++ recordTails (tdNode trapdoor) i).length) % 64 =
            6 * (tails ++ recordTails (tdNode trapdoor) i).length := hpost1.ht.hbits
        simp only [hrest, List.flatMap_cons, List.flatMap_nil, List.append_nil]; omega
      · simpa only [hrest, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hpost1
    | succ rem' =>
      have hnlast : ordinal + 1 ≠ positions.card := by omega
      simp only [hnlast, ↓reduceDIte] at hpost1
      have ht1_le : (tails ++ recordTails (tdNode trapdoor) i).length ≤ 9 * (ordinal + 1) := by
        simp only [List.length_append]; have := recordTails_length_le_9 (tdNode trapdoor) i; omega
      obtain ⟨recSteps2, cycNf2, fl2, rEnd, baseEnd, sEnd, hst2_le, hr2, hamort2, hfl_end, hcap⟩ :=
        ih (by omega) (by omega) (by omega) ht1_le hpost1
      have h1 : decide (ordinal + 1 = positions.card) = false := decide_eq_false hnlast
      simp only [h1, Bool.false_eq_true, ↓reduceIte] at hamort1
      refine ⟨recSteps1 + recSteps2, cycNf1 + tblCyc1 + cycNf2, fl1 + fl2, rEnd, baseEnd, sEnd, by omega, ?_, ?_, ?_, ?_⟩
      · have heq : (cycNf1 + tblCyc1 + 4 * fl1) + (cycNf2 + 4 * fl2) = (cycNf1 + tblCyc1 + cycNf2) + 4 * (fl1 + fl2) := by omega
        have htot := hr1.trans hr2
        rw [heq] at htot; exact htot
      · unfold tblCyc1
        cases tblInit with
        | true =>
          have ht1 := htbl_mono rfl; subst ht1; simp only [Bool.true_eq_false, false_and, ↓reduceIte] at hamort2 ⊢; omega
        | false =>
          cases tblInit1 <;> simp only [true_and, Bool.false_eq_true, ↓reduceIte] at hamort2 ⊢ <;> omega
      · simpa only [hdrop, List.flatMap_cons, List.append_assoc, Nat.add_assoc] using hfl_end
      · simpa only [hdrop, List.flatMap_cons, List.append_assoc, Nat.add_assoc] using hcap

/-- Full record-loop theorem from `PC_rec_r0 = 59` (after `openRuns_entry_nonzero`) to `PC_cap_pass = 6793`! -/
theorem openRuns_rec_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hne : positions.card ≠ 0)
    (hinv : RecInv trapdoor positions 0 ⟨0, by omega⟩ 0 [] [] 0 false s) :
    let allFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    let allTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    ∃ recSteps cycNf recFlushes rEnd baseEnd s',
      recSteps ≤ cycNf + 4 * recFlushes ∧
      OpenRuns s recSteps (cycNf + 4 * recFlushes) s' ∧
      8 * cycNf + phi8 rEnd ≤ 3453 * positions.card + 16 + 8 * 168 ∧
      allTails.length ≤ 9 * positions.card ∧
      64 * recFlushes ≤ 6 * allTails.length ∧
      CapEntryInv trapdoor positions rEnd baseEnd allFwd allTails recFlushes s' := by
  have hcard := positions_card_le' positions
  obtain ⟨recSteps, cycNf, fl, rEnd, baseEnd, s', hst_le, hr, hamort, hfl, hcap⟩ :=
    openRuns_rec_loop positions.card (by omega) (by omega) (by omega) (by simp) hinv
  have hphi0 : phi8 ⟨0, by omega⟩ = 0 := rfl
  have hcyc_le : 8 * cycNf + phi8 rEnd ≤ 3453 * positions.card + 16 + 8 * 168 := by
    rw [hphi0] at hamort; simp only [Bool.false_eq_true, ↓reduceIte] at hamort; omega
  have ht_le : ((positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))).length ≤ 9 * positions.card := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    have haux : ∀ l : List Index, (l.flatMap (recordTails (tdNode trapdoor))).length ≤ 9 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have := recordTails_length_le_9 (tdNode trapdoor) x; omega
    simpa only [hlen] using haux (positions.sort (· ≤ ·))
  refine ⟨recSteps, cycNf, fl, rEnd, baseEnd, s', hst_le, hr, hcyc_le, ht_le, by simpa using hfl, by simpa using hcap⟩

end CommitGolfCandidate.MoonOpen

