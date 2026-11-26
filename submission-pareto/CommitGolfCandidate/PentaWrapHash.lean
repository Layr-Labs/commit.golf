import CommitGolfCandidate.CheckActions
import CommitGolfCandidate.PentaWrapRunB

/-! The checker wrapper's hash phase (wrapper offsets 315-3456) under a fixed oracle.

The submitted proof carries only the 43 level-7 table groups. After the table loop has doubled them
into the scratch table, the hash phase recomputes the 54 nodes of levels 8, 9 and 10: hash `i`
copies the five slots of doubled group `i` behind 40 zero bytes in the scratch buffer `HB`, calls
the permutation into `OB`, and stores the low 256 bits of the reply in both copies of its slot.
`hashTable` models the doubled table after `i` hashes. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.CheckActions

set_option maxRecDepth 100000

def HBW : Nat := 67108864
def OBW : Nat := 67108896

/-- Doubled-table offset (in words) of the first copy of the slot written by hash `i`. -/
def dstOff (i : Nat) : Nat := 40*(hashSlot i / 5) + 4*(hashSlot i % 5)

theorem hash_src_word (i : Nat) : hashSrc i = 8*(TBW + 40*i) := by unfold hashSrc TABLE TBW; omega
theorem hash_dst_word (i : Nat) : hashDst i = 8*(TBW + dstOff i) := by unfold hashDst dstOff TABLE TBW; omega

/-- The permutation input of hash `i` for a doubled table `T`: 40 zero bytes, then group `i`. -/
def hashInput (T : Nat → Word) (i : Nat) : Words 25 :=
  fun j => if j.val < 5 then 0 else T (40*i + (j.val - 5))

def hashReply (o : Oracle) (T : Nat → Word) (i : Nat) : BitVec 1600 :=
  o.permutation (packBuffer (hashInput T i))

/-- One hash: both copies of slot `hashSlot i` receive the low four reply words. -/
def hashStep (o : Oracle) (T : Nat → Word) (i : Nat) : Nat → Word :=
  fun x =>
    if h : dstOff i ≤ x ∧ x < dstOff i + 4 then replyWords (hashReply o T i) ⟨x - dstOff i, by omega⟩
    else if h' : dstOff i + 20 ≤ x ∧ x < dstOff i + 24 then replyWords (hashReply o T i) ⟨x - dstOff i - 20, by omega⟩
    else T x

def hashTable (o : Oracle) (T : Nat → Word) : Nat → Nat → Word
  | 0 => T
  | i+1 => hashStep o (hashTable o T i) i

/-! ### Single fixed-oracle steps -/

theorem fixed_reg_val (s : MachineState) (rd : Reg) (v : Word) (r : Reg) :
    (putReg s rd v).getReg r = if rd = r ∧ rd ≠ .x0 then v else s.getReg r := by
  cases rd <;> cases r <;> rfl

theorem fixed_reg_mem (s : MachineState) (rd : Reg) (v : Word) (w : Nat) :
    memoryView (putReg s rd v) w = memoryView s w := by
  cases rd <;> rfl

theorem fixed_store_reg (s : MachineState) (a : Nat) (v : Word) (r : Reg) :
    (putWord s a v).getReg r = s.getReg r := by
  cases r <;> rfl

theorem fixed_store_mem (s : MachineState) (a : Nat) (v : Word) (w : Nat) (ha : a < 2^61) (hw : w < 2^61) :
    memoryView (putWord s a v) w = if w = a then v else memoryView s w := by
  have h := memory_at_store (state := s) (value := v) ha hw
  simp only [writeWord] at h
  exact h


/-! ### Lists of actions -/

theorem fixed_ops_append (o : Oracle) (a b : List Action) (s : MachineState) :
    fixedOps o (a ++ b) s = fixedOps o b (fixedOps o a s) := by
  simp [fixedOps, List.foldl_append]

theorem valid_fixed_append (o : Oracle) (a b : List Action) (s : MachineState)
    (ha : validFixed o a s) (hb : validFixed o b (fixedOps o a s)) : validFixed o (a ++ b) s := by
  induction a generalizing s with
  | nil => simpa [fixedOps] using hb
  | cons x rest ih =>
    exact ⟨ha.1, ih _ ha.2 (by simpa [fixedOps] using hb)⟩

theorem ops_rows_append (o : Oracle) (a b : List Action) (s : MachineState) :
    opsRows o (a ++ b) s = opsRows o a s ++ opsRows o b (fixedOps o a s) := by
  induction a generalizing s with
  | nil => simp [opsRows, fixedOps]
  | cons x rest ih => simp [opsRows, ih, fixedOps, List.append_assoc]

theorem op_calls_append (a b : List Action) : opCalls (a ++ b) = opCalls a + opCalls b := by
  simp [opCalls]

private theorem small_imm : ∀ m < 64, signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m) := by
  decide

theorem wa_offset (a m : Nat) (hm : m < 64) :
    wordAddress a + signExtend12 (BitVec.ofNat 12 (8*m)) = wordAddress (a+m) := by
  rw [small_imm m hm, wordAddress_add]; rfl

/-! ### The group copy into `HB` -/

def copyOps (i n : Nat) : List Action :=
  (List.range n).flatMap fun m =>
    [.load .x31 .x6 (BitVec.ofNat 12 (8*m)) (TBW+40*i+m), .store .x10 .x31 (BitVec.ofNat 12 (8*(5+m))) (HBW+5+m)]

theorem copy_ops_succ (i n : Nat) : copyOps i (n+1) = copyOps i n ++
    [.load .x31 .x6 (BitVec.ofNat 12 (8*n)) (TBW+40*i+n), .store .x10 .x31 (BitVec.ofNat 12 (8*(5+n))) (HBW+5+n)] := by
  simp [copyOps, List.range_succ, List.flatMap_append]

theorem copy_run (o : Oracle) (i : Nat) (hi : i < 54) : ∀ n ≤ 20, ∀ st : MachineState,
    st.getReg .x6 = wordAddress (TBW+40*i) → st.getReg .x10 = wordAddress HBW →
    validFixed o (copyOps i n) st ∧ opsRows o (copyOps i n) st = [] ∧ opCalls (copyOps i n) = 0 ∧
    (∀ r, r ≠ .x31 → (fixedOps o (copyOps i n) st).getReg r = st.getReg r) ∧
    ∀ w < 2^33, memoryView (fixedOps o (copyOps i n) st) w =
      if HBW+5 ≤ w ∧ w < HBW+5+n then memoryView st (TBW+40*i+(w-(HBW+5))) else memoryView st w := by
  have tw : TBW = 33554432 := rfl
  have hw : HBW = 67108864 := rfl
  intro n
  induction n with
  | zero =>
    intro _ st _ _
    refine ⟨trivial, rfl, rfl, fun _ _ => rfl, fun w _ => ?_⟩
    rw [if_neg (by omega)]; rfl
  | succ n ih =>
    intro le st x6 x10
    obtain ⟨v, rows, calls, regs, mem⟩ := ih (by omega) st x6 x10
    generalize hm : fixedOps o (copyOps i n) st = mid at v rows calls regs mem
    let a₁ : Action := .load .x31 .x6 (BitVec.ofNat 12 (8*n)) (TBW+40*i+n)
    let a₂ : Action := .store .x10 .x31 (BitVec.ofNat 12 (8*(5+n))) (HBW+5+n)
    have s₁ : fixedStep o mid a₁ = putReg mid .x31 (memoryView mid (TBW+40*i+n)) := rfl
    have s₂ : fixedStep o (fixedStep o mid a₁) a₂ =
        putWord (fixedStep o mid a₁) (HBW+5+n) ((fixedStep o mid a₁).getReg .x31) := rfl
    have r31 : (fixedStep o mid a₁).getReg .x31 = memoryView mid (TBW+40*i+n) := by
      rw [s₁, fixed_reg_val]; simp
    have whole : fixedOps o (copyOps i (n+1)) st = fixedStep o (fixedStep o mid a₁) a₂ := by
      rw [copy_ops_succ, fixed_ops_append, hm]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [copy_ops_succ]; apply valid_fixed_append o _ _ st v; rw [hm]
      refine ⟨⟨?_, by omega⟩, ⟨?_, by omega⟩, trivial⟩
      · rw [regs .x6 (by decide), x6, wa_offset _ _ (by omega)]
      · rw [s₁, fixed_reg_val, if_neg (by decide), regs .x10 (by decide), x10, wa_offset _ _ (by omega)]
        exact congrArg wordAddress (by omega)
    · rw [copy_ops_succ, ops_rows_append, rows, hm]; rfl
    · rw [copy_ops_succ, op_calls_append, calls]; rfl
    · intro r hr
      rw [whole, s₂, fixed_store_reg, s₁, fixed_reg_val, if_neg (by intro h; exact hr h.1.symm), regs r hr]
    · intro w hw'
      rw [whole, s₂, fixed_store_mem _ (HBW+5+n) _ w (by omega) (by omega), r31, s₁, fixed_reg_mem, mem w hw',
        mem (TBW+40*i+n) (by omega), if_neg (show ¬(HBW+5 ≤ TBW+40*i+n ∧ TBW+40*i+n < HBW+5+n) by omega)]
      by_cases h1 : w = HBW+5+n
      · rw [if_pos h1, if_pos (by omega), show TBW+40*i+(w-(HBW+5)) = TBW+40*i+n by omega]
      · rw [if_neg h1]
        by_cases h2 : HBW+5 ≤ w ∧ w < HBW+5+n
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]

/-! ### The digest copies out of `OB` -/

def outOps (i n : Nat) : List Action :=
  (List.range n).flatMap fun m =>
    [.load .x31 .x12 (BitVec.ofNat 12 (8*m)) (OBW+m), .store .x7 .x31 (BitVec.ofNat 12 (8*m)) (TBW+dstOff i+m),
     .store .x7 .x31 (BitVec.ofNat 12 (8*(20+m))) (TBW+dstOff i+20+m)]

theorem out_ops_succ (i n : Nat) : outOps i (n+1) = outOps i n ++
    [.load .x31 .x12 (BitVec.ofNat 12 (8*n)) (OBW+n), .store .x7 .x31 (BitVec.ofNat 12 (8*n)) (TBW+dstOff i+n),
     .store .x7 .x31 (BitVec.ofNat 12 (8*(20+n))) (TBW+dstOff i+20+n)] := by
  simp [outOps, List.range_succ, List.flatMap_append]

theorem dst_off_bound : ∀ i < 54, dstOff i + 24 ≤ 2200 := by decide

theorem out_run (o : Oracle) (i : Nat) (hi : i < 54) : ∀ n ≤ 4, ∀ st : MachineState,
    st.getReg .x7 = wordAddress (TBW+dstOff i) → st.getReg .x12 = wordAddress OBW →
    validFixed o (outOps i n) st ∧ opsRows o (outOps i n) st = [] ∧ opCalls (outOps i n) = 0 ∧
    (∀ r, r ≠ .x31 → (fixedOps o (outOps i n) st).getReg r = st.getReg r) ∧
    ∀ w < 2^33, memoryView (fixedOps o (outOps i n) st) w =
      if TBW+dstOff i ≤ w ∧ w < TBW+dstOff i+n then memoryView st (OBW+(w-(TBW+dstOff i)))
      else if TBW+dstOff i+20 ≤ w ∧ w < TBW+dstOff i+20+n then memoryView st (OBW+(w-(TBW+dstOff i+20)))
      else memoryView st w := by
  have tw : TBW = 33554432 := rfl
  have ow : OBW = 67108896 := rfl
  have db := dst_off_bound i hi
  intro n
  induction n with
  | zero =>
    intro _ st _ _
    refine ⟨trivial, rfl, rfl, fun _ _ => rfl, fun w _ => ?_⟩
    rw [if_neg (by omega), if_neg (by omega)]; rfl
  | succ n ih =>
    intro le st x7 x12
    obtain ⟨v, rows, calls, regs, mem⟩ := ih (by omega) st x7 x12
    generalize hm : fixedOps o (outOps i n) st = mid at v rows calls regs mem
    have whole : fixedOps o (outOps i (n+1)) st = fixedStep o (fixedStep o (fixedStep o mid
        (.load .x31 .x12 (BitVec.ofNat 12 (8*n)) (OBW+n))) (.store .x7 .x31 (BitVec.ofNat 12 (8*n)) (TBW+dstOff i+n)))
        (.store .x7 .x31 (BitVec.ofNat 12 (8*(20+n))) (TBW+dstOff i+20+n)) := by
      rw [out_ops_succ, fixed_ops_append, hm]; rfl
    have valid_eq : validFixed o ([.load .x31 .x12 (BitVec.ofNat 12 (8*n)) (OBW+n),
        .store .x7 .x31 (BitVec.ofNat 12 (8*n)) (TBW+dstOff i+n),
        .store .x7 .x31 (BitVec.ofNat 12 (8*(20+n))) (TBW+dstOff i+20+n)]) mid → validFixed o (outOps i (n+1)) st :=
      fun h => by rw [out_ops_succ]; exact valid_fixed_append o _ _ st v (by rw [hm]; exact h)
    generalize ht₁ : fixedStep o mid (.load .x31 .x12 (BitVec.ofNat 12 (8*n)) (OBW+n)) = t₁ at whole
    generalize ht₂ : fixedStep o t₁ (.store .x7 .x31 (BitVec.ofNat 12 (8*n)) (TBW+dstOff i+n)) = t₂ at whole
    have s₁ : t₁ = putReg mid .x31 (memoryView mid (OBW+n)) := by rw [← ht₁]; rfl
    have s₂ : t₂ = putWord t₁ (TBW+dstOff i+n) (t₁.getReg .x31) := by rw [← ht₂]; rfl
    have s₃ : fixedStep o t₂ (.store .x7 .x31 (BitVec.ofNat 12 (8*(20+n))) (TBW+dstOff i+20+n)) =
        putWord t₂ (TBW+dstOff i+20+n) (t₂.getReg .x31) := rfl
    have r31 : t₁.getReg .x31 = memoryView mid (OBW+n) := by rw [s₁, fixed_reg_val]; simp
    have r31' : t₂.getReg .x31 = memoryView mid (OBW+n) := by rw [s₂, fixed_store_reg, r31]
    have keep₁ (r : Reg) (hr : r ≠ .x31) : t₁.getReg r = mid.getReg r := by
      rw [s₁, fixed_reg_val, if_neg (by intro h; exact hr h.1.symm)]
    have keep₂ (r : Reg) (hr : r ≠ .x31) : t₂.getReg r = mid.getReg r := by
      rw [s₂, fixed_store_reg, keep₁ r hr]
    have ob : memoryView mid (OBW+n) = memoryView st (OBW+n) := by
      rw [mem _ (by omega), if_neg (by omega), if_neg (by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine valid_eq ?_
      refine ⟨⟨?_, by omega⟩, ?_⟩
      · rw [regs .x12 (by decide), x12, wa_offset _ _ (by omega)]
      rw [ht₁]
      refine ⟨⟨?_, by omega⟩, ?_⟩
      · rw [keep₁ .x7 (by decide), regs .x7 (by decide), x7, wa_offset _ _ (by omega)]
      rw [ht₂]
      refine ⟨⟨?_, by omega⟩, trivial⟩
      · rw [keep₂ .x7 (by decide), regs .x7 (by decide), x7, wa_offset _ _ (by omega)]
        exact congrArg wordAddress (by omega)
    · rw [out_ops_succ, ops_rows_append, rows, hm]; rfl
    · rw [out_ops_succ, op_calls_append, calls]; rfl
    · intro r hr
      rw [whole, s₃, fixed_store_reg, keep₂ r hr, regs r hr]
    · intro w hw'
      rw [whole, s₃, fixed_store_mem _ (TBW+dstOff i+20+n) _ w (by omega) (by omega), r31', s₂,
        fixed_store_mem _ (TBW+dstOff i+n) _ w (by omega) (by omega), r31, s₁, fixed_reg_mem, mem w hw', ob]
      split_ifs <;> first | omega | (congr 2; omega) | rfl

/-! ### One hash -/

def luiVal (imm : BitVec 20) : Word := (imm.zeroExtend 32 <<< 12).signExtend 64

def blockOps (i : Nat) : List Action :=
  [.lui .x6 (hi20 (hashSrc i)) (luiVal (hi20 (hashSrc i))),
   .offset .x6 .x6 (lo12 (hashSrc i)) (wordAddress (TBW+40*i))] ++ copyOps i 20 ++
  [.perm HBW OBW, .lui .x7 (hi20 (hashDst i)) (luiVal (hi20 (hashDst i))),
   .offset .x7 .x7 (lo12 (hashDst i)) (wordAddress (TBW+dstOff i))] ++ outOps i 4

theorem block_ops_code (i : Nat) : (blockOps i).map Action.op = hashBlock i := by
  simp [blockOps, hashBlock, copyOps, outOps, List.map_flatMap, Action.op]

set_option maxRecDepth 100000 in
theorem block_addresses : ∀ i < 54,
    luiVal (hi20 (hashSrc i)) + signExtend12 (lo12 (hashSrc i)) = wordAddress (TBW+40*i) ∧
    luiVal (hi20 (hashDst i)) + signExtend12 (lo12 (hashDst i)) = wordAddress (TBW+dstOff i) := by
  decide

structure HashReady (st : MachineState) : Prop where
  x10 : st.getReg .x10 = wordAddress HBW
  x11 : st.getReg .x11 = 200
  x12 : st.getReg .x12 = wordAddress OBW
  x13 : st.getReg .x13 = 1
  x5 : st.getReg .x5 = 0

def HashMem (T : Nat → Word) (st : MachineState) : Prop :=
  (∀ x < 2200, memoryView st (TBW + x) = T x) ∧ ∀ j < 5, memoryView st (HBW + j) = 0

theorem hash_ready_keep {a b : MachineState} (r : HashReady a)
    (same : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ .x31 → b.getReg x = a.getReg x) : HashReady b :=
  ⟨(same _ (by decide) (by decide) (by decide)).trans r.x10, (same _ (by decide) (by decide) (by decide)).trans r.x11,
   (same _ (by decide) (by decide) (by decide)).trans r.x12, (same _ (by decide) (by decide) (by decide)).trans r.x13,
   (same _ (by decide) (by decide) (by decide)).trans r.x5⟩

theorem block_run (o : Oracle) (i : Nat) (hi : i < 54) (T : Nat → Word) (st : MachineState)
    (ready : HashReady st) (mem : HashMem T st) :
    validFixed o (blockOps i) st ∧ opCalls (blockOps i) = 1 ∧ HashReady (fixedOps o (blockOps i) st) ∧
      HashMem (hashStep o T i) (fixedOps o (blockOps i) st) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x31 → (fixedOps o (blockOps i) st).getReg r = st.getReg r) ∧
      (∀ w < 2^33, (w < TBW ∨ TBW+2200 ≤ w) → (w < HBW+5 ∨ HBW+25 ≤ w) → (w < OBW ∨ OBW+25 ≤ w) →
        memoryView (fixedOps o (blockOps i) st) w = memoryView st w) := by
  have tw : TBW = 33554432 := rfl
  have hw : HBW = 67108864 := rfl
  have ow : OBW = 67108896 := rfl
  have db := dst_off_bound i hi
  obtain ⟨as, ad⟩ := block_addresses i hi
  -- pointer to the source group
  let s₁ := fixedStep o st (.lui .x6 (hi20 (hashSrc i)) (luiVal (hi20 (hashSrc i))))
  let s₂ := fixedStep o s₁ (.offset .x6 .x6 (lo12 (hashSrc i)) (wordAddress (TBW+40*i)))
  have r₂ (r : Reg) (h : r ≠ .x6) : s₂.getReg r = st.getReg r := by
    show (putReg (putReg st _ _) _ _).getReg r = _
    rw [fixed_reg_val, fixed_reg_val, if_neg (by intro e; exact h e.1.symm), if_neg (by intro e; exact h e.1.symm)]
  have x6₂ : s₂.getReg .x6 = wordAddress (TBW+40*i) := by
    show (putReg _ _ _).getReg _ = _
    rw [fixed_reg_val]; simp
  have m₂ (w : Nat) : memoryView s₂ w = memoryView st w := by
    show memoryView (putReg (putReg st _ _) _ _) w = _
    rw [fixed_reg_mem, fixed_reg_mem]
  -- copy
  obtain ⟨cv, crows, ccalls, cregs, cmem⟩ := copy_run o i hi 20 le_rfl s₂ x6₂ ((r₂ .x10 (by decide)).trans ready.x10)
  generalize hc : fixedOps o (copyOps i 20) s₂ = s₃ at cv crows ccalls cregs cmem
  have r₃ (r : Reg) (h6 : r ≠ .x6) (h31 : r ≠ .x31) : s₃.getReg r = st.getReg r := (cregs r h31).trans (r₂ r h6)
  have window₃ : (window (memoryView s₃) HBW : Words 25) = hashInput T i := by
    funext j
    have hj := j.isLt
    simp only [window, hashInput]
    rw [cmem _ (by omega)]
    by_cases low : j.val < 5
    · rw [if_neg (by omega), if_pos low, m₂, mem.2 j.val low]
    · rw [if_pos (by omega), if_neg low, m₂,
        show TBW + 40*i + (HBW + j.val - (HBW+5)) = TBW + (40*i + (j.val-5)) by omega, mem.1 _ (by omega)]
  -- the call
  let y := hashReply o T i
  let s₄ := fixedStep o s₃ (.perm HBW OBW)
  have r₄ (r : Reg) : s₄.getReg r = s₃.getReg r := writeBits_register ..
  have m₄ (w : Nat) (hw' : w < 2^33) : memoryView s₄ w = writeWindow (memoryView s₃) OBW (replyWords y) w := by
    show memoryView (writeBits s₃ (wordAddress OBW) (o.permutation (packBuffer (window (memoryView s₃) HBW)))) w = _
    rw [window₃]
    exact permutation_write_memory s₃ OBW w _ (by omega) hw'
  -- pointer to the slot
  let s₅ := fixedStep o s₄ (.lui .x7 (hi20 (hashDst i)) (luiVal (hi20 (hashDst i))))
  let s₆ := fixedStep o s₅ (.offset .x7 .x7 (lo12 (hashDst i)) (wordAddress (TBW+dstOff i)))
  have r₆ (r : Reg) (h : r ≠ .x7) : s₆.getReg r = s₄.getReg r := by
    show (putReg (putReg s₄ _ _) _ _).getReg r = _
    rw [fixed_reg_val, fixed_reg_val, if_neg (by intro e; exact h e.1.symm), if_neg (by intro e; exact h e.1.symm)]
  have x7₆ : s₆.getReg .x7 = wordAddress (TBW+dstOff i) := by
    show (putReg _ _ _).getReg _ = _
    rw [fixed_reg_val]; simp
  have m₆ (w : Nat) : memoryView s₆ w = memoryView s₄ w := by
    show memoryView (putReg (putReg s₄ _ _) _ _) w = _
    rw [fixed_reg_mem, fixed_reg_mem]
  have x12₆ : s₆.getReg .x12 = wordAddress OBW := by
    rw [r₆ _ (by decide), r₄, r₃ _ (by decide) (by decide), ready.x12]
  obtain ⟨ov, orows, ocalls, oregs, omem⟩ := out_run o i hi 4 le_rfl s₆ x7₆ x12₆
  generalize ho : fixedOps o (outOps i 4) s₆ = s₇ at ov orows ocalls oregs omem
  have whole : fixedOps o (blockOps i) st = s₇ := by
    have split : fixedOps o (blockOps i) st = fixedOps o (outOps i 4) (fixedOps o [.perm HBW OBW,
        .lui .x7 (hi20 (hashDst i)) (luiVal (hi20 (hashDst i))),
        .offset .x7 .x7 (lo12 (hashDst i)) (wordAddress (TBW+dstOff i))]
        (fixedOps o (copyOps i 20) (fixedOps o [.lui .x6 (hi20 (hashSrc i)) (luiVal (hi20 (hashSrc i))),
          .offset .x6 .x6 (lo12 (hashSrc i)) (wordAddress (TBW+40*i))] st))) := by
      simp only [blockOps, fixed_ops_append]
    rw [split, show fixedOps o [.lui .x6 (hi20 (hashSrc i)) (luiVal (hi20 (hashSrc i))),
          .offset .x6 .x6 (lo12 (hashSrc i)) (wordAddress (TBW+40*i))] st = s₂ from rfl, hc, ← ho]
    rfl
  have regs (r : Reg) (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h31 : r ≠ .x31) : s₇.getReg r = st.getReg r := by
    rw [oregs r h31, r₆ r h7, r₄, r₃ r h6 h31]
  rw [whole]
  refine ⟨?_, ?_, hash_ready_keep ready regs, ⟨?_, ?_⟩, regs, ?_⟩
  · simp only [blockOps]
    refine valid_fixed_append o _ _ st (valid_fixed_append o _ _ st ?_ ?_) ?_
    · refine valid_fixed_append o _ _ st ?_ ?_
      · exact ⟨rfl, ⟨by show (putReg st _ _).getReg .x6 + _ = _; rw [fixed_reg_val]; simpa using as, trivial⟩⟩
      · simpa [fixedOps] using cv
    · rw [show fixedOps o ([.lui .x6 (hi20 (hashSrc i)) (luiVal (hi20 (hashSrc i))),
          .offset .x6 .x6 (lo12 (hashSrc i)) (wordAddress (TBW+40*i))] ++ copyOps i 20) st = s₃ by
          rw [← hc, fixed_ops_append]; rfl]
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, by omega, by omega⟩, rfl, ⟨?_, trivial⟩⟩
      · rw [r₃ _ (by decide) (by decide), ready.x10]
      · rw [r₃ _ (by decide) (by decide), ready.x12]
      · rw [r₃ _ (by decide) (by decide), ready.x5]
      · rw [r₃ _ (by decide) (by decide), ready.x11]
      · rw [r₃ _ (by decide) (by decide), ready.x13]
      · show (putReg s₄ _ _).getReg .x7 + _ = _
        rw [fixed_reg_val]; simpa using ad
    · rw [show fixedOps o ([.lui .x6 (hi20 (hashSrc i)) (luiVal (hi20 (hashSrc i))),
          .offset .x6 .x6 (lo12 (hashSrc i)) (wordAddress (TBW+40*i))] ++ copyOps i 20 ++
          [.perm HBW OBW, .lui .x7 (hi20 (hashDst i)) (luiVal (hi20 (hashDst i))),
           .offset .x7 .x7 (lo12 (hashDst i)) (wordAddress (TBW+dstOff i))]) st = s₆ by
          rw [fixed_ops_append, fixed_ops_append, show fixedOps o [.lui .x6 (hi20 (hashSrc i)) (luiVal (hi20 (hashSrc i))),
            .offset .x6 .x6 (lo12 (hashSrc i)) (wordAddress (TBW+40*i))] st = s₂ from rfl, hc]; rfl]
      exact ov
  · simp only [opCalls] at ccalls ocalls
    simp [blockOps, op_calls_append, ccalls, ocalls, opCalls, Action.calls]
  · intro x hx
    rw [omem _ (by omega)]
    simp only [m₆]
    unfold hashStep
    by_cases lo : dstOff i ≤ x ∧ x < dstOff i + 4
    · rw [dif_pos lo, if_pos (show TBW + dstOff i ≤ TBW + x ∧ TBW + x < TBW + dstOff i + 4 by omega),
        m₄ _ (by omega)]
      simp only [writeWindow]
      rw [dif_pos (show OBW ≤ OBW + (TBW + x - (TBW + dstOff i)) ∧
        OBW + (TBW + x - (TBW + dstOff i)) < OBW + 25 by omega)]
      simp only [replyWords, y]
      exact congrArg (fun n => BitVec.extractLsb' (64*n) 64 (hashReply o T i)) (by omega)
    · rw [dif_neg lo, if_neg (show ¬(TBW + dstOff i ≤ TBW + x ∧ TBW + x < TBW + dstOff i + 4) by omega)]
      by_cases hi' : dstOff i + 20 ≤ x ∧ x < dstOff i + 24
      · rw [dif_pos hi', if_pos (show TBW + dstOff i + 20 ≤ TBW + x ∧ TBW + x < TBW + dstOff i + 20 + 4 by omega),
          m₄ _ (by omega)]
        simp only [writeWindow]
        rw [dif_pos (show OBW ≤ OBW + (TBW + x - (TBW + dstOff i + 20)) ∧
          OBW + (TBW + x - (TBW + dstOff i + 20)) < OBW + 25 by omega)]
        simp only [replyWords, y]
        exact congrArg (fun n => BitVec.extractLsb' (64*n) 64 (hashReply o T i)) (by omega)
      · rw [dif_neg hi', if_neg (show ¬(TBW + dstOff i + 20 ≤ TBW + x ∧ TBW + x < TBW + dstOff i + 20 + 4) by omega),
          m₄ _ (by omega)]
        simp only [writeWindow]
        rw [dif_neg (show ¬(OBW ≤ TBW + x ∧ TBW + x < OBW + 25) by omega), cmem _ (by omega),
          if_neg (show ¬(HBW + 5 ≤ TBW + x ∧ TBW + x < HBW + 5 + 20) by omega), m₂, mem.1 x hx]
  · intro j hj
    rw [omem _ (by omega), if_neg (show ¬(TBW + dstOff i ≤ HBW + j ∧ HBW + j < TBW + dstOff i + 4) by omega),
      if_neg (show ¬(TBW + dstOff i + 20 ≤ HBW + j ∧ HBW + j < TBW + dstOff i + 20 + 4) by omega), m₆,
      m₄ _ (by omega)]
    simp only [writeWindow]
    rw [dif_neg (show ¬(OBW ≤ HBW + j ∧ HBW + j < OBW + 25) by omega), cmem _ (by omega),
      if_neg (show ¬(HBW + 5 ≤ HBW + j ∧ HBW + j < HBW + 5 + 20) by omega), m₂, mem.2 j hj]
  · intro w hw' t h o'
    rw [omem w hw', if_neg (show ¬(TBW + dstOff i ≤ w ∧ w < TBW + dstOff i + 4) by omega),
      if_neg (show ¬(TBW + dstOff i + 20 ≤ w ∧ w < TBW + dstOff i + 20 + 4) by omega), m₆, m₄ w hw']
    simp only [writeWindow]
    rw [dif_neg (show ¬(OBW ≤ w ∧ w < OBW + 25) by omega), cmem w hw',
      if_neg (show ¬(HBW + 5 ≤ w ∧ w < HBW + 5 + 20) by omega), m₂]

/-! ### All 54 hashes -/

def blocksOps (n : Nat) : List Action := (List.range n).flatMap blockOps

theorem blocks_ops_succ (n : Nat) : blocksOps (n+1) = blocksOps n ++ blockOps n := by
  simp [blocksOps, List.range_succ, List.flatMap_append]

theorem blocks_run (o : Oracle) (T : Nat → Word) : ∀ n ≤ 54, ∀ st : MachineState, HashReady st → HashMem T st →
    validFixed o (blocksOps n) st ∧ opCalls (blocksOps n) = n ∧ HashReady (fixedOps o (blocksOps n) st) ∧
      HashMem (hashTable o T n) (fixedOps o (blocksOps n) st) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x31 → (fixedOps o (blocksOps n) st).getReg r = st.getReg r) ∧
      (∀ w < 2^33, (w < TBW ∨ TBW+2200 ≤ w) → (w < HBW+5 ∨ HBW+25 ≤ w) → (w < OBW ∨ OBW+25 ≤ w) →
        memoryView (fixedOps o (blocksOps n) st) w = memoryView st w) := by
  intro n
  induction n with
  | zero => intro _ st r m; exact ⟨trivial, rfl, r, m, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | succ n ih =>
    intro le st r m
    obtain ⟨v, c, r', m', regs, mem⟩ := ih (by omega) st r m
    obtain ⟨v₂, c₂, r₂, m₂, regs₂, mem₂⟩ := block_run o n (by omega) _ _ r' m'
    rw [blocks_ops_succ]
    refine ⟨valid_fixed_append o _ _ st v v₂, by rw [op_calls_append, c, c₂], ?_, ?_, ?_, ?_⟩ <;>
      rw [fixed_ops_append]
    · exact r₂
    · exact m₂
    · intro x a b d; rw [regs₂ x a b d, regs x a b d]
    · intro w hw a b d; rw [mem₂ w hw a b d, mem w hw a b d]

/-! ### Setup, clearing and restore -/

def setupOps (a10 a11 a12 a13 v6 : Word) : List Action :=
  [.offset .x18 .x10 0 a10, .offset .x19 .x11 0 a11, .offset .x20 .x12 0 a12, .offset .x21 .x13 0 a13,
   .lui .x10 131072 (luiVal 131072), .offset .x11 .x0 200 200, .lui .x12 131072 (luiVal 131072),
   .offset .x12 .x12 256 (wordAddress OBW), .offset .x13 .x0 1 1, .offset .x5 .x0 0 0, .offset .x22 .x6 0 v6]

def clearOps : List Action :=
  (List.range 20).map (fun m => .store .x10 .x0 (BitVec.ofNat 12 (8*(5+m))) (HBW+5+m)) ++
  (List.range 25).map (fun m => .store .x12 .x0 (BitVec.ofNat 12 (8*m)) (OBW+m))

def restoreOps (a10 a11 a12 a13 v6 a17 : Word) : List Action :=
  [.offset .x10 .x18 0 a10, .offset .x11 .x19 0 a11, .offset .x12 .x20 0 a12, .offset .x13 .x21 0 a13,
   .offset .x17 .x17 1824 (a17 + signExtend12 1824), .offset .x6 .x22 1920 (v6 + signExtend12 1920),
   .lui .x7 (hi20 (TABLE+17600)) (luiVal (hi20 (TABLE+17600))),
   .offset .x7 .x7 (lo12 (TABLE+17600)) (BitVec.ofNat 64 (TABLE+17600))]

def hashOps (a10 a11 a12 a13 v6 a17 : Word) : List Action :=
  setupOps a10 a11 a12 a13 v6 ++ blocksOps 54 ++ clearOps ++ restoreOps a10 a11 a12 a13 v6 a17

theorem hash_ops_code (a10 a11 a12 a13 v6 a17 : Word) :
    (hashOps a10 a11 a12 a13 v6 a17).map Action.op =
      hashSetup ++ (List.range 54).flatMap hashBlock ++ hashClear ++ hashRestore := by
  simp only [hashOps, List.map_append, blocksOps, List.map_flatMap, block_ops_code]
  rfl

theorem hash_ops_length (a10 a11 a12 a13 v6 a17 : Word) : (hashOps a10 a11 a12 a13 v6 a17).length = 3142 := by
  have h := congrArg List.length (hash_ops_code a10 a11 a12 a13 v6 a17)
  rw [List.length_map] at h
  rw [h]; decide

theorem lui_hb : luiVal 131072 = wordAddress HBW := by decide
theorem lui_table : luiVal (hi20 (TABLE+17600)) + signExtend12 (lo12 (TABLE+17600)) =
    BitVec.ofNat 64 (TABLE+17600) := by decide

theorem setup_run (o : Oracle) (st : MachineState) (a10 a11 a12 a13 v6 : Word)
    (x10 : st.getReg .x10 = a10) (x11 : st.getReg .x11 = a11) (x12 : st.getReg .x12 = a12)
    (x13 : st.getReg .x13 = a13) (x6 : st.getReg .x6 = v6) :
    let t := fixedOps o (setupOps a10 a11 a12 a13 v6) st
    validFixed o (setupOps a10 a11 a12 a13 v6) st ∧ opCalls (setupOps a10 a11 a12 a13 v6) = 0 ∧ HashReady t ∧
      t.getReg .x18 = a10 ∧ t.getReg .x19 = a11 ∧ t.getReg .x20 = a12 ∧ t.getReg .x21 = a13 ∧ t.getReg .x22 = v6 ∧
      (∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x18 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 →
        r ≠ .x22 → t.getReg r = st.getReg r) ∧ ∀ w, memoryView t w = memoryView st w := by
  intro t
  have z : st.getReg .x0 = 0#64 := rfl
  have zero12 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [t, setupOps, fixedOps, fixedStep, validFixed, Action.valid, fixed_reg_val, fixed_reg_mem, x10, x11, x12,
      x13, x6, z, zero12, lui_hb] <;> first | decide | skip
  intro r a b c d e f g h i j
  simp [t, setupOps, fixedOps, fixedStep, fixed_reg_val, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e,
    Ne.symm f, Ne.symm g, Ne.symm h, Ne.symm i, Ne.symm j]


def zeroOps (b : Reg) (S c n : Nat) : List Action :=
  (List.range n).map (fun m => .store b .x0 (BitVec.ofNat 12 (8*(c+m))) (S+(c+m)))

theorem zero_run (o : Oracle) (b : Reg) (S c : Nat) (hS : S + 64 < 2^33) : ∀ n, c + n ≤ 64 → ∀ st : MachineState,
    st.getReg b = wordAddress S →
    validFixed o (zeroOps b S c n) st ∧ opCalls (zeroOps b S c n) = 0 ∧
      (∀ r, (fixedOps o (zeroOps b S c n) st).getReg r = st.getReg r) ∧
      ∀ w < 2^33, memoryView (fixedOps o (zeroOps b S c n) st) w =
        if S+c ≤ w ∧ w < S+c+n then 0 else memoryView st w := by
  intro n
  induction n with
  | zero =>
    intro _ st _
    refine ⟨trivial, rfl, fun _ => rfl, fun w _ => ?_⟩
    rw [if_neg (by omega)]; rfl
  | succ n ih =>
    intro le st hb
    obtain ⟨v, c₀, regs, mem⟩ := ih (by omega) st hb
    have split : zeroOps b S c (n+1) = zeroOps b S c n ++ [.store b .x0 (BitVec.ofNat 12 (8*(c+n))) (S+(c+n))] := by
      simp [zeroOps, List.range_succ]
    generalize hm : fixedOps o (zeroOps b S c n) st = mid at v c₀ regs mem
    rw [split]
    refine ⟨valid_fixed_append o _ _ st v ?_, ?_, ?_, ?_⟩
    · rw [hm]
      exact ⟨⟨by rw [regs, hb, wa_offset _ _ (by omega)], by omega⟩, trivial⟩
    · rw [op_calls_append, c₀]; rfl
    · intro r
      rw [fixed_ops_append, hm]
      exact (fixed_store_reg mid _ _ r).trans (regs r)
    · intro w hw
      rw [fixed_ops_append, hm]
      show memoryView (putWord mid (S+(c+n)) (mid.getReg .x0)) w = _
      rw [fixed_store_mem _ _ _ _ (by omega) (by omega), mem w hw]
      by_cases e : w = S+(c+n)
      · rw [if_pos e, if_pos (show S+c ≤ w ∧ w < S+c+(n+1) by omega)]; rfl
      · rw [if_neg e]
        by_cases a : S+c ≤ w ∧ w < S+c+n
        · rw [if_pos a, if_pos (show S+c ≤ w ∧ w < S+c+(n+1) by omega)]
        · rw [if_neg a, if_neg (show ¬(S+c ≤ w ∧ w < S+c+(n+1)) by omega)]

theorem clear_ops_eq : clearOps = zeroOps .x10 HBW 5 20 ++ zeroOps .x12 OBW 0 25 := by
  simp [clearOps, zeroOps, Nat.add_assoc]

theorem clear_run (o : Oracle) (st : MachineState) (ready : HashReady st) :
    validFixed o clearOps st ∧ opCalls clearOps = 0 ∧
      (∀ r, (fixedOps o clearOps st).getReg r = st.getReg r) ∧
      ∀ w < 2^33, memoryView (fixedOps o clearOps st) w =
        if (HBW+5 ≤ w ∧ w < HBW+25) ∨ (OBW ≤ w ∧ w < OBW+25) then 0 else memoryView st w := by
  have hw : HBW = 67108864 := rfl
  have ow : OBW = 67108896 := rfl
  obtain ⟨v₁, c₁, r₁, m₁⟩ := zero_run o .x10 HBW 5 (by omega) 20 (by omega) st ready.x10
  generalize h₁ : fixedOps o (zeroOps .x10 HBW 5 20) st = s₁ at v₁ c₁ r₁ m₁
  obtain ⟨v₂, c₂, r₂, m₂⟩ := zero_run o .x12 OBW 0 (by omega) 25 (by omega) s₁ ((r₁ _).trans ready.x12)
  rw [clear_ops_eq]
  refine ⟨valid_fixed_append o _ _ st v₁ (by rw [h₁]; exact v₂), by rw [op_calls_append, c₁, c₂], ?_, ?_⟩
  · intro r; rw [fixed_ops_append, h₁, r₂, r₁]
  · intro w hw'
    rw [fixed_ops_append, h₁, m₂ w hw', m₁ w hw']
    split_ifs <;> first | rfl | omega

theorem restore_run' (o : Oracle) (st : MachineState) (a10 a11 a12 a13 v6 a17 : Word)
    (x18 : st.getReg .x18 = a10) (x19 : st.getReg .x19 = a11) (x20 : st.getReg .x20 = a12)
    (x21 : st.getReg .x21 = a13) (x22 : st.getReg .x22 = v6) (x17 : st.getReg .x17 = a17) :
    let t := fixedOps o (restoreOps a10 a11 a12 a13 v6 a17) st
    validFixed o (restoreOps a10 a11 a12 a13 v6 a17) st ∧ opCalls (restoreOps a10 a11 a12 a13 v6 a17) = 0 ∧
      t.getReg .x10 = a10 ∧ t.getReg .x11 = a11 ∧ t.getReg .x12 = a12 ∧ t.getReg .x13 = a13 ∧
      t.getReg .x17 = a17 + signExtend12 1824 ∧ t.getReg .x6 = v6 + signExtend12 1920 ∧
      t.getReg .x7 = BitVec.ofNat 64 (TABLE+17600) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x17 →
        t.getReg r = st.getReg r) ∧ ∀ w, memoryView t w = memoryView st w := by
  intro t
  have zero12 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [t, restoreOps, fixedOps, fixedStep, validFixed, Action.valid, fixed_reg_val, fixed_reg_mem, x18, x19, x20,
      x21, x22, x17, zero12, lui_table]
  all_goals first
    | exact ⟨by decide, rfl⟩
    | intro r a b c d e f g
      simp [Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm f, Ne.symm g]

/-! ### The whole hash phase -/

theorem fixed_ops_pc (o : Oracle) : ∀ (ops : List Action) (s : MachineState),
    (fixedOps o ops s).pc = s.pc + BitVec.ofNat 64 (4*ops.length)
  | [], s => by simp [fixedOps]
  | a :: rest, s => by
    rw [show fixedOps o (a :: rest) s = fixedOps o rest (fixedStep o s a) from rfl, fixed_ops_pc o rest, fixed_pc,
      BitVec.add_assoc]
    congr 1
    rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 1
    simp; omega

theorem wrap_code_prefix : ∃ head : List Instr, head.length = 315 ∧ wrapCode = head ++ hashCode :=
  ⟨_, by decide, rfl⟩

theorem wrap_hash (a10 a11 a12 a13 v6 a17 : Word) (i : Nat) (hi : i < 3142) :
    wrapCode[315+i]? = ((hashOps a10 a11 a12 a13 v6 a17).map Action.op)[i]? := by
  obtain ⟨head, len, split⟩ := wrap_code_prefix
  have hx : (hashSetup ++ (List.range 54).flatMap hashBlock ++ hashClear ++ hashRestore).length = 3142 := by
    rw [← hash_ops_code a10 a11 a12 a13 v6 a17, List.length_map, hash_ops_length]
  rw [split, List.getElem?_append_right (by omega), len, Nat.add_sub_cancel_left, hash_ops_code]
  show (hashSetup ++ (List.range 54).flatMap hashBlock ++ hashClear ++ hashRestore ++ constantCode ++
    [.JAL .x0 2083700])[i]? = _
  rw [List.getElem?_append_left (by simp only [List.length_append] at hx ⊢; omega),
    List.getElem?_append_left (by simp only [List.length_append] at hx ⊢; omega)]

theorem hash_fetch {img : Image} (wrap : WrapImage img) (a10 a11 a12 a13 v6 a17 : Word) :
    fetchOps img (460+315) (hashOps a10 a11 a12 a13 v6 a17) := by
  intro i s pc
  have bound : i.val < 3142 := by
    have h1 := i.isLt
    have h2 := hash_ops_length a10 a11 a12 a13 v6 a17
    omega
  apply wrap_fetch wrap s (315+i.val)
  · rw [wrap_hash a10 a11 a12 a13 v6 a17 i.val bound, List.getElem?_map, List.getElem?_eq_getElem i.isLt]
    rfl
  · rw [pc]; congr 1; omega

theorem hash_phase (o : Oracle) {img : Image} (wrap : WrapImage img) (st : MachineState)
    (pc : st.pc = BitVec.ofNat 64 (4096+4*(460+315))) (T : Nat → Word)
    (tbl : ∀ x < 2200, memoryView st (TBW+x) = T x) (hb : ∀ j < 25, memoryView st (HBW+j) = 0)
    (ob : ∀ j < 25, memoryView st (OBW+j) = 0) (a10 a11 a12 a13 v6 a17 : Word)
    (x10 : st.getReg .x10 = a10) (x11 : st.getReg .x11 = a11) (x12 : st.getReg .x12 = a12)
    (x13 : st.getReg .x13 = a13) (x6 : st.getReg .x6 = v6) (x17 : st.getReg .x17 = a17) (fuel : Nat) :
    let ops := hashOps a10 a11 a12 a13 v6 a17
    let t := fixedOps o ops st
    (checkEvaluation o (recordRows (execute img (3142 + fuel) st false)) =
      let tail := checkEvaluation o (recordRows (execute img fuel t false))
      ((tail.1.1.charge (3142 + 7 * 54) 54, opsRows o ops st ++ tail.1.2), 54 + tail.2)) ∧
    t.pc = BitVec.ofNat 64 (4096+4*(460+3457)) ∧
    t.getReg .x10 = a10 ∧ t.getReg .x11 = a11 ∧ t.getReg .x12 = a12 ∧ t.getReg .x13 = a13 ∧
    t.getReg .x17 = a17 + signExtend12 1824 ∧ t.getReg .x6 = v6 + signExtend12 1920 ∧
    t.getReg .x7 = BitVec.ofNat 64 (TABLE+17600) ∧
    (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x17 → r ≠ .x18 →
      r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x31 → t.getReg r = st.getReg r) ∧
    (∀ x < 2200, memoryView t (TBW+x) = hashTable o T 54 x) ∧
    (∀ w < 2^33, (w < TBW ∨ TBW+2200 ≤ w) → memoryView t w = memoryView st w) := by
  intro ops t
  have hw : HBW = 67108864 := rfl
  have ow : OBW = 67108896 := rfl
  have tw : TBW = 33554432 := rfl
  obtain ⟨v₁, c₁, ready₁, y18, y19, y20, y21, y22, regs₁, mem₁⟩ := setup_run o st a10 a11 a12 a13 v6 x10 x11 x12 x13 x6
  generalize h₁ : fixedOps o (setupOps a10 a11 a12 a13 v6) st = s₁ at v₁ c₁ ready₁ y18 y19 y20 y21 y22 regs₁ mem₁
  obtain ⟨v₂, c₂, ready₂, hm₂, regs₂, mem₂⟩ := blocks_run o T 54 le_rfl s₁ ready₁
    ⟨fun x hx => by rw [mem₁, tbl x hx], fun j hj => by rw [mem₁, hb j (by omega)]⟩
  generalize h₂ : fixedOps o (blocksOps 54) s₁ = s₂ at v₂ c₂ ready₂ hm₂ regs₂ mem₂
  obtain ⟨v₃, c₃, regs₃, mem₃⟩ := clear_run o s₂ ready₂
  generalize h₃ : fixedOps o clearOps s₂ = s₃ at v₃ c₃ regs₃ mem₃
  have k₃ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x31) : s₃.getReg r = s₁.getReg r :=
    (regs₃ r).trans (regs₂ r a b c)
  obtain ⟨v₄, c₄, z10, z11, z12, z13, z17, z6, z7, regs₄, mem₄⟩ := restore_run' o s₃ a10 a11 a12 a13 v6 a17
    ((k₃ _ (by decide) (by decide) (by decide)).trans y18) ((k₃ _ (by decide) (by decide) (by decide)).trans y19)
    ((k₃ _ (by decide) (by decide) (by decide)).trans y20) ((k₃ _ (by decide) (by decide) (by decide)).trans y21)
    ((k₃ _ (by decide) (by decide) (by decide)).trans y22)
    ((k₃ _ (by decide) (by decide) (by decide)).trans ((regs₁ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans x17))
  have whole : t = fixedOps o (restoreOps a10 a11 a12 a13 v6 a17) s₃ := by
    show fixedOps o (hashOps a10 a11 a12 a13 v6 a17) st = _
    simp only [hashOps, fixed_ops_append, h₁, h₂, h₃]
  have valid : validFixed o ops st :=
    valid_fixed_append o _ _ st (valid_fixed_append o _ _ st (valid_fixed_append o _ _ st v₁ (by rw [h₁]; exact v₂))
      (by rw [fixed_ops_append, h₁, h₂]; exact v₃)) (by rw [fixed_ops_append, fixed_ops_append, h₁, h₂, h₃]; exact v₄)
  have calls : opCalls ops = 54 := by
    simp only [ops, hashOps, op_calls_append, c₁, c₂, c₃, c₄]
  have len : ops.length = 3142 := hash_ops_length _ _ _ _ _ _
  refine ⟨?_, ?_, by rw [whole]; exact z10, by rw [whole]; exact z11, by rw [whole]; exact z12,
    by rw [whole]; exact z13, by rw [whole]; exact z17, by rw [whole]; exact z6, by rw [whole]; exact z7, ?_, ?_, ?_⟩
  · have obs := observe_ops o img ops (460+315) fuel st pc (hash_fetch wrap a10 a11 a12 a13 v6 a17) valid
    rw [len, calls] at obs
    exact obs
  · show (fixedOps o ops st).pc = _
    rw [fixed_ops_pc, len, pc, ← BitVec.ofNat_add]
  · intro r a b c d e f g h i j k l m n
    rw [whole, regs₄ r b c d e f g h, regs₃ r, regs₂ r b c n, regs₁ r a d e f g i j k l m]
  · intro x hx
    rw [whole, mem₄, mem₃ _ (by omega), if_neg (by omega)]
    exact hm₂.1 x hx
  · intro w hw' side
    rw [whole, mem₄, mem₃ w hw']
    by_cases scratch : (HBW+5 ≤ w ∧ w < HBW+25) ∨ (OBW ≤ w ∧ w < OBW+25)
    · rw [if_pos scratch]
      rcases scratch with a | a
      · have := hb (w - HBW) (by omega)
        rw [show HBW + (w - HBW) = w by omega] at this
        exact this.symm
      · have := ob (w - OBW) (by omega)
        rw [show OBW + (w - OBW) = w by omega] at this
        exact this.symm
    · rw [if_neg scratch, mem₂ w hw' side (by omega) (by omega), mem₁]

end TwoPermutationPrototype.PentaWrap



