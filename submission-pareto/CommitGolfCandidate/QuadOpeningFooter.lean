import CommitGolfCandidate.QuadOpeningRecord

/-! The level-7 table copy of the cap opener (words 106 and 527-2820). After the last record the
latch falls through to word 106, which jumps to word 527. The footer copies the 43 level-7 groups
(160 bytes each, at `pentaGroupBase 7 + 40 + 368 g`) through the permutation: 43 forward calls
write `P(group g)` to a scratch area 8,192 bytes past the table start, then 43 inverse calls write
`P⁻¹(P(group g)) = group g` to the proof at `160 g` past the table start. Each 200-byte reply
also covers the next 40 bytes, which the following group overwrites. The exit follows at
words 796-799. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

/-! ### Table layout -/

/-- First table group of table level `L` (trapdoor level `7 + L`). -/
def tableFirst (L : Nat) : Nat := match L with | 0 => 0 | 1 => 43 | 2 => 52 | _ => 54

/-- Table level of table group `G < 55`. -/
def tableLevel (G : Nat) : Nat := if G < 43 then 0 else if G < 52 then 1 else if G < 54 then 2 else 3

/-- Initial address of table doubleword `x < 1100`: doubleword `x % 4` of slot `x % 20 / 4` of
group `x / 20 - tableFirst L` of level `7 + L`. -/
def tableSource (x : Nat) : Nat :=
  trapdoorBase + pentaSlotOffset (7 + tableLevel (x/20)) (5*(x/20 - tableFirst (tableLevel (x/20))) + x%20/4) +
    8*(x%4)

/-- Source of output doubleword `u`: the records, then the table. -/
def proofSource (positions : Positions) (u : Nat) : Nat :=
  if u < 142*positions.card then wordSource positions u else tableSource (u - 142*positions.card)

theorem penta_counts : pentaCount 8 = 43 ∧ pentaCount 9 = 9 ∧ pentaCount 10 = 2 ∧ pentaCount 11 = 1 := by
  decide

theorem table_first_next (L : Nat) (hL : L < 4) :
    tableFirst L + pentaCount (7+L+1) = if L = 3 then 55 else tableFirst (L+1) := by
  obtain ⟨c8, c9, c10, c11⟩ := penta_counts
  interval_cases L <;> simp [tableFirst, c8, c9, c10, c11]

theorem table_level_first (L g : Nat) (hL : L < 4) (hg : g < pentaCount (7+L+1)) :
    tableLevel (tableFirst L + g) = L := by
  obtain ⟨c8, c9, c10, c11⟩ := penta_counts
  interval_cases L <;> simp only [Nat.reduceAdd, c8, c9, c10, c11] at hg <;>
    simp only [tableFirst, tableLevel] <;> split_ifs <;> omega

theorem table_source_group (L g m : Nat) (hL : L < 4) (hg : g < pentaCount (7+L+1)) (hm : m < 20) :
    tableSource (20*(tableFirst L + g) + m) = trapdoorBase + pentaGroupBase (7+L) + 40 + 368*g + 8*m := by
  unfold tableSource
  rw [show (20*(tableFirst L + g) + m)/20 = tableFirst L + g by omega,
    show (20*(tableFirst L + g) + m)%20 = m by omega, table_level_first L g hL hg, Nat.add_sub_cancel_left]
  unfold pentaSlotOffset
  rw [show (5*g + m/4)/5 = g by omega, show (5*g + m/4)%5 = m/4 by omega]
  omega


theorem group_aligned' : ∀ L < 4, (pentaGroupBase (7+L)+40) % 8 = 0 := by decide

/-! ### Code layout -/

set_option maxRecDepth 100000 in
theorem footer_length : footerCode.length = 2294 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The table copy occupies words 527-2820; the level-specialized copy variants follow it. -/
theorem program_split : ∃ head tail : List Instr, head.length = 527 ∧ program = head ++ footerCode ++ tail := by
  refine ⟨setupCode ++ recCode ++
    [footerJump] ++ List.replicate 41 (.ADDI .x0 .x0 0) ++ exitCode ++ List.replicate 7 (.ADDI .x0 .x0 0) ++
    (List.range 5).flatMap variantCode ++ prefixCode,
    (List.replicate 251 (.ADDI .x0 .x0 0) ++
      (List.range 7).flatMap (fun k => (List.range 5).flatMap (levelVariantCode k))) ++
    List.replicate 832 (.ADDI .x0 .x0 0) ++ pairsList, by decide, ?_⟩
  simp only [program, List.append_assoc]

theorem program_footer (i : Nat) (hi : i < 2294) : program[527+i]? = footerCode[i]? := by
  obtain ⟨head, tail, len, split⟩ := program_split
  rw [split, List.append_assoc, List.getElem?_append_right (by omega), len, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [footer_length]; exact hi)]

/-- `code` sits at footer offset `start`. -/
def FootAt (start : Nat) (code : List Instr) : Prop := ∀ i < code.length, footerCode[start+i]? = code[i]?

instance (start : Nat) (code : List Instr) : Decidable (FootAt start code) := by
  unfold FootAt
  infer_instance

theorem code_of_foot {start : Nat} {code : List Instr} (h : FootAt start code)
    (fits : start + code.length ≤ 2294) : CodeAt (527+start) code := by
  intro i hi
  rw [Nat.add_assoc, program_footer _ (by omega)]
  exact h i hi

set_option maxRecDepth 100000 in
theorem foot_codes : FootAt 0 footHead ∧ (∀ g < 42, FootAt (7+3*g) fwdBlock) ∧ FootAt 133 footMid ∧
    (∀ g < 42, FootAt (138+3*g) invBlock) ∧ FootAt 264 lastCode ∧ FootAt 304 footExit := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem jump_code : program[106]? = some footerJump := by decide +kernel

theorem head_code : CodeAt 527 footHead := code_of_foot foot_codes.1 (by decide)
theorem fwd_code (g : Nat) (hg : g < 42) : CodeAt (534+3*g) fwdBlock := by
  have h := code_of_foot (foot_codes.2.1 g hg) (by simp [fwdBlock]; omega)
  rw [show 534+3*g = 527+(7+3*g) by omega]; exact h
theorem mid_code : CodeAt 660 footMid := code_of_foot foot_codes.2.2.1 (by decide)
theorem inv_code (g : Nat) (hg : g < 42) : CodeAt (665+3*g) invBlock := by
  have h := code_of_foot (foot_codes.2.2.2.1 g hg) (by simp [invBlock]; omega)
  rw [show 665+3*g = 527+(138+3*g) by omega]; exact h
theorem last_code : CodeAt 791 lastCode := code_of_foot foot_codes.2.2.2.2.1 (by decide)
theorem exit_code : CodeAt 831 footExit := code_of_foot foot_codes.2.2.2.2.2 (by decide)

theorem code_tail {start : Nat} {first : Instr} {rest : List Instr} (code : CodeAt start (first :: rest)) :
    CodeAt (start+1) rest := by
  intro i hi
  have := code (i+1) (by simp; omega)
  simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem code_head {start : Nat} {first : Instr} {rest : List Instr} (code : CodeAt start (first :: rest)) :
    program[start]? = some first := by
  simpa using code 0 (by simp)

/-! ### Syscall steps -/

/-! ### Forward and inverse blocks -/

open TwoPermutationPrototype.RV64 OracleComp

def fwdAdv (t : MachineState) : MachineState :=
  ([.ADDI .x10 .x10 368, .ADDI .x12 .x12 200] : List Instr).foldl execInstrBr t

def invAdv (t : MachineState) : MachineState :=
  ([.ADDI .x10 .x10 200, .ADDI .x12 .x12 160] : List Instr).foldl execInstrBr t

theorem fwd_adv_regs (t : MachineState) :
    (fwdAdv t).getReg .x10 = t.getReg .x10 + wordAddress 46 ∧
    (fwdAdv t).getReg .x12 = t.getReg .x12 + wordAddress 25 ∧
    (fwdAdv t).mem = t.mem ∧ (fwdAdv t).pc = t.pc + 8 ∧
    ∀ r, r ≠ .x10 → r ≠ .x12 → (fwdAdv t).getReg r = t.getReg r := by
  refine ⟨?_, ?_, pure_mem _ _ rfl, ?_, ?_⟩
  · simp [fwdAdv, execInstrBr, signExtend12]; rfl
  · simp [fwdAdv, execInstrBr, signExtend12]; rfl
  · rw [fwdAdv, pure_pc _ _ rfl]; rfl
  · intro r a b
    simp [fwdAdv, execInstrBr, Ne.symm a, Ne.symm b]

theorem inv_adv_regs (t : MachineState) :
    (invAdv t).getReg .x10 = t.getReg .x10 + wordAddress 25 ∧
    (invAdv t).getReg .x12 = t.getReg .x12 + wordAddress 20 ∧
    (invAdv t).mem = t.mem ∧ (invAdv t).pc = t.pc + 8 ∧
    ∀ r, r ≠ .x10 → r ≠ .x12 → (invAdv t).getReg r = t.getReg r := by
  refine ⟨?_, ?_, pure_mem _ _ rfl, ?_, ?_⟩
  · simp [invAdv, execInstrBr, signExtend12]; rfl
  · simp [invAdv, execInstrBr, signExtend12]; rfl
  · rw [invAdv, pure_pc _ _ rfl]; rfl
  · intro r a b
    simp [invAdv, execInstrBr, Ne.symm a, Ne.symm b]

/-- Registers at the start of forward block `g`. -/
structure FwdAt (S T g : Nat) (s : MachineState) : Prop where
  pc : s.pc = BitVec.ofNat 64 (4096+4*(534+3*g))
  src : s.getReg .x10 = wordAddress (S+46*g)
  dst : s.getReg .x12 = wordAddress (T+25*g)
  sel : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  prim : s.getReg .x13 = 1

/-- Registers at the start of inverse block `g`. -/
structure InvAt (A D g : Nat) (s : MachineState) : Prop where
  pc : s.pc = BitVec.ofNat 64 (4096+4*(665+3*g))
  src : s.getReg .x10 = wordAddress (A+25*g)
  dst : s.getReg .x12 = wordAddress (D+20*g)
  sel : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  prim : s.getReg .x13 = 2

theorem fwd_step (S T g fuel : Nat) (s : MachineState) (hg : g < 42) (at_ : FwdAt S T g s)
    (sb : S+46*g+25 ≤ 2^33) (tb : T+25*g+25 ≤ 2^33) :
    execute openingImage (3+fuel) s true = (do
      let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (S+46*g))))))
      let r ← execute openingImage fuel (fwdAdv (writeBits s (wordAddress (T+25*g)) y)) true
      pure (r.charge 10 1)) := by
  have code := fwd_code g hg
  have fetched : fetch openingImage s = some (.base .ECALL) :=
    fetch_program s (534+3*g) .ECALL (code_head code) at_.pc
  rw [show 3+fuel = (2+fuel)+1 by omega,
    execute_permutation_call openingImage (2+fuel) s true (S+46*g) (T+25*g) sb tb at_.src at_.dst
      at_.sel at_.size at_.prim fetched]
  apply bind_congr; intro y
  have pcw : (writeBits s (wordAddress (T+25*g)) y).pc = BitVec.ofNat 64 (4096+4*(534+3*g+1)) := by
    rw [write_pc, pc_next _ _ at_.pc]
  have run : Runs _ (fwdAdv (writeBits s (wordAddress (T+25*g)) y)) 2 2 :=
    (runs_pure _ _ _ (code_tail code) pcw rfl).cast rfl rfl
  rw [run fuel true]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro r
  rw [charge_merge]

theorem inv_step (A D g fuel : Nat) (s : MachineState) (hg : g < 42) (at_ : InvAt A D g s)
    (ab : A+25*g+25 ≤ 2^33) (db : D+20*g+25 ≤ 2^33) :
    execute openingImage (3+fuel) s true = (do
      let y ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView s) (A+25*g))))))
      let r ← execute openingImage fuel (invAdv (writeBits s (wordAddress (D+20*g)) y)) true
      pure (r.charge 10 1)) := by
  have code := inv_code g hg
  have fetched : fetch openingImage s = some (.base .ECALL) :=
    fetch_program s (665+3*g) .ECALL (code_head code) at_.pc
  rw [show 3+fuel = (2+fuel)+1 by omega,
    execute_inverse_call openingImage (2+fuel) s true (A+25*g) (D+20*g) ab db at_.src at_.dst
      at_.sel at_.size at_.prim fetched]
  apply bind_congr; intro y
  have pcw : (writeBits s (wordAddress (D+20*g)) y).pc = BitVec.ofNat 64 (4096+4*(665+3*g+1)) := by
    rw [write_pc, pc_next _ _ at_.pc]
  have run : Runs _ (invAdv (writeBits s (wordAddress (D+20*g)) y)) 2 2 :=
    (runs_pure _ _ _ (code_tail code) pcw rfl).cast rfl rfl
  rw [run fuel true]
  simp only [bind_assoc, pure_bind]
  apply bind_congr; intro r
  rw [charge_merge]

theorem fwd_next {bits : Nat} (S T g : Nat) (s : MachineState) (at_ : FwdAt S T g s) (y : BitVec bits) :
    FwdAt S T (g+1) (fwdAdv (writeBits s (wordAddress (T+25*g)) y)) ∧
      ∀ r, r ≠ .x10 → r ≠ .x12 → (fwdAdv (writeBits s (wordAddress (T+25*g)) y)).getReg r = s.getReg r := by
  obtain ⟨a10, a12, _, apc, keep⟩ := fwd_adv_regs (writeBits s (wordAddress (T+25*g)) y)
  have w (r : Reg) := writeBits_register s (wordAddress (T+25*g)) y r
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun r a b => (keep r a b).trans (w r)⟩
  · rw [apc, write_pc, at_.pc, BitVec.add_assoc]
    rw [show (4 : Word) + 8 = BitVec.ofNat 64 12 from rfl, ← BitVec.ofNat_add]
    congr 1
  · rw [a10, w, at_.src, ← wordAddress_add]; congr 1
  · rw [a12, w, at_.dst, ← wordAddress_add]; congr 1
  · rw [keep _ (by decide) (by decide), w, at_.sel]
  · rw [keep _ (by decide) (by decide), w, at_.size]
  · rw [keep _ (by decide) (by decide), w, at_.prim]

theorem inv_next {bits : Nat} (A D g : Nat) (s : MachineState) (at_ : InvAt A D g s) (y : BitVec bits) :
    InvAt A D (g+1) (invAdv (writeBits s (wordAddress (D+20*g)) y)) ∧
      ∀ r, r ≠ .x10 → r ≠ .x12 → (invAdv (writeBits s (wordAddress (D+20*g)) y)).getReg r = s.getReg r := by
  obtain ⟨a10, a12, _, apc, keep⟩ := inv_adv_regs (writeBits s (wordAddress (D+20*g)) y)
  have w (r : Reg) := writeBits_register s (wordAddress (D+20*g)) y r
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun r a b => (keep r a b).trans (w r)⟩
  · rw [apc, write_pc, at_.pc, BitVec.add_assoc]
    rw [show (4 : Word) + 8 = BitVec.ofNat 64 12 from rfl, ← BitVec.ofNat_add]
    congr 1
  · rw [a10, w, at_.src, ← wordAddress_add]; congr 1
  · rw [a12, w, at_.dst, ← wordAddress_add]; congr 1
  · rw [keep _ (by decide) (by decide), w, at_.sel]
  · rw [keep _ (by decide) (by decide), w, at_.size]
  · rw [keep _ (by decide) (by decide), w, at_.prim]

/-! ### The two loops as oracle computations -/

def fwdTrace (S T : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n+1, g, s => do
      let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView s) (S+46*g))))))
      fwdTrace S T n (g+1) (fwdAdv (writeBits s (wordAddress (T+25*g)) y))

def invTrace (A D : Nat) : Nat → Nat → MachineState → OracleComp World MachineState
  | 0, _, s => pure s
  | n+1, g, s => do
      let y ← World.query (.inr (.inr (.inr (packBuffer (window (memoryView s) (A+25*g))))))
      invTrace A D n (g+1) (invAdv (writeBits s (wordAddress (D+20*g)) y))

theorem fwd_run (S T : Nat) (sb : S+46*42 ≤ 2^33) (tb : T+25*42 ≤ 2^33) :
    ∀ n g fuel (s : MachineState), g+n ≤ 42 → FwdAt S T g s →
      execute openingImage (3*n+fuel) s true = (do
        let t ← fwdTrace S T n g s
        let r ← execute openingImage fuel t true
        pure (r.charge (10*n) n)) := by
  intro n
  induction n with
  | zero =>
    intro g fuel s _ _
    simp only [fwdTrace, pure_bind, Nat.mul_zero, Nat.zero_add]
    rw [show (do let r ← execute openingImage fuel s true; pure (r.charge 0 0)) =
      execute openingImage fuel s true from by
        conv => rhs; rw [← bind_pure (execute openingImage fuel s true)]
        apply bind_congr; intro r; cases r; simp [Execution.charge]]
  | succ n ih =>
    intro g fuel s le at_
    rw [show 3*(n+1)+fuel = 3+(3*n+fuel) by omega, fwd_step S T g _ s (by omega) at_ (by omega) (by omega)]
    simp only [fwdTrace, bind_assoc]
    apply bind_congr; intro y
    rw [ih (g+1) fuel _ (by omega) (fwd_next S T g s at_ y).1]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro t
    apply bind_congr; intro r
    rw [charge_merge, show 10 + 10*n = 10*(n+1) by omega, show 1 + n = n+1 by omega]

theorem inv_run (A D : Nat) (ab : A+25*42 ≤ 2^33) (db : D+20*42+5 ≤ 2^33) :
    ∀ n g fuel (s : MachineState), g+n ≤ 42 → InvAt A D g s →
      execute openingImage (3*n+fuel) s true = (do
        let t ← invTrace A D n g s
        let r ← execute openingImage fuel t true
        pure (r.charge (10*n) n)) := by
  intro n
  induction n with
  | zero =>
    intro g fuel s _ _
    simp only [invTrace, pure_bind, Nat.mul_zero, Nat.zero_add]
    rw [show (do let r ← execute openingImage fuel s true; pure (r.charge 0 0)) =
      execute openingImage fuel s true from by
        conv => rhs; rw [← bind_pure (execute openingImage fuel s true)]
        apply bind_congr; intro r; cases r; simp [Execution.charge]]
  | succ n ih =>
    intro g fuel s le at_
    rw [show 3*(n+1)+fuel = 3+(3*n+fuel) by omega, inv_step A D g _ s (by omega) at_ (by omega) (by omega)]
    simp only [invTrace, bind_assoc]
    apply bind_congr; intro y
    rw [ih (g+1) fuel _ (by omega) (inv_next A D g s at_ y).1]
    simp only [bind_assoc, pure_bind]
    apply bind_congr; intro t
    apply bind_congr; intro r
    rw [charge_merge, show 10 + 10*n = 10*(n+1) by omega, show 1 + n = n+1 by omega]

theorem fwd_post (S T : Nat) : ∀ n g (s t : MachineState), FwdAt S T g s →
    t ∈ support (fwdTrace S T n g s) →
      FwdAt S T (g+n) t ∧ ∀ r, r ≠ .x10 → r ≠ .x12 → t.getReg r = s.getReg r := by
  intro n
  induction n with
  | zero =>
    intro g s t at_ hit
    simp only [fwdTrace, support_pure, Set.mem_singleton_iff] at hit
    subst t; exact ⟨at_, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro g s t at_ hit
    simp only [fwdTrace, mem_support_bind_iff] at hit
    obtain ⟨y, _, rest⟩ := hit
    obtain ⟨next, keep⟩ := fwd_next S T g s at_ y
    obtain ⟨fin, keep'⟩ := ih (g+1) _ t next rest
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 n] using fin, fun r a b => (keep' r a b).trans (keep r a b)⟩

theorem inv_post (A D : Nat) : ∀ n g (s t : MachineState), InvAt A D g s →
    t ∈ support (invTrace A D n g s) →
      InvAt A D (g+n) t ∧ ∀ r, r ≠ .x10 → r ≠ .x12 → t.getReg r = s.getReg r := by
  intro n
  induction n with
  | zero =>
    intro g s t at_ hit
    simp only [invTrace, support_pure, Set.mem_singleton_iff] at hit
    subst t; exact ⟨at_, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro g s t at_ hit
    simp only [invTrace, mem_support_bind_iff] at hit
    obtain ⟨y, _, rest⟩ := hit
    obtain ⟨next, keep⟩ := inv_next A D g s at_ y
    obtain ⟨fin, keep'⟩ := ih (g+1) _ t next rest
    exact ⟨by simpa [Nat.add_assoc, Nat.add_comm 1 n] using fin, fun r a b => (keep' r a b).trans (keep r a b)⟩

/-! ### Fixed-oracle semantics -/

def fixedFwd (o : Oracle) (S T : Nat) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, g, s => fixedFwd o S T n (g+1)
      (fwdAdv (writeBits s (wordAddress (T+25*g)) (o.permutation (packBuffer (window (memoryView s) (S+46*g))))))

def fixedInv (o : Oracle) (A D : Nat) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, g, s => fixedInv o A D n (g+1)
      (invAdv (writeBits s (wordAddress (D+20*g)) (o.permutation.symm (packBuffer (window (memoryView s) (A+25*g))))))

theorem fwd_fixed (o : Oracle) (S T : Nat) : ∀ n g (s : MachineState),
    o.run (fwdTrace S T n g s) = pure (fixedFwd o S T n g s, n) := by
  intro n
  induction n with
  | zero => intro g s; exact oracle_run_pure ..
  | succ n ih =>
    intro g s
    rw [fwdTrace, oracle_run_public_bind]
    simp only [Oracle.answer]
    rw [ih]
    simp [fixedFwd, Nat.add_comm]
    rfl

theorem inv_fixed (o : Oracle) (A D : Nat) : ∀ n g (s : MachineState),
    o.run (invTrace A D n g s) = pure (fixedInv o A D n g s, n) := by
  intro n
  induction n with
  | zero => intro g s; exact oracle_run_pure ..
  | succ n ih =>
    intro g s
    rw [invTrace, oracle_run_public_bind]
    simp only [Oracle.answer]
    rw [ih]
    simp [fixedInv, Nat.add_comm]
    rfl

theorem fwd_mem (o : Oracle) (S T : Nat) (s0 : MachineState) (sep : S+46*42 ≤ T) (tb : T+25*42 ≤ 2^33) :
    ∀ n g (s : MachineState), g+n ≤ 42 →
      (∀ w < T, memoryView s w = memoryView s0 w) →
      (∀ h < g, window (memoryView s) (T+25*h) =
        (replyWords (o.permutation (packBuffer (window (memoryView s0) (S+46*h)))) : Words 25)) →
      (∀ w < T, memoryView (fixedFwd o S T n g s) w = memoryView s0 w) ∧
      (∀ h < g+n, window (memoryView (fixedFwd o S T n g s)) (T+25*h) =
        (replyWords (o.permutation (packBuffer (window (memoryView s0) (S+46*h)))) : Words 25)) := by
  intro n
  induction n with
  | zero => intro g s _ low done; exact ⟨low, done⟩
  | succ n ih =>
    intro g s le low done
    let y := o.permutation (packBuffer (window (memoryView s) (S+46*g)))
    let s' := fwdAdv (writeBits s (wordAddress (T+25*g)) y)
    have view : ∀ w < 2^33, memoryView s' w = writeWindow (memoryView s) (T+25*g) (replyWords y) w := by
      intro w big
      rw [view_of_mem (fwd_adv_regs _).2.2.1]
      exact permutation_write_memory s (T+25*g) w y (by omega) big
    have srcSame : window (memoryView s) (S+46*g) = (window (memoryView s0) (S+46*g) : Words 25) := by
      funext j; exact low _ (by have := j.isLt; omega)
    have low' : ∀ w < T, memoryView s' w = memoryView s0 w := by
      intro w hw
      rw [view w (by omega), writeWindow, dite_eq_right (by omega)]
      exact low w hw
    have done' : ∀ h < g+1, window (memoryView s') (T+25*h) =
        (replyWords (o.permutation (packBuffer (window (memoryView s0) (S+46*h)))) : Words 25) := by
      intro h hh
      funext j
      have jb := j.isLt
      by_cases last : h = g
      · subst h
        simp only [window]
        rw [view _ (by omega), writeWindow, dite_eq_left (by omega)]
        simp only [y, srcSame]
        congr 2
        first | omega | (apply Fin.ext; simp; omega)
      · have old := congrFun (done h (by omega)) j
        simp only [window] at old ⊢
        rw [view _ (by omega), writeWindow, dite_eq_right (by omega)]
        exact old
    have rest := ih (g+1) s' (by omega) low' done'
    simpa [fixedFwd, Nat.add_assoc, Nat.add_comm 1 n] using rest

theorem inv_mem (o : Oracle) (A D : Nat) (src : Nat → BitVec 1600) (s0 : MachineState)
    (sep : D+20*42+5 ≤ A) (ab : A+25*42 ≤ 2^33) :
    ∀ n g (s : MachineState), g+n ≤ 42 →
      (∀ w < D, memoryView s w = memoryView s0 w) →
      (∀ h, g ≤ h → h < 42 → window (memoryView s) (A+25*h) = (replyWords (o.permutation (src h)) : Words 25)) →
      (∀ h < g, ∀ m < 20, memoryView s (D+20*h+m) = (src h).extractLsb' (64*m) 64) →
      (∀ w < D, memoryView (fixedInv o A D n g s) w = memoryView s0 w) ∧
      (∀ h < g+n, ∀ m < 20, memoryView (fixedInv o A D n g s) (D+20*h+m) = (src h).extractLsb' (64*m) 64) := by
  intro n
  induction n with
  | zero => intro g s _ low _ done; exact ⟨low, done⟩
  | succ n ih =>
    intro g s le low pending done
    let y := o.permutation.symm (packBuffer (window (memoryView s) (A+25*g)))
    have answer : y = src g := by
      have rp := reply_pack' (o.permutation (src g))
      simp only [y, pending g le_rfl (by omega)]
      rw [rp]
      exact Equiv.symm_apply_apply _ _
    let s' := invAdv (writeBits s (wordAddress (D+20*g)) y)
    have view : ∀ w < 2^33, memoryView s' w = writeWindow (memoryView s) (D+20*g) (replyWords y) w := by
      intro w big
      rw [view_of_mem (inv_adv_regs _).2.2.1]
      exact permutation_write_memory s (D+20*g) w y (by omega) big
    have low' : ∀ w < D, memoryView s' w = memoryView s0 w := by
      intro w hw
      rw [view w (by omega), writeWindow, dite_eq_right (by omega)]
      exact low w hw
    have pending' : ∀ h, g+1 ≤ h → h < 42 →
        window (memoryView s') (A+25*h) = (replyWords (o.permutation (src h)) : Words 25) := by
      intro h lo hi
      funext j
      have jb := j.isLt
      have old := congrFun (pending h (by omega) hi) j
      simp only [window] at old ⊢
      rw [view _ (by omega), writeWindow, dite_eq_right (by omega)]
      exact old
    have done' : ∀ h < g+1, ∀ m < 20, memoryView s' (D+20*h+m) = (src h).extractLsb' (64*m) 64 := by
      intro h hh m hm
      by_cases last : h = g
      · subst h
        rw [view _ (by omega), writeWindow, dite_eq_left (by omega), answer]
        simp only [replyWords]
        congr 2
        omega
      · rw [view _ (by omega), writeWindow, dite_eq_right (by omega)]
        exact done h (by omega) m hm
    have rest := ih (g+1) s' (by omega) low' pending' done'
    simpa [fixedInv, Nat.add_assoc, Nat.add_comm 1 n] using rest

/-! ### The whole footer -/

/-- Word index of the first level-7 group (`pentaGroupBase 7 + 40` past the trapdoor). -/
def S7 : Nat := (trapdoorBase + pentaGroupBase 7 + 40) / 8
/-- Word index of the table start after `k` records. -/
def tableWord (k : Nat) : Nat := proofBase / 8 + 142*k
/-- Word index of the scratch area. -/
def scratchWord (k : Nat) : Nat := tableWord k + 1024

theorem s7_address : 8*S7 = trapdoorBase + pentaGroupBase 7 + 40 := by decide
theorem s7_value : S7 = 536871428 + (pentaGroupBase 7 + 40) / 8 := by decide
theorem s7_room : 8*(S7+46*43) ≤ proofBase := by decide

theorem s7_num : S7 = 729812996 := by decide

theorem s7_lt (k : Nat) : S7+46*43 ≤ tableWord k := by
  have pb : proofBase / 8 = 1350566924 := by decide
  unfold tableWord
  rw [s7_num, pb]
  omega

theorem s7_below (k : Nat) : S7+46*42 + 20 ≤ tableWord k + 20*42 := by
  have pb : proofBase / 8 = 1350566924 := by decide
  unfold tableWord
  rw [s7_num, pb]
  omega

def headState (s0 : MachineState) : MachineState :=
  footHead.foldl execInstrBr (s0.setPC (BitVec.ofNat 64 (4096+4*527)))
def midState (t : MachineState) : MachineState := footMid.foldl execInstrBr t
def exitList : List Instr := [.ADDI .x12 .x12 160, .SUB .x11 .x12 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0]
def lastState (u : MachineState) : MachineState := lastCode.foldl execInstrBr u
def exitState (u : MachineState) : MachineState := exitList.foldl execInstrBr (lastState u)

def lastPairs (n : Nat) : List Instr :=
  (List.range n).flatMap fun m => [.LD .x31 .x30 (BitVec.ofNat 12 (8*m)), .SD .x12 .x31 (BitVec.ofNat 12 (8*m))]

theorem last_pairs_succ (n : Nat) : lastPairs (n+1) =
    lastPairs n ++ [.LD .x31 .x30 (BitVec.ofNat 12 (8*n)), .SD .x12 .x31 (BitVec.ofNat 12 (8*n))] := by
  simp [lastPairs, List.range_succ, List.flatMap_append]

theorem last_pairs_length (n : Nat) : (lastPairs n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [last_pairs_succ, List.length_append, ih]; simp; omega

set_option maxRecDepth 100000 in
theorem last_codes : ∀ m < 20, program[791+2*m]? = some (.LD .x31 .x30 (BitVec.ofNat 12 (8*m))) ∧
    program[791+2*m+1]? = some (.SD .x12 .x31 (BitVec.ofNat 12 (8*m))) := by
  decide +kernel

/-- The last group: `n ≤ 20` doublewords from `x30 = Src` to `x12 = Dst`. -/
theorem last_copy (Src Dst : Nat) (sep : Src + 20 ≤ Dst) (db : Dst + 20 ≤ 2^33) :
    ∀ n ≤ 20, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*791) →
      state.getReg .x30 = wordAddress Src → state.getReg .x12 = wordAddress Dst →
      Runs state ((lastPairs n).foldl execInstrBr state) (2*n) (2*n) ∧
      ((lastPairs n).foldl execInstrBr state).pc = BitVec.ofNat 64 (4096+4*(791+2*n)) ∧
      (∀ r, r ≠ .x31 → ((lastPairs n).foldl execInstrBr state).getReg r = state.getReg r) ∧
      ∀ w < 2^33, memoryView ((lastPairs n).foldl execInstrBr state) w =
        if Dst ≤ w ∧ w < Dst + n then memoryView state (Src + (w - Dst)) else memoryView state w := by
  intro n
  induction n with
  | zero =>
    intro _ state pc _ _
    refine ⟨Runs.zero state, by simp [lastPairs]; exact pc, fun _ _ => rfl, fun w _ => ?_⟩
    rw [if_neg (by omega)]; rfl
  | succ n ih =>
    intro le state pc x30 x12
    obtain ⟨run, pcN, keepN, viewN⟩ := ih (by omega) state pc x30 x12
    have room : MEMORY_BYTES = 68719476736 := rfl
    obtain ⟨c1, c2⟩ := last_codes n (by omega)
    have offs : signExtend12 (BitVec.ofNat 12 (8*n)) = BitVec.ofNat 64 (8*n) := by
      have : ∀ m < 20, signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m) := by decide
      exact this n (by omega)
    generalize hm : (lastPairs n).foldl execInstrBr state = mid at run pcN keepN viewN
    obtain ⟨r1, v1, k1, m1, p1⟩ := run_ld mid .x31 .x30 _ (791+2*n) c1 pcN (8*(Src+n))
      (by rw [keepN .x30 (by decide), x30, offs]; unfold wordAddress; rw [← BitVec.ofNat_add]; congr 1; omega)
      (by omega) (by omega) (by decide)
    generalize h1 : execInstrBr mid (.LD .x31 .x30 (BitVec.ofNat 12 (8*n))) = s1 at r1 v1 k1 m1 p1
    obtain ⟨r2, k2, v2, p2⟩ := run_sd s1 .x12 .x31 _ (791+2*n+1) c2 p1 (Dst+n)
      (by rw [k1 .x12 (by decide), keepN .x12 (by decide), x12, offs]; unfold wordAddress; rw [← BitVec.ofNat_add]
          congr 1; omega) (by omega)
    generalize h2 : execInstrBr s1 (.SD .x12 .x31 (BitVec.ofNat 12 (8*n))) = s2 at r2 k2 v2 p2
    have shape : (lastPairs (n+1)).foldl execInstrBr state = s2 := by
      rw [last_pairs_succ, List.foldl_append, hm]; simp [← h1, ← h2]
    rw [shape]
    refine ⟨(run.trans (r1.trans r2)).cast (by omega) (by omega), by rw [p2]; congr 1, fun r a => ?_, fun w hw => ?_⟩
    · rw [k2, k1 r a, keepN r a]
    · rw [v2 w (by omega)]
      by_cases here : w = Dst + n
      · rw [if_pos here, if_pos (by omega), v1, view_get, viewN _ (by omega), if_neg (by omega)]
        congr 1; omega
      · rw [if_neg here, view_of_mem m1, viewN w hw]
        by_cases inside : Dst ≤ w ∧ w < Dst + n
        · rw [if_pos inside, if_pos (by omega)]
        · rw [if_neg inside, if_neg (by omega)]


def footerTrace (k : Nat) (s0 : MachineState) : OracleComp World MachineState := do
  let t ← fwdTrace S7 (scratchWord k) 42 0 (headState s0)
  let u ← invTrace (scratchWord k) (tableWord k) 42 0 (midState t)
  pure (exitState u)

theorem footer_jump (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*106)) :
    Runs state (state.setPC (BitVec.ofNat 64 (4096+4*527))) 1 1 := by
  have shape : execInstrBr state footerJump = state.setPC (BitVec.ofNat 64 (4096+4*527)) := by
    change state.setPC (state.pc + signExtend21 1684) = _
    rw [pc]
    exact congrArg state.setPC (by decide)
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program state 106 _ jump_code pc)
    (show ordinaryStep state (.base footerJump) = some (execInstrBr state footerJump) from rfl), shape]
  rfl

theorem lui_two : ((BitVec.ofNat 20 2).zeroExtend 32 <<< 12).signExtend 64 = wordAddress 1024 := by decide

theorem head_facts (k : Nat) (s0 : MachineState)
    (heap : s0.getReg .x9 = BitVec.ofNat 64 trapdoorBase) (to_ : s0.getReg .x21 = wordAddress (tableWord k)) :
    FwdAt S7 (scratchWord k) 0 (headState s0) ∧ (headState s0).mem = s0.mem ∧
      ∀ r, r ≠ .x5 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → (headState s0).getReg r = s0.getReg r := by
  have page := lui_page 7 (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [headState, pure_pc _ _ rfl]
    simp only [MachineState.setPC]
    rw [show (4*footHead.length) = 28 from rfl, ← BitVec.ofNat_add]
  · simp [headState, footHead, execInstrBr, heap, page]
    rw [wordAddress, s7_address, ← BitVec.ofNat_add]
    congr 1
  · simp [headState, footHead, execInstrBr, to_]
    rw [scratchWord, wordAddress_add, show wordAddress 1024 = 8192#64 from rfl]
    exact BitVec.add_comm _ _
  · simp [headState, footHead, execInstrBr, signExtend12]; rfl
  · simp [headState, footHead, execInstrBr, signExtend12]; rfl
  · simp [headState, footHead, execInstrBr, signExtend12]; rfl
  · rw [headState, pure_mem _ _ rfl]; rfl
  · intro r a b c d e
    simp [headState, footHead, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e]

theorem mid_facts (k : Nat) (t : MachineState) (at_ : FwdAt S7 (scratchWord k) 42 t)
    (to_ : t.getReg .x21 = wordAddress (tableWord k)) :
    InvAt (scratchWord k) (tableWord k) 0 (midState t) ∧ (midState t).mem = t.mem ∧
      (midState t).getReg .x30 = wordAddress (S7+46*42) ∧
      ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x13 → r ≠ .x30 → (midState t).getReg r = t.getReg r := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [midState, pure_pc _ _ rfl, at_.pc, show (4*footMid.length) = 20 from rfl, ← BitVec.ofNat_add]
  · simp [midState, footMid, execInstrBr, to_]
    rw [scratchWord, wordAddress_add, show wordAddress 1024 = 8192#64 from rfl]
    exact BitVec.add_comm _ _
  · simp [midState, footMid, execInstrBr, to_, signExtend12]
  · simp [midState, footMid, execInstrBr, at_.sel]
  · simp [midState, footMid, execInstrBr, at_.size]
  · simp [midState, footMid, execInstrBr, signExtend12]; rfl
  · rw [midState, pure_mem _ _ rfl]
  · simp [midState, footMid, execInstrBr, at_.src, show signExtend12 0#12 = 0#64 by decide]
  · intro r a b c d
    simp [midState, footMid, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d]

theorem exit_facts (A D Src : Nat) (u : MachineState) (at_ : InvAt A D 42 u)
    (x30 : u.getReg .x30 = wordAddress Src) (sep : Src + 20 ≤ D + 20*42) (db : D + 20*42 + 20 ≤ 2^33) :
    Runs u (lastState u) 40 40 ∧
    (exitState u).pc = BitVec.ofNat 64 (4096+4*835) ∧
    (∀ w < 2^33, memoryView (exitState u) w =
      if D + 20*42 ≤ w ∧ w < D + 20*42 + 20 then memoryView u (Src + (w - (D + 20*42))) else memoryView u w) ∧
    (exitState u).getReg .x11 = (u.getReg .x12 + signExtend12 160) - u.getReg .x15 ∧
    (exitState u).getReg .x5 = 1 ∧ (exitState u).getReg .x10 = 0 ∧
    (lastState u).pc = BitVec.ofNat 64 (4096+4*831) := by
  obtain ⟨run, pcL, keepL, viewL⟩ := last_copy Src (D+20*42) sep db 20 le_rfl u (by simpa using at_.pc) x30
    (by simpa using at_.dst)
  have same : (lastPairs 20).foldl execInstrBr u = lastState u := rfl
  rw [same] at run pcL keepL viewL
  have pureE : exitList.all pureOp = true := rfl
  refine ⟨run, ?_, ?_, ?_, ?_, ?_, pcL⟩
  · rw [exitState, pure_pc _ _ pureE, pcL, show (4*exitList.length) = 16 from rfl, ← BitVec.ofNat_add]
  · intro w hw
    rw [exitState, view_of_mem (pure_mem _ _ pureE), viewL w hw]
  · rw [exitState]
    simp [exitList, execInstrBr]
    rw [keepL _ (by decide), keepL _ (by decide)]
  · simp [exitState, exitList, execInstrBr, signExtend12]; rfl
  · simp [exitState, exitList, execInstrBr, signExtend12]; rfl

theorem exit_list_code : CodeAt 831 exitList := by
  intro i hi
  rw [exit_code i (by simp [exitList, footExit] at hi ⊢; omega)]
  have : i < 4 := by simpa [exitList] using hi
  interval_cases i <;> rfl

theorem table_bounds (k : Nat) (hk : k ≤ 2^24) :
    S7+46*42 ≤ scratchWord k ∧ scratchWord k+25*42 ≤ 2^33 ∧ tableWord k+20*42+5 ≤ scratchWord k ∧
      tableWord k + 20*42 + 5 ≤ 2^33 := by
  have pb : proofBase = 10804535392 := rfl
  have : S7 = 536871428 + (pentaGroupBase 7 + 40) / 8 := s7_value
  have room := s7_room
  unfold scratchWord tableWord
  omega

/-- From word 106 to the halt at word 835: 310 steps, 898 cycles and 84 permutation calls. -/
theorem footer_exec (k : Nat) (hk : k ≤ 2^24) (s0 : MachineState)
    (pc : s0.pc = BitVec.ofNat 64 (4096+4*106))
    (heap : s0.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (to_ : s0.getReg .x21 = wordAddress (tableWord k)) (fuel : Nat) :
    execute openingImage (310+fuel) s0 true =
      (fun u => (⟨.success, u, 898, 84⟩ : Execution)) <$> footerTrace k s0 := by
  obtain ⟨b1, b2, b3, b4⟩ := table_bounds k hk
  obtain ⟨at2, mem2, keep2⟩ := head_facts k s0 heap to_
  have run1 := footer_jump s0 pc
  have run2 : Runs (s0.setPC (BitVec.ofNat 64 (4096+4*527))) (headState s0) 7 7 :=
    (runs_pure footHead 527 (s0.setPC (BitVec.ofNat 64 (4096+4*527))) head_code rfl rfl).cast rfl rfl
  rw [show 310+fuel = 1+(7+(3*42+(5+(3*42+(40+(4+(fuel+1))))))) by omega, run1, run2]
  simp only [bind_assoc, pure_bind]
  rw [fwd_run S7 (scratchWord k) (by omega) b2 42 0 _ (headState s0) (by omega) at2]
  simp only [footerTrace, map_bind, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support; intro t ht
  obtain ⟨at3, keep3⟩ := fwd_post S7 (scratchWord k) 42 0 _ t at2 ht
  have x21t : t.getReg .x21 = wordAddress (tableWord k) := by
    rw [keep3 _ (by decide) (by decide), keep2 _ (by decide) (by decide) (by decide) (by decide) (by decide), to_]
  obtain ⟨at4, mem4, x30m, keep4⟩ := mid_facts k t at3 x21t
  have run3 : Runs t (midState t) 5 5 :=
    (runs_pure footMid 660 t mid_code (by simpa using at3.pc) rfl).cast rfl rfl
  rw [run3]
  simp only [bind_assoc, pure_bind]
  rw [inv_run (scratchWord k) (tableWord k) b2 b4 42 0 _ (midState t) (by omega) at4]
  simp only [bind_assoc, map_bind, pure_bind]
  apply bind_congr_of_forall_mem_support; intro u hu
  obtain ⟨at5, keep5⟩ := inv_post (scratchWord k) (tableWord k) 42 0 _ u at4 hu
  have x30u : u.getReg .x30 = wordAddress (S7+46*42) := by rw [keep5 _ (by decide) (by decide), x30m]
  have sep := s7_below k
  obtain ⟨runL, pc6, _, x11, x5, x10, pcL⟩ := exit_facts _ _ (S7+46*42) u at5 x30u sep (by omega)
  have run4 : Runs (lastState u) (exitState u) 4 4 :=
    (runs_pure exitList 831 (lastState u) exit_list_code pcL rfl).cast rfl rfl
  rw [runL, run4]
  have halted := fetch_program (exitState u) 835 .ECALL (by
    have := exit_code 4 (by decide); simpa [footExit] using this) pc6
  simp [execute, halted, x5, x10, Execution.charge]

def fixedFooter (o : Oracle) (k : Nat) (s0 : MachineState) : MachineState :=
  exitState (fixedInv o (scratchWord k) (tableWord k) 42 0
    (midState (fixedFwd o S7 (scratchWord k) 42 0 (headState s0))))

theorem footer_fixed (o : Oracle) (k : Nat) (s0 : MachineState) :
    o.run (footerTrace k s0) = pure (fixedFooter o k s0, 84) := by
  unfold footerTrace
  rw [oracle_run_bind, fwd_fixed]
  simp only [pure_bind]
  rw [oracle_run_bind, inv_fixed]
  simp only [pure_bind, oracle_run_pure]
  rfl

/-- On every reply sequence, the exit reports the table end minus the proof base. -/
theorem footer_length_reg (k : Nat) (hk : k ≤ 2^24) (s0 z : MachineState)
    (heap : s0.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (to_ : s0.getReg .x21 = wordAddress (tableWord k))
    (hit : z ∈ support (footerTrace k s0)) :
    z.getReg .x11 = (wordAddress (tableWord k + 20*42) + signExtend12 160) - s0.getReg .x15 := by
  obtain ⟨b1, b2, b3, b4⟩ := table_bounds k hk
  obtain ⟨at2, _, keep2⟩ := head_facts k s0 heap to_
  simp only [footerTrace, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hit
  obtain ⟨t, ht, u, hu, rfl⟩ := hit
  obtain ⟨at3, keep3⟩ := fwd_post S7 (scratchWord k) 42 0 _ t at2 ht
  have x21t : t.getReg .x21 = wordAddress (tableWord k) := by
    rw [keep3 _ (by decide) (by decide), keep2 _ (by decide) (by decide) (by decide) (by decide) (by decide), to_]
  obtain ⟨at4, _, x30m, keep4⟩ := mid_facts k t at3 x21t
  obtain ⟨at5, keep5⟩ := inv_post (scratchWord k) (tableWord k) 42 0 _ u at4 hu
  have x30u : u.getReg .x30 = wordAddress (S7+46*42) := by rw [keep5 _ (by decide) (by decide), x30m]
  have sep := s7_below k
  obtain ⟨_, _, _, x11, _, _, _⟩ := exit_facts _ _ (S7+46*42) u at5 x30u sep (by omega)
  rw [x11, at5.dst, keep5 _ (by decide) (by decide), keep4 _ (by decide) (by decide) (by decide) (by decide),
    keep3 _ (by decide) (by decide), keep2 _ (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem fixed_fwd_regs (o : Oracle) (S T : Nat) : ∀ n g (s : MachineState), FwdAt S T g s →
    FwdAt S T (g+n) (fixedFwd o S T n g s) ∧
      ∀ r, r ≠ .x10 → r ≠ .x12 → (fixedFwd o S T n g s).getReg r = s.getReg r := by
  intro n
  induction n with
  | zero => intro g s at_; exact ⟨at_, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro g s at_
    obtain ⟨next, keep⟩ := fwd_next S T g s at_ (o.permutation (packBuffer (window (memoryView s) (S+46*g))))
    obtain ⟨fin, keep'⟩ := ih (g+1) _ next
    exact ⟨by simpa [fixedFwd, Nat.add_assoc, Nat.add_comm 1 n] using fin,
      fun r a b => by simpa [fixedFwd] using (keep' r a b).trans (keep r a b)⟩

theorem fixed_inv_regs (o : Oracle) (A D : Nat) : ∀ n g (s : MachineState), InvAt A D g s →
    InvAt A D (g+n) (fixedInv o A D n g s) ∧
      ∀ r, r ≠ .x10 → r ≠ .x12 → (fixedInv o A D n g s).getReg r = s.getReg r := by
  intro n
  induction n with
  | zero => intro g s at_; exact ⟨at_, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro g s at_
    obtain ⟨next, keep⟩ := inv_next A D g s at_ (o.permutation.symm (packBuffer (window (memoryView s) (A+25*g))))
    obtain ⟨fin, keep'⟩ := ih (g+1) _ next
    exact ⟨by simpa [fixedInv, Nat.add_assoc, Nat.add_comm 1 n] using fin,
      fun r a b => by simpa [fixedInv] using (keep' r a b).trans (keep r a b)⟩

set_option maxRecDepth 20000 in
/-- With the fixed oracle, the footer leaves the records alone and emits the 43 level-7 groups. -/
theorem footer_output (o : Oracle) (init s0 : MachineState) (positions : Positions) (k : Nat)
    (hk : k = positions.card)
    (heap : s0.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (to_ : s0.getReg .x21 = wordAddress (tableWord k))
    (inv : Inv init s0 (wordSource positions) (142*k)) :
    Inv init (fixedFooter o k s0) (proofSource positions) (142*k+860) := by
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  obtain ⟨b1, b2, b3, b4⟩ := table_bounds k (by omega)
  obtain ⟨at2, mem2, keep2⟩ := head_facts k s0 heap to_
  let s2 := headState s0
  let t := fixedFwd o S7 (scratchWord k) 42 0 s2
  let s3 := midState t
  let u := fixedInv o (scratchWord k) (tableWord k) 42 0 s3
  let src : Nat → BitVec 1600 := fun h => packBuffer (window (memoryView s2) (S7+46*h))
  have v2 : memoryView s2 = memoryView s0 := view_of_mem mem2
  obtain ⟨fLow, fWin⟩ := fwd_mem o S7 (scratchWord k) s2 b1 b2 42 0 s2 (by omega) (fun _ _ => rfl)
    (fun h hh => absurd hh (Nat.not_lt_zero _))
  have v3 : memoryView s3 = memoryView t := view_of_mem (pure_mem _ _ rfl)
  obtain ⟨iLow, iOut⟩ := inv_mem o (scratchWord k) (tableWord k) src s3 b3 b2 42 0 s3 (by omega)
    (fun _ _ => rfl) (fun h _ hh => by rw [v3]; exact fWin h hh) (fun h hh => absurd hh (Nat.not_lt_zero _))
  obtain ⟨at3, keep3⟩ := fixed_fwd_regs o S7 (scratchWord k) 42 0 s2 at2
  have x21t : t.getReg .x21 = wordAddress (tableWord k) := by
    rw [keep3 _ (by decide) (by decide), keep2 _ (by decide) (by decide) (by decide) (by decide) (by decide), to_]
  obtain ⟨at4, _, x30m, keep4⟩ := mid_facts k t (by simpa using at3) x21t
  obtain ⟨at5, keep5⟩ := fixed_inv_regs o (scratchWord k) (tableWord k) 42 0 s3 at4
  have x30u : u.getReg .x30 = wordAddress (S7+46*42) := by rw [keep5 _ (by decide) (by decide), x30m]
  have sep := s7_below k
  obtain ⟨_, _, viewE, _, _, _, _⟩ := exit_facts _ _ (S7+46*42) u (by simpa using at5) x30u sep (by omega)
  have vf : ∀ w < 2^33, memoryView (fixedFooter o k s0) w =
      if tableWord k + 20*42 ≤ w ∧ w < tableWord k + 20*42 + 20 then memoryView u (S7+46*42 + (w - (tableWord k + 20*42)))
      else memoryView u w := viewE
  have pb : proofBase = 8 * (proofBase / 8) := by decide
  have tb : trapdoorBase = 4294971424 := rfl
  have pbv : proofBase = 10804535392 := rfl
  have s7v := s7_value
  have low : ∀ w, w < tableWord k → memoryView (fixedFooter o k s0) w = memoryView s0 w := by
    intro w hw
    rw [vf w (by unfold tableWord at hw; omega), if_neg (by omega), iLow w hw, v3, fLow w (by unfold scratchWord; omega), v2]
  refine ⟨fun a lo hi al => ?_, fun v hv => ?_⟩
  · have e : (fixedFooter o k s0).getMem (BitVec.ofNat 64 a) = s0.getMem (BitVec.ofNat 64 a) := by
      obtain ⟨w, rfl⟩ : ∃ w, a = 8*w := ⟨a/8, by omega⟩
      exact low w (by unfold tableWord; omega)
    exact e.trans (inv.input a lo hi al)
  · by_cases rec : v < 142*k
    · have e : (fixedFooter o k s0).getMem (BitVec.ofNat 64 (proofBase+8*v)) =
          s0.getMem (BitVec.ofNat 64 (proofBase+8*v)) := by
        rw [show proofBase+8*v = 8*(proofBase/8+v) by omega]
        exact low _ (by unfold tableWord; omega)
      rw [e, inv.output v rec]
      unfold proofSource
      rw [if_pos (by omega)]
    · let v' := v - 142*k
      have hv' : v' < 860 := by omega
      let h := v' / 20
      let m := v' % 20
      have hh : h < 43 := by omega
      have hm : m < 20 := by omega
      have addr : proofBase+8*v = 8*(tableWord k + 20*h + m) := by unfold tableWord; omega
      have value : memoryView (fixedFooter o k s0) (tableWord k + 20*h + m) = memoryView s0 (S7+46*h+m) := by
        rw [vf _ (by unfold tableWord; omega)]
        by_cases top : h = 42
        · have below := s7_lt k
          have fb : S7+46*42 + m < scratchWord k := by unfold scratchWord; omega
          rw [if_pos (by omega), show tableWord k + 20*h + m - (tableWord k + 20*42) = m by omega,
            iLow _ (by omega), v3, fLow _ fb, v2]
          apply congrArg (memoryView s0); omega
        · rw [if_neg (by omega), iOut h (by omega) m hm]
          have packed := packed_word (window (memoryView s2) (S7+46*h)) ⟨m, by omega⟩
          simp only [src] at packed ⊢
          rw [packed]
          simp only [window, v2]
      rw [addr, view_get, value]
      have srcAddr : proofSource positions v = 8*(S7+46*h+m) := by
        unfold proofSource
        rw [if_neg (by omega)]
        have g := table_source_group 0 h m (by decide) (by rw [(penta_counts).1]; exact hh) hm
        simp only [tableFirst, Nat.add_zero, Nat.zero_add] at g
        rw [show v - 142*positions.card = 20*h + m by omega, g]
        have := s7_address
        omega
      rw [srcAddr]
      have e1 := s7_address
      have e2 := s7_room
      have lo : trapdoorBase ≤ 8*(S7+46*h+m) := by omega
      have hi : 8*(S7+46*h+m) < proofBase :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (by omega : S7+46*h+m < S7+46*43) (by decide)) e2
      have al : 8*(S7+46*h+m) % 8 = 0 := by omega
      exact inv.input _ lo hi al

end TwoPermutationPrototype.QuadOpening
