import CommitGolfCandidate.QuadOpeningRecord

/-! The table copy of the level-7 cap opener (words 106 and 527-2844). After the last record the
latch falls through to word 106, which jumps to word 527. For each level `k = 7 … 10` the copy
sets `x30` to the trapdoor address of the level's first group (`lui`/`add`, the same page
arithmetic as the record writer), then copies every group of the level: the 20 doublewords of its
five slots (`pentaGroupBase k + 40 + 368 g`, 160 bytes) are appended to the output, `x30`
advances by 368 between groups and `x21` by 160 after every group. The exit sequence follows at words 2841-2844. The table is
`55 · 160 = 8,800` bytes in trapdoor order, ragged zero slots included. -/

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
  if u < 114*positions.card then wordSource positions u else tableSource (u - 114*positions.card)

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

/-! ### Code layout -/

theorem group_code_length : groupCode.length = 42 := by decide
theorem last_group_code_length : lastGroupCode.length = 41 := by decide

theorem flatten_replicate_length {α : Type} (c : List α) (n : Nat) :
    (List.replicate n c).flatten.length = n*c.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih, Nat.succ_mul]; omega

theorem flatten_replicate_get {α : Type} (c : List α) : ∀ (n g i : Nat), g < n → i < c.length →
    (List.replicate n c).flatten[c.length*g + i]? = c[i]?
  | 0, _, _, hg, _ => absurd hg (Nat.not_lt_zero _)
  | n+1, 0, i, _, hi => by
    rw [List.replicate_succ, List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_append_left hi]
  | n+1, g+1, i, hg, hi => by
    rw [List.replicate_succ, List.flatten_cons, List.getElem?_append_right (by rw [Nat.mul_succ]; omega),
      show c.length*(g+1)+i - c.length = c.length*g+i by rw [Nat.mul_succ]; omega]
    exact flatten_replicate_get c n g i (by omega) hi

theorem table_level_length (k : Nat) : (tableLevelCode k).length = 2 + 42*(pentaCount (k+1) - 1) + 41 := by
  unfold tableLevelCode
  rw [List.length_append, List.length_append, flatten_replicate_length, group_code_length, last_group_code_length]
  simp only [List.length_cons, List.length_nil]
  omega

theorem footer_parts : footerCode =
    tableLevelCode 7 ++ (tableLevelCode 8 ++ (tableLevelCode 9 ++ (tableLevelCode 10 ++ exitCode))) := by
  simp only [footerCode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- Offset of table level `L` inside `footerCode`. -/
def levelOffset (L : Nat) : Nat := match L with | 0 => 0 | 1 => 1807 | 2 => 2186 | _ => 2271

theorem level_lengths : (tableLevelCode 7).length = 1807 ∧ (tableLevelCode 8).length = 379 ∧
    (tableLevelCode 9).length = 85 ∧ (tableLevelCode 10).length = 43 := by
  obtain ⟨c8, c9, c10, c11⟩ := penta_counts
  simp only [table_level_length, Nat.reduceAdd, c8, c9, c10, c11]
  decide

theorem footer_level (L i : Nat) (hL : L < 4) (hi : i < (tableLevelCode (7+L)).length) :
    footerCode[levelOffset L + i]? = (tableLevelCode (7+L))[i]? := by
  obtain ⟨l7, l8, l9, l10⟩ := level_lengths
  rw [footer_parts]
  interval_cases L
  · simp only [levelOffset, Nat.zero_add, Nat.reduceAdd] at hi ⊢
    exact List.getElem?_append_left hi
  · simp only [levelOffset, Nat.reduceAdd] at hi ⊢
    rw [List.getElem?_append_right (by omega), l7, show 1807 + i - 1807 = i by omega,
      List.getElem?_append_left hi]
  · simp only [levelOffset, Nat.reduceAdd] at hi ⊢
    rw [List.getElem?_append_right (by omega), l7, List.getElem?_append_right (by omega), l8,
      show 2186 + i - 1807 - 379 = i by omega, List.getElem?_append_left hi]
  · simp only [levelOffset, Nat.reduceAdd] at hi ⊢
    rw [List.getElem?_append_right (by omega), l7, List.getElem?_append_right (by omega), l8,
      List.getElem?_append_right (by omega), l9, show 2271 + i - 1807 - 379 - 85 = i by omega,
      List.getElem?_append_left hi]

theorem footer_length : footerCode.length = 2318 := by
  obtain ⟨l7, l8, l9, l10⟩ := level_lengths
  rw [footer_parts]
  simp only [List.length_append, l7, l8, l9, l10]
  rfl

theorem program_split : ∃ head : List Instr, program = head ++ footerCode := ⟨_, rfl⟩

theorem program_footer (i : Nat) : program[527+i]? = footerCode[i]? := by
  obtain ⟨head, split⟩ := program_split
  have total := program_length
  rw [split, List.length_append, footer_length] at total
  rw [split, List.getElem?_append_right (by omega)]
  congr 1
  omega

theorem level_head_code (L : Nat) (hL : L < 4) :
    CodeAt (527 + levelOffset L) [.LUI .x11 (BitVec.ofNat 20 (groupPage (7+L))), .ADD .x30 .x11 .x9] := by
  intro i hi
  have two : i < 2 := by simpa using hi
  rw [Nat.add_assoc, program_footer, footer_level L i hL (by rw [table_level_length]; omega)]
  unfold tableLevelCode
  rw [List.append_assoc]
  exact List.getElem?_append_left (by simpa using two)

theorem group_code_at (L g : Nat) (hL : L < 4) (hg : g < pentaCount (7+L+1) - 1) :
    CodeAt (527 + levelOffset L + 2 + 42*g) groupCode := by
  intro i hi
  rw [group_code_length] at hi
  rw [show 527 + levelOffset L + 2 + 42*g + i = 527 + (levelOffset L + (2 + (42*g + i))) by omega,
    program_footer, footer_level L _ hL (by rw [table_level_length]; omega)]
  unfold tableLevelCode
  have head : ([.LUI .x11 (BitVec.ofNat 20 (groupPage (7+L))), .ADD .x30 .x11 .x9] : List Instr).length = 2 := rfl
  rw [List.append_assoc, List.getElem?_append_right (by rw [head]; omega), head, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by rw [flatten_replicate_length, group_code_length]; omega)]
  have got := flatten_replicate_get groupCode (pentaCount (7+L+1) - 1) g i hg (by rw [group_code_length]; exact hi)
  rw [group_code_length] at got
  exact got

/-- The last group follows the regular groups and leaves the source pointer alone. -/
theorem last_group_code_at (L : Nat) (hL : L < 4) :
    CodeAt (527 + levelOffset L + 2 + 42*(pentaCount (7+L+1) - 1)) lastGroupCode := by
  intro i hi
  rw [last_group_code_length] at hi
  rw [show 527 + levelOffset L + 2 + 42*(pentaCount (7+L+1) - 1) + i =
      527 + (levelOffset L + (2 + 42*(pentaCount (7+L+1) - 1) + i)) by omega,
    program_footer, footer_level L _ hL (by rw [table_level_length]; omega)]
  unfold tableLevelCode
  have prefixLength :
      (([.LUI .x11 (BitVec.ofNat 20 (groupPage (7+L))), .ADD .x30 .x11 .x9] : List Instr) ++
        (List.replicate (pentaCount (7+L+1) - 1) groupCode).flatten).length =
          2 + 42*(pentaCount (7+L+1) - 1) := by
    rw [List.length_append, flatten_replicate_length, group_code_length, Nat.mul_comm]
    rfl
  rw [List.getElem?_append_right (by rw [prefixLength]; omega), prefixLength, Nat.add_sub_cancel_left]

set_option maxRecDepth 100000 in
theorem exit_codes :
    program[106]? = some footerJump ∧
    CodeAt 2841 [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0] ∧ program[2844]? = some .ECALL := by
  decide +kernel

/-! ### One group -/

theorem group_code_split : groupCode = groupPairs 20 ++ [.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] := rfl

theorem group_pairs_length (n : Nat) : (groupPairs n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [groupPairs, List.range_succ, List.flatMap_append] at ih ⊢
    simp [ih]
    omega

theorem group_pairs_succ (n : Nat) : groupPairs (n+1) =
    groupPairs n ++ [.LD .x31 .x30 (BitVec.ofNat 12 (8*n)), .SD .x21 .x31 (BitVec.ofNat 12 (8*n))] := by
  simp [groupPairs, List.range_succ, List.flatMap_append]

set_option maxRecDepth 100000 in
theorem group_pairs_load : ∀ m < 20,
    (groupPairs 20)[2*m]? = some (.LD .x31 .x30 (BitVec.ofNat 12 (8*m))) := by decide

set_option maxRecDepth 100000 in
theorem group_pairs_store : ∀ m < 20,
    (groupPairs 20)[2*m+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (8*m))) := by decide

private theorem group_offset_value : ∀ m < 20, signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m) := by
  decide

/-- One load/store pair of a table group: output word `count` is source word `S + 8 w`. -/
theorem group_step (init state : MachineState) (source : Nat → Nat) (start w count S D : Nat)
    (live : w < 20) (code : CodeAt start (groupPairs 20))
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(start+2*w)))
    (from_ : state.getReg .x30 = BitVec.ofNat 64 S) (to_ : state.getReg .x21 = BitVec.ofNat 64 D)
    (target : D+8*w = proofBase+8*count) (aligned : S % 8 = 0) (low : trapdoorBase ≤ S)
    (high : S+160 ≤ proofBase) (fits : proofBase+8*count+8 ≤ MEMORY_BYTES)
    (named : source count = S+8*w) (inv : Inv init state source count) :
    let after := execInstrBr (execInstrBr state (.LD .x31 .x30 (BitVec.ofNat 12 (8*w))))
      (.SD .x21 .x31 (BitVec.ofNat 12 (8*w)))
    Runs state after 2 2 ∧ Inv init after source (count+1) ∧ after.pc = state.pc+8 ∧
      ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  have offset := group_offset_value w live
  have room : MEMORY_BYTES < 2^64 := by decide
  have heap : trapdoorBase % 8 = 0 := by decide
  have proofAligned : proofBase % 8 = 0 := by decide
  have below : proofBase ≤ MEMORY_BYTES := by decide
  let loaded := execInstrBr state (.LD .x31 .x30 (BitVec.ofNat 12 (8*w)))
  have loadAddress : state.getReg .x30 + signExtend12 (BitVec.ofNat 12 (8*w)) = BitVec.ofNat 64 (S+8*w) := by
    rw [from_, offset, ← BitVec.ofNat_add]
  have storeAddress : loaded.getReg .x21 + signExtend12 (BitVec.ofNat 12 (8*w)) =
      BitVec.ofNat 64 (proofBase+8*count) := by
    have keep : loaded.getReg .x21 = state.getReg .x21 := by
      simp [loaded, execInstrBr, QOpening.getReg_setReg]
    rw [keep, to_, offset, ← BitVec.ofNat_add, target]
  have loadCode : program[start+2*w]? = some (.LD .x31 .x30 (BitVec.ofNat 12 (8*w))) := by
    have := code (2*w) (by rw [group_pairs_length]; omega)
    rw [this, group_pairs_load w live]
  have storeCode : program[start+2*w+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (8*w))) := by
    have := code (2*w+1) (by rw [group_pairs_length]; omega)
    rw [Nat.add_assoc, this, group_pairs_store w live]
  have loadValid : memoryArgumentsValid state (.LD .x31 .x30 (BitVec.ofNat 12 (8*w))) = true := by
    simp only [memoryArgumentsValid, memAccess, loadAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have storeValid : memoryArgumentsValid loaded (.SD .x21 .x31 (BitVec.ofNat 12 (8*w))) = true := by
    simp only [memoryArgumentsValid, memAccess, storeAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have loadPC : loaded.pc = BitVec.ofNat 64 (4096+4*(start+2*w+1)) :=
    (straight_pc state _ rfl).trans (pc_next _ _ pc)
  have run₁ := runs_one state _ (start+2*w) loadCode pc rfl loadValid
  have run₂ := runs_one loaded _ (start+2*w+1) storeCode loadPC rfl storeValid
  have value : loaded.getReg .x31 = init.getMem (BitVec.ofNat 64 (source count)) := by
    simp only [loaded, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp only [loadAddress, ite_true, ne_eq, reduceCtorEq, not_false_eq_true, and_self, named]
    exact inv.input _ (by omega) (by omega) (by omega)
  have memory : after.mem = (state.setMem (BitVec.ofNat 64 (proofBase+8*count))
      (init.getMem (BitVec.ofNat 64 (source count)))).mem := by
    show (execInstrBr loaded _).mem = _
    simp only [execInstrBr, storeAddress, value]
    rfl
  refine ⟨run₁.trans run₂, ?_, ?_, ?_⟩
  · exact (inv.store fits _ rfl).of_mem memory
  · show (execInstrBr loaded _).pc = _
    rw [straight_pc loaded _ rfl, straight_pc state _ rfl, BitVec.add_assoc]
    rfl
  · intro r other
    show (execInstrBr loaded _).getReg r = _
    simp [loaded, execInstrBr, QOpening.getReg_setReg, QOpening.getReg_setMem, Ne.symm other]

/-- The first `n ≤ 20` load/store pairs of a table group copy output words `count …`. -/
theorem group_block (init : MachineState) (source : Nat → Nat) (start S D count : Nat)
    (code : CodeAt start (groupPairs 20)) (aligned : S % 8 = 0) (low : trapdoorBase ≤ S)
    (high : S+160 ≤ proofBase) (target : D = proofBase+8*count)
    (fits : proofBase+8*(count+20) ≤ MEMORY_BYTES)
    (named : ∀ m < 20, source (count+m) = S+8*m) :
    ∀ n ≤ 20, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*start) →
      state.getReg .x30 = BitVec.ofNat 64 S → state.getReg .x21 = BitVec.ofNat 64 D →
      Inv init state source count →
      let after := (groupPairs n).foldl execInstrBr state
      Runs state after (2*n) (2*n) ∧ Inv init after source (count+n) ∧
        after.pc = BitVec.ofNat 64 (4096+4*(start+2*n)) ∧
        ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro n
  induction n with
  | zero =>
    intro _ state pc _ _ inv
    exact ⟨Runs.zero state, inv, pc, fun _ _ => rfl⟩
  | succ n ih =>
    intro le state pc from_ to_ inv
    obtain ⟨run, inv', pc', regs⟩ := ih (by omega) state pc from_ to_ inv
    let middle := (groupPairs n).foldl execInstrBr state
    have step := group_step init middle source start n (count+n) S D (by omega) code pc'
      ((regs .x30 (by decide)).trans from_) ((regs .x21 (by decide)).trans to_)
      (by omega) aligned low high (by omega) (named n (by omega)) inv'
    obtain ⟨run₂, inv₂, pc₂, regs₂⟩ := step
    intro after
    have shape : after = execInstrBr (execInstrBr middle (.LD .x31 .x30 (BitVec.ofNat 12 (8*n))))
        (.SD .x21 .x31 (BitVec.ofNat 12 (8*n))) := by
      simp [after, middle, group_pairs_succ, List.foldl_append]
    rw [shape]
    refine ⟨(run.trans run₂).cast (by omega) (by omega), by simpa [Nat.add_assoc] using inv₂, ?_, ?_⟩
    · rw [pc₂, pc', show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 1
    · intro r other
      exact (regs₂ r other).trans (regs r other)

/-- A whole table group: 20 doublewords, then `x30 += 368` and `x21 += 160`. -/
theorem group_run (init state : MachineState) (source : Nat → Nat) (start S count : Nat)
    (code : CodeAt start groupCode) (pc : state.pc = BitVec.ofNat 64 (4096+4*start))
    (from_ : state.getReg .x30 = BitVec.ofNat 64 S)
    (to_ : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*count))
    (aligned : S % 8 = 0) (low : trapdoorBase ≤ S) (high : S+160 ≤ proofBase)
    (fits : proofBase+8*(count+20) ≤ MEMORY_BYTES)
    (named : ∀ m < 20, source (count+m) = S+8*m) (inv : Inv init state source count) :
    let after := groupCode.foldl execInstrBr state
    Runs state after 42 42 ∧ Inv init after source (count+20) ∧
      after.pc = BitVec.ofNat 64 (4096+4*(start+42)) ∧
      after.getReg .x30 = BitVec.ofNat 64 (S+368) ∧
      after.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(count+20)) ∧
      ∀ r, r ≠ .x31 → r ≠ .x30 → r ≠ .x21 → after.getReg r = state.getReg r := by
  intro after
  have pairsCode : CodeAt start (groupPairs 20) := by
    intro i hi
    rw [group_pairs_length] at hi
    rw [code i (by rw [group_code_length]; omega), group_code_split,
      List.getElem?_append_left (by rw [group_pairs_length]; omega)]
  have tailCode : CodeAt (start+40) [.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] := by
    intro i hi
    have two : i < 2 := by simpa using hi
    rw [Nat.add_assoc, code (40+i) (by rw [group_code_length]; omega), group_code_split,
      List.getElem?_append_right (by rw [group_pairs_length]; omega), group_pairs_length,
      show 40 + i - 2*20 = i by omega]
  obtain ⟨run₁, inv₁, pc₁, regs₁⟩ := group_block init source start S (proofBase+8*count) count pairsCode
    aligned low high rfl fits named 20 le_rfl state pc from_ to_ inv
  let middle := (groupPairs 20).foldl execInstrBr state
  have pure₂ : ([.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] : List Instr).all pureOp = true := rfl
  have run₂ := runs_pure _ (start+40) middle tailCode (by simpa using pc₁) pure₂
  have shape : after = ([.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] : List Instr).foldl execInstrBr middle := by
    simp only [after, middle, group_code_split, List.foldl_append]
  have proofBound : proofBase+8*(count+20) < 2^64 := by
    have : MEMORY_BYTES < 2^64 := by decide
    omega
  have trapBound : S+368 < 2^64 := by
    have : proofBase = 10804535392 := rfl
    omega
  rw [shape]
  refine ⟨(run₁.trans run₂).cast rfl (by simp [cost, instructionCycles]), ?_, ?_, ?_, ?_, ?_⟩
  · exact inv₁.of_mem (pure_mem _ _ pure₂)
  · rw [pure_pc _ _ pure₂, pc₁]
    rw [show (4096+4*(start+2*20)) = 4096+4*(start+40) by omega, show (4*List.length
      ([.ADDI .x30 .x30 368, .ADDI .x21 .x21 160] : List Instr)) = 8 by rfl, ← BitVec.ofNat_add]
    congr 1
  · simp [execInstrBr, signExtend12]
    rw [regs₁ .x30 (by decide), from_, ← BitVec.ofNat_add]
  · simp [execInstrBr, signExtend12]
    rw [regs₁ .x21 (by decide), to_, ← BitVec.ofNat_add,
      show proofBase+8*count+160 = proofBase+8*(count+20) by omega]
  · intro r a b c
    simp [execInstrBr, Ne.symm b, Ne.symm c]
    exact regs₁ r a

/-- Copy the last group's 20 doublewords and advance only the proof cursor. -/
theorem last_group_run (init state : MachineState) (source : Nat → Nat) (start S count : Nat)
    (code : CodeAt start lastGroupCode) (pc : state.pc = BitVec.ofNat 64 (4096+4*start))
    (from_ : state.getReg .x30 = BitVec.ofNat 64 S)
    (to_ : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*count))
    (aligned : S % 8 = 0) (low : trapdoorBase ≤ S) (high : S+160 ≤ proofBase)
    (fits : proofBase+8*(count+20) ≤ MEMORY_BYTES)
    (named : ∀ m < 20, source (count+m) = S+8*m) (inv : Inv init state source count) :
    ∃ after : MachineState, Runs state after 41 41 ∧ Inv init after source (count+20) ∧
      after.pc = BitVec.ofNat 64 (4096+4*(start+41)) ∧
      after.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(count+20)) ∧
      ∀ r, r ≠ .x31 → r ≠ .x21 → after.getReg r = state.getReg r := by
  have split : lastGroupCode = groupPairs 20 ++ [.ADDI .x21 .x21 160] := rfl
  have pairsCode : CodeAt start (groupPairs 20) := by
    intro i hi
    rw [code i (by rw [last_group_code_length]; rw [group_pairs_length] at hi; omega),
      split, List.getElem?_append_left hi]
  have tailCode : CodeAt (start+40) [.ADDI .x21 .x21 160] := by
    intro i hi
    have zero : i = 0 := by simpa using hi
    subst i
    simpa [split, group_pairs_length, List.getElem?_append_right] using code 40 (by rw [last_group_code_length]; decide)
  obtain ⟨run₁, inv₁, pc₁, regs₁⟩ := group_block init source start S (proofBase+8*count) count pairsCode
    aligned low high rfl fits named 20 le_rfl state pc from_ to_ inv
  let middle := (groupPairs 20).foldl execInstrBr state
  let tail : List Instr := [.ADDI .x21 .x21 160]
  have pure₂ : tail.all pureOp = true := rfl
  have run₂ := runs_pure tail (start+40) middle tailCode (by simpa using pc₁) pure₂
  refine ⟨tail.foldl execInstrBr middle, (run₁.trans run₂).cast rfl (by simp [tail, cost, instructionCycles]),
    inv₁.of_mem (pure_mem _ _ pure₂), ?_, ?_, ?_⟩
  · rw [pure_pc _ _ pure₂, pc₁, show (4*tail.length) = 4 from rfl, ← BitVec.ofNat_add]
    congr 1
  · simp [tail, execInstrBr, signExtend12]
    rw [regs₁ .x21 (by decide), to_, ← BitVec.ofNat_add,
      show proofBase+8*count+160 = proofBase+8*(count+20) by omega]
  · intro r a b
    simpa [tail, execInstrBr, Ne.symm b] using regs₁ r a

/-! ### One table level -/

theorem group_aligned' : ∀ L < 4, (pentaGroupBase (7+L)+40) % 8 = 0 := by decide

/-- Groups `0 … g-1` of table level `L`. -/
theorem level_groups (init : MachineState) (source : Nat → Nat) (L base : Nat) (hL : L < 4)
    (fits : proofBase + 8*(base + 1100) ≤ MEMORY_BYTES)
    (named : ∀ g < pentaCount (7+L+1), ∀ m < 20,
      source (base + 20*(tableFirst L + g) + m) = trapdoorBase + pentaGroupBase (7+L) + 40 + 368*g + 8*m) :
    ∀ g ≤ pentaCount (7+L+1) - 1, ∀ state : MachineState,
      state.pc = BitVec.ofNat 64 (4096+4*(527 + levelOffset L + 2)) →
      state.getReg .x30 = BitVec.ofNat 64 (trapdoorBase + pentaGroupBase (7+L) + 40) →
      state.getReg .x21 = BitVec.ofNat 64 (proofBase + 8*(base + 20*tableFirst L)) →
      Inv init state source (base + 20*tableFirst L) →
      let after := (List.replicate g groupCode).flatten.foldl execInstrBr state
      Runs state after (42*g) (42*g) ∧ Inv init after source (base + 20*(tableFirst L + g)) ∧
        after.pc = BitVec.ofNat 64 (4096+4*(527 + levelOffset L + 2 + 42*g)) ∧
        after.getReg .x30 = BitVec.ofNat 64 (trapdoorBase + pentaGroupBase (7+L) + 40 + 368*g) ∧
        after.getReg .x21 = BitVec.ofNat 64 (proofBase + 8*(base + 20*(tableFirst L + g))) ∧
        ∀ r, r ≠ .x31 → r ≠ .x30 → r ≠ .x21 → after.getReg r = state.getReg r := by
  have last := table_first_next L hL
  have room := group_room (7+L) (by omega)
  have aligned := group_aligned' L hL
  have tb : trapdoorBase = 4294971424 := rfl
  have pb : proofBase = 10804535392 := rfl
  have first : tableFirst L + pentaCount (7+L+1) ≤ 55 := by
    rw [last]; split <;> (interval_cases L <;> simp_all [tableFirst])
  intro g
  induction g with
  | zero =>
    intro _ state pc from_ to_ inv
    exact ⟨Runs.zero state, inv, pc, from_, to_, fun _ _ _ _ => rfl⟩
  | succ g ih =>
    intro le state pc from_ to_ inv
    obtain ⟨run, inv', pc', from', to', regs⟩ := ih (by omega) state pc from_ to_ inv
    let middle := (List.replicate g groupCode).flatten.foldl execInstrBr state
    obtain ⟨run₂, inv₂, pc₂, from₂, to₂, regs₂⟩ := group_run init middle source
      (527 + levelOffset L + 2 + 42*g) (trapdoorBase + pentaGroupBase (7+L) + 40 + 368*g)
      (base + 20*(tableFirst L + g)) (group_code_at L g hL (by omega)) pc' from' to'
      (by omega) (by omega) (by omega) (by omega) (named g (by omega)) inv'
    intro after
    have shape : after = groupCode.foldl execInstrBr middle := by
      simp only [after, middle, List.replicate_succ', List.flatten_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.foldl_append]
    rw [shape]
    refine ⟨(run.trans run₂).cast (by rw [Nat.mul_succ]) (by rw [Nat.mul_succ]), ?_, ?_, ?_, ?_, ?_⟩
    · exact inv₂.cast_count (by omega)
    · rw [pc₂, show 4096+4*(527 + levelOffset L + 2 + 42*g + 42) =
        4096+4*(527 + levelOffset L + 2 + 42*(g+1)) by omega]
    · rw [from₂, show trapdoorBase + pentaGroupBase (7+L) + 40 + 368*g + 368 =
        trapdoorBase + pentaGroupBase (7+L) + 40 + 368*(g+1) by omega]
    · rw [to₂, show proofBase + 8*(base + 20*(tableFirst L + g) + 20) =
        proofBase + 8*(base + 20*(tableFirst L + (g+1))) by omega]
    · intro r a b c
      exact (regs₂ r a b c).trans (regs r a b c)

/-- Table level `L`: the head (`lui`, `add`) and all its groups. -/
theorem level_run (init state : MachineState) (source : Nat → Nat) (L base : Nat) (hL : L < 4)
    (fits : proofBase + 8*(base + 1100) ≤ MEMORY_BYTES)
    (named : ∀ g < pentaCount (7+L+1), ∀ m < 20,
      source (base + 20*(tableFirst L + g) + m) = trapdoorBase + pentaGroupBase (7+L) + 40 + 368*g + 8*m)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(527 + levelOffset L)))
    (heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (to_ : state.getReg .x21 = BitVec.ofNat 64 (proofBase + 8*(base + 20*tableFirst L)))
    (inv : Inv init state source (base + 20*tableFirst L)) :
    ∃ after : MachineState,
      Runs state after (2 + 42*(pentaCount (7+L+1) - 1) + 41) (2 + 42*(pentaCount (7+L+1) - 1) + 41) ∧
      Inv init after source (base + 20*(tableFirst L + pentaCount (7+L+1))) ∧
      after.pc = BitVec.ofNat 64 (4096+4*(527 + levelOffset L + 2 + 42*(pentaCount (7+L+1) - 1) + 41)) ∧
      after.getReg .x21 = BitVec.ofNat 64 (proofBase + 8*(base + 20*(tableFirst L + pentaCount (7+L+1)))) ∧
      ∀ r, r ≠ .x11 → r ≠ .x31 → r ≠ .x30 → r ≠ .x21 → after.getReg r = state.getReg r := by
  let head : List Instr := [.LUI .x11 (BitVec.ofNat 20 (groupPage (7+L))), .ADD .x30 .x11 .x9]
  have pure₁ : head.all pureOp = true := rfl
  have run₁ := runs_pure head (527 + levelOffset L) state (level_head_code L hL) pc pure₁
  let s₁ := head.foldl execInstrBr state
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(527 + levelOffset L + 2)) := by
    rw [pure_pc _ _ pure₁, pc, show (4*head.length) = 8 from rfl, ← BitVec.ofNat_add]
    congr 1
  have keep₁ (r : Reg) (a : r ≠ .x11) (b : r ≠ .x30) : s₁.getReg r = state.getReg r := by
    simp [s₁, head, execInstrBr, Ne.symm a, Ne.symm b]
  have from₁ : s₁.getReg .x30 = BitVec.ofNat 64 (trapdoorBase + pentaGroupBase (7+L) + 40) := by
    simp [s₁, head, execInstrBr, heap, lui_page (7+L) (by omega)]
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  let groups := pentaCount (7+L+1) - 1
  have last : groups + 1 = pentaCount (7+L+1) := by
    dsimp only [groups]
    obtain ⟨c8, c9, c10, c11⟩ := penta_counts
    interval_cases L <;> simp [c8, c9, c10, c11]
  have room := group_room (7+L) (by omega)
  have aligned := group_aligned' L hL
  have tb : trapdoorBase = 4294971424 := rfl
  have pb : proofBase = 10804535392 := rfl
  have endBound : tableFirst L + pentaCount (7+L+1) ≤ 55 := by
    rw [table_first_next L hL]
    split <;> (interval_cases L <;> simp_all [tableFirst])
  obtain ⟨run₂, inv₂, pc₂, from₂, to₂, regs₂⟩ := level_groups init source L base hL fits named
    groups le_rfl s₁ pc₁ from₁ ((keep₁ .x21 (by decide) (by decide)).trans to_)
    (inv.of_mem (pure_mem _ _ pure₁))
  obtain ⟨s₃, run₃, inv₃, pc₃, to₃, regs₃⟩ := last_group_run init _ source
    (527 + levelOffset L + 2 + 42*groups) _ (base + 20*(tableFirst L + groups))
    (last_group_code_at L hL) pc₂ from₂ to₂ (by omega) (by omega) (by omega)
    (by omega) (named groups (by omega)) inv₂
  refine ⟨s₃, (run₁.trans (run₂.trans run₃)).cast (by simp [head, groups]; omega)
    (by simp [head, groups, cost, instructionCycles]; omega),
    inv₃.cast_count (by omega), pc₃, ?_, ?_⟩
  · rw [to₃, ← last]
    congr 1
  · intro r a b c d
    exact (regs₃ r b d).trans ((regs₂ r b c d).trans (keep₁ r a c))

/-! ### The whole table copy -/

theorem footer_jump (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*106)) :
    Runs state (state.setPC (BitVec.ofNat 64 (4096+4*527))) 1 1 := by
  obtain ⟨code, _, _⟩ := exit_codes
  have shape : execInstrBr state footerJump = state.setPC (BitVec.ofNat 64 (4096+4*527)) := by
    change state.setPC (state.pc + signExtend21 1684) = _
    rw [pc]
    exact congrArg state.setPC (by decide)
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program state 106 _ code pc)
    (show ordinaryStep state (.base footerJump) = some (execInstrBr state footerJump) from rfl), shape]
  rfl

/-- From the record latch's fall-through at word 106 to the exit at word 2841. -/
theorem footer_run (init state : MachineState) (positions : Positions) (nonempty : 0 < positions.card)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*106))
    (heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase)
    (to_ : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(114*positions.card)))
    (inv : Inv init state (wordSource positions) (114*positions.card)) :
    ∃ final : MachineState,
      Runs state final 2315 2315 ∧ final.pc = BitVec.ofNat 64 (4096+4*2841) ∧
      Inv init final (proofSource positions) (114*positions.card+1100) ∧
      final.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(114*positions.card+1100)) ∧
      ∀ r, r ≠ .x11 → r ≠ .x31 → r ≠ .x30 → r ≠ .x21 → final.getReg r = state.getReg r := by
  obtain ⟨c8, c9, c10, c11⟩ := penta_counts
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  let base := 114*positions.card
  have fits : proofBase + 8*(base + 1100) ≤ MEMORY_BYTES := by
    have : proofBase = 10804535392 := rfl
    have : MEMORY_BYTES = 68719476736 := rfl
    omega
  have named (L : Nat) (hL : L < 4) : ∀ g < pentaCount (7+L+1), ∀ m < 20,
      proofSource positions (base + 20*(tableFirst L + g) + m) =
        trapdoorBase + pentaGroupBase (7+L) + 40 + 368*g + 8*m := by
    intro g hg m hm
    unfold proofSource
    rw [if_neg (by omega), show base + 20*(tableFirst L + g) + m - 114*positions.card =
      20*(tableFirst L + g) + m by omega]
    exact table_source_group L g m hL hg hm
  have inv₀ : Inv init (state.setPC (BitVec.ofNat 64 (4096+4*527))) (proofSource positions) base := by
    refine ⟨fun a l h alg => inv.input a l h alg, fun u hu => ?_⟩
    have out := inv.output u hu
    unfold proofSource
    rw [if_pos hu]
    exact out
  have run₀ := footer_jump state pc
  let s₀ := state.setPC (BitVec.ofNat 64 (4096+4*527))
  have regs₀ (r : Reg) : s₀.getReg r = state.getReg r := MachineState.getReg_setPC
  -- level 7
  obtain ⟨s₁, run₁, inv₁, pc₁, to₁, regs₁⟩ := level_run init s₀ (proofSource positions) 0 base (by decide)
    fits (named 0 (by decide)) rfl ((regs₀ .x9).trans heap) ((regs₀ .x21).trans to_) inv₀
  simp only [Nat.reduceAdd, Nat.reduceSub, c8, tableFirst, levelOffset] at run₁ inv₁ pc₁ to₁
  -- level 8
  obtain ⟨s₂, run₂, inv₂, pc₂, to₂, regs₂⟩ := level_run init s₁ (proofSource positions) 1 base (by decide)
    fits (named 1 (by decide)) (by rw [pc₁]; rfl) ((regs₁ .x9 (by decide) (by decide) (by decide) (by decide)).trans
      ((regs₀ .x9).trans heap)) (by rw [to₁]; rfl) inv₁
  simp only [Nat.reduceAdd, Nat.reduceSub, c9, tableFirst, levelOffset] at run₂ inv₂ pc₂ to₂
  -- level 9
  obtain ⟨s₃, run₃, inv₃, pc₃, to₃, regs₃⟩ := level_run init s₂ (proofSource positions) 2 base (by decide)
    fits (named 2 (by decide)) (by rw [pc₂]; rfl) ((regs₂ .x9 (by decide) (by decide) (by decide) (by decide)).trans
      ((regs₁ .x9 (by decide) (by decide) (by decide) (by decide)).trans ((regs₀ .x9).trans heap)))
    (by rw [to₂]; rfl) inv₂
  simp only [Nat.reduceAdd, Nat.reduceSub, c10, tableFirst, levelOffset] at run₃ inv₃ pc₃ to₃
  -- level 10
  obtain ⟨s₄, run₄, inv₄, pc₄, to₄, regs₄⟩ := level_run init s₃ (proofSource positions) 3 base (by decide)
    fits (named 3 (by decide)) (by rw [pc₃]; rfl) ((regs₃ .x9 (by decide) (by decide) (by decide) (by decide)).trans
      ((regs₂ .x9 (by decide) (by decide) (by decide) (by decide)).trans
        ((regs₁ .x9 (by decide) (by decide) (by decide) (by decide)).trans ((regs₀ .x9).trans heap))))
    (by rw [to₃]; rfl) inv₃
  simp only [Nat.reduceAdd, Nat.reduceSub, c11, tableFirst, levelOffset] at run₄ inv₄ pc₄ to₄
  refine ⟨s₄, (run₀.trans (run₁.trans (run₂.trans (run₃.trans run₄)))).cast rfl rfl, pc₄, inv₄, to₄, ?_⟩
  intro r a b c d
  rw [regs₄ r a b c d, regs₃ r a b c d, regs₂ r a b c d, regs₁ r a b c d, regs₀ r]

end TwoPermutationPrototype.QuadOpening
