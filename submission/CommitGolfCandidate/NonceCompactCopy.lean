import CommitGolfCandidate.NonceCompactFetch
import CommitGolfCandidate.S6Codec

/-! The two copy routines of the compaction: the halfword loop (words 217..223, `x28` halfwords)
and the 30-byte field copy (words 224..256). Both read at x23 and write at x25, moving the
internal proof down in place; the invariant `NonceCompacted` says which output bytes are done. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-! ### Words, bytes and single steps -/

theorem s6_add_ofNat (left right : Nat) :
    (BitVec.ofNat 64 left : Word) + BitVec.ofNat 64 right = BitVec.ofNat 64 (left + right) :=
  (BitVec.ofNat_add left right).symm

theorem s6_ofNat_succ (value : Nat) : (BitVec.ofNat 64 value : Word) + 1 = BitVec.ofNat 64 (value + 1) :=
  s6_add_ofNat value 1

theorem s6_ofNat_ne {left right : Nat} (different : left ≠ right) (leftSmall : left < 2 ^ 64)
    (rightSmall : right < 2 ^ 64) : (BitVec.ofNat 64 left : Word) ≠ BitVec.ofNat 64 right := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftSmall, Nat.mod_eq_of_lt rightSmall] at numeric
  exact different numeric

theorem s6_ofNat_eq_zero (value : Nat) (small : value < 2 ^ 64) :
    (BitVec.ofNat 64 value : Word) = 0 ↔ value = 0 := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
    exact numeric
  · rintro rfl
    rfl

theorem s6_decrement (count : Nat) (positive : 0 < count) :
    BitVec.ofNat 64 count + signExtend12 (4095 : BitVec 12) = BitVec.ofNat 64 (count - 1) := by
  rw [show signExtend12 (4095 : BitVec 12) = -(1 : Word) by decide]
  have equation : count = count - 1 + 1 := by omega
  conv_lhs => rw [equation]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp

theorem s6_pc_next (k : Nat) :
    (BitVec.ofNat 64 (4864 + 4 * k) : Word) + 4 = BitVec.ofNat 64 (4864 + 4 * (k + 1)) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, s6_add_ofNat]
  congr 1

theorem s6_valid (address bytes : Nat) (aligned : address % bytes = 0)
    (inside : address + bytes ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 address) bytes = true := by
  have small : address < 2 ^ 64 := by
    unfold MEMORY_BYTES at inside
    omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Bool.and_eq_true,
    decide_eq_true_eq]
  exact ⟨inside, aligned⟩

theorem s6_byte_of_mem {left right : MachineState} (same : left.mem = right.mem) (query : Word) :
    left.getByte query = right.getByte query := by
  simp only [MachineState.getByte, MachineState.getMem, same]

theorem s6_set_reg_mem (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by
  cases reg <;> rfl

theorem s6_set_half_reg (state : MachineState) (address : Word) (half : BitVec 16) (reg : Reg) :
    (state.setHalfword address half).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem s6_step (state : MachineState) (k : Nat) (inside : k < 65) (instruction : Instr)
    (table : s6CompactInstrs.getD k .EBREAK = instruction)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * k))
    (stepped : ordinaryStep state (.base instruction) = some (execInstrBr state instruction))
    (cycles : instructionCycles (.base instruction) = 1) :
    NonceRuns s6OpeningImage 1 state (execInstrBr state instruction) := by
  subst table
  exact nonce_runs_step (s6_compact_fetch state k inside pc) stepped cycles

/-- ADDI effects. -/
theorem s6_addi_reg (state : MachineState) (rd rs : Reg) (imm : BitVec 12) (reg : Reg)
    (outside : reg ≠ rd) : (execInstrBr state (.ADDI rd rs imm)).getReg reg = state.getReg reg := by
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem s6_addi_self (state : MachineState) (rd rs : Reg) (imm : BitVec 12) (nonzero : rd ≠ .x0) :
    (execInstrBr state (.ADDI rd rs imm)).getReg rd = state.getReg rs + signExtend12 imm := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq nonzero]

theorem s6_addi_mem (state : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr state (.ADDI rd rs imm)).mem = state.mem := by
  simp only [execInstrBr, MachineState.setPC, s6_set_reg_mem]

theorem s6_addi_pc (state : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr state (.ADDI rd rs imm)).pc = state.pc + 4 := rfl

theorem s6_branch_reg (state : MachineState) (left right : Reg) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE left right offset)).getReg reg = state.getReg reg ∧
    (execInstrBr state (.BEQ left right offset)).getReg reg = state.getReg reg := by
  constructor <;> simp only [execInstrBr] <;> split <;> exact MachineState.getReg_setPC

theorem s6_branch_mem (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BNE left right offset)).mem = state.mem ∧
    (execInstrBr state (.BEQ left right offset)).mem = state.mem := by
  constructor <;> simp only [execInstrBr] <;> split <;> rfl

theorem s6_bne_pc (state : MachineState) (reg : Reg) (offset : BitVec 13) (value : Nat)
    (small : value < 2 ^ 64) (current : state.getReg reg = BitVec.ofNat 64 value) :
    (execInstrBr state (.BNE reg .x0 offset)).pc =
      if value = 0 then state.pc + 4 else state.pc + signExtend13 offset := by
  have zero : state.getReg .x0 = 0 := rfl
  simp only [execInstrBr, current, zero]
  by_cases empty : value = 0
  · subst value
    simp [MachineState.setPC]
  · have nonzero : (BitVec.ofNat 64 value : Word) ≠ 0 := fun same =>
      empty ((s6_ofNat_eq_zero value small).mp same)
    have test : (BitVec.ofNat 64 value != (0 : Word)) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact nonzero
    rw [if_neg empty, if_pos test]
    rfl

theorem s6_beq_pc (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BEQ left right offset)).pc =
      if state.getReg left = state.getReg right then state.pc + signExtend13 offset else state.pc + 4 := by
  simp only [execInstrBr]
  by_cases same : state.getReg left = state.getReg right
  · simp [same, MachineState.setPC]
  · simp [same, MachineState.setPC]

theorem s6_jal_effect (state : MachineState) (rd : Reg) (offset : BitVec 21) (nonzero : rd ≠ .x0) :
    (execInstrBr state (.JAL rd offset)).pc = state.pc + signExtend21 offset ∧
    (execInstrBr state (.JAL rd offset)).getReg rd = state.pc + 4 ∧
    (∀ reg, reg ≠ rd → (execInstrBr state (.JAL rd offset)).getReg reg = state.getReg reg) ∧
    (execInstrBr state (.JAL rd offset)).mem = state.mem := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq nonzero]
  · intro reg outside
    simp only [execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]
  · simp only [execInstrBr, MachineState.setPC, s6_set_reg_mem]

theorem s6_compact_jal_zero (state : MachineState) (offset : BitVec 21) :
    (execInstrBr state (.JAL .x0 offset)).pc = state.pc + signExtend21 offset ∧
    (∀ reg, (execInstrBr state (.JAL .x0 offset)).getReg reg = state.getReg reg) ∧
    (execInstrBr state (.JAL .x0 offset)).mem = state.mem := by
  refine ⟨rfl, ?_, rfl⟩
  intro reg
  rfl

theorem s6_return_effect (state : MachineState)
    (aligned : state.getReg .x1 &&& ~~~(1 : Word) = state.getReg .x1) :
    (execInstrBr state (.JALR .x0 .x1 0)).pc = state.getReg .x1 ∧
    (∀ reg, (execInstrBr state (.JALR .x0 .x1 0)).getReg reg = state.getReg reg) ∧
    (execInstrBr state (.JALR .x0 .x1 0)).mem = state.mem := by
  refine ⟨?_, fun reg => rfl, rfl⟩
  simpa [execInstrBr, signExtend12, MachineState.setPC] using aligned

/-! ### The compaction invariant -/

/-- Output bytes `[base, base + n)` hold the packed proof, read from the internal proof of `orig`
at `base`; every other byte is still the original. -/
structure NonceCompacted (orig : MachineState) (base count n : Nat) (state : MachineState) : Prop where
  packed : ∀ k < n, state.getByte (BitVec.ofNat 64 (base + k)) =
    orig.getByte (BitVec.ofNat 64 (base + s6PackSource count k))
  frame : ∀ query : Word, (∀ k < n, query ≠ BitVec.ofNat 64 (base + k)) →
    state.getByte query = orig.getByte query

theorem nonce_compacted_start (orig : MachineState) (base count : Nat) :
    NonceCompacted orig base count 0 orig :=
  ⟨fun k inside => absurd inside (Nat.not_lt_zero k), fun _ _ => rfl⟩

theorem nonce_compacted_mem {orig state next : MachineState} {base count n : Nat}
    (before : NonceCompacted orig base count n state) (same : next.mem = state.mem) :
    NonceCompacted orig base count n next :=
  ⟨fun k inside => (s6_byte_of_mem same _).trans (before.packed k inside),
   fun query outside => (s6_byte_of_mem same query).trans (before.frame query outside)⟩

theorem nonce_compacted_pair (orig state next : MachineState) (base count n source : Nat)
    (before : NonceCompacted orig base count n state)
    (effect : ∀ query, next.getByte query =
      if query = BitVec.ofNat 64 (base + n) then state.getByte (BitVec.ofNat 64 (base + source))
      else if query = BitVec.ofNat 64 (base + n) + 1 then
        state.getByte (BitVec.ofNat 64 (base + source) + 1)
      else state.getByte query)
    (first : s6PackSource count n = source) (second : s6PackSource count (n + 1) = source + 1)
    (ahead : n ≤ source) (small : base + source + 2 < 2 ^ 64) :
    NonceCompacted orig base count (n + 2) next := by
  simp only [s6_ofNat_succ] at effect
  have unread : ∀ extra < 2, state.getByte (BitVec.ofNat 64 (base + source + extra)) =
      orig.getByte (BitVec.ofNat 64 (base + source + extra)) := by
    intro extra bound
    apply before.frame
    intro k inside
    exact s6_ofNat_ne (by omega) (by omega) (by omega)
  constructor
  · intro k inside
    rw [effect]
    by_cases low : k < n
    · rw [if_neg (s6_ofNat_ne (by omega) (by omega) (by omega)),
        if_neg (s6_ofNat_ne (by omega) (by omega) (by omega))]
      exact before.packed k low
    · by_cases middle : k = n
      · subst k
        rw [if_pos rfl, first]
        simpa only [Nat.add_zero] using unread 0 (by omega)
      · have last : k = n + 1 := by omega
        subst k
        rw [if_neg (s6_ofNat_ne (by omega) (by omega) (by omega)),
          if_pos (congrArg (BitVec.ofNat 64) (by omega)), second, ← Nat.add_assoc]
        exact unread 1 (by omega)
  · intro query outside
    rw [effect, if_neg (outside n (by omega)),
      if_neg (by
        have other := outside (n + 1) (by omega)
        rwa [← Nat.add_assoc] at other)]
    exact before.frame query (fun k inside => outside k (by omega))

/-! ### One halfword copy (lhu x6 / sh x6) -/

def s6CopyPair (offset : BitVec 12) (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr state (.LHU .x6 .x23 offset)) (.SH .x25 .x6 offset)

theorem s6_copy_pair_pc (offset : BitVec 12) (state : MachineState) :
    (s6CopyPair offset state).pc = state.pc + 4 + 4 := rfl

theorem s6_copy_pair_reg (offset : BitVec 12) (state : MachineState) (reg : Reg) (outside : reg ≠ .x6) :
    (s6CopyPair offset state).getReg reg = state.getReg reg := by
  simp only [s6CopyPair, execInstrBr, MachineState.getReg_setPC, s6_set_half_reg,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem s6_copy_pair_byte (offset : BitVec 12) (state : MachineState) (query : Word)
    (sourceEven : (state.getReg .x23 + signExtend12 offset).toNat % 2 = 0)
    (targetEven : (state.getReg .x25 + signExtend12 offset).toNat % 2 = 0) :
    (s6CopyPair offset state).getByte query =
      if query = state.getReg .x25 + signExtend12 offset then
        state.getByte (state.getReg .x23 + signExtend12 offset)
      else if query = state.getReg .x25 + signExtend12 offset + 1 then
        state.getByte (state.getReg .x23 + signExtend12 offset + 1)
      else state.getByte query := by
  let loaded := execInstrBr state (.LHU .x6 .x23 offset)
  have loadedMem : loaded.mem = state.mem := by
    simp only [loaded, execInstrBr, MachineState.setPC, s6_set_reg_mem]
  have loadedTarget : loaded.getReg .x25 = state.getReg .x25 := by
    simp only [loaded, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ Reg.x25)]
  have loadedValue : loaded.getReg .x6 =
      (state.getHalfword (state.getReg .x23 + signExtend12 offset)).zeroExtend 64 := by
    simp only [loaded, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ Reg.x0)]
  have shape : s6CopyPair offset state =
      (loaded.setHalfword (loaded.getReg .x25 + signExtend12 offset)
        ((loaded.getReg .x6).truncate 16)).setPC (loaded.pc + 4) := rfl
  have truncated : ∀ half : BitVec 16, (half.zeroExtend 64).truncate 16 = half := by
    intro half
    apply BitVec.eq_of_toNat_eq
    have bound := half.isLt
    simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth]
    omega
  rw [shape]
  change (loaded.setHalfword (loaded.getReg .x25 + signExtend12 offset)
    ((loaded.getReg .x6).truncate 16)).getByte query = _
  rw [half_set_read _ _ _ _ (by rw [loadedTarget]; exact targetEven), loadedTarget, loadedValue,
    truncated, half_get_low _ _ sourceEven, half_get_high _ _ sourceEven, s6_byte_of_mem loadedMem]

theorem s6_copy_pair_runs (state : MachineState) (k : Nat) (inside : k + 1 < 65) (offset : BitVec 12)
    (load : s6CompactInstrs.getD k .EBREAK = .LHU .x6 .x23 offset)
    (store : s6CompactInstrs.getD (k + 1) .EBREAK = .SH .x25 .x6 offset)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * k))
    (sourceValid : accessValid (state.getReg .x23 + signExtend12 offset) 2 = true)
    (targetValid : accessValid (state.getReg .x25 + signExtend12 offset) 2 = true) :
    NonceRuns s6OpeningImage 2 state (s6CopyPair offset state) := by
  have loadedTarget : (execInstrBr state (.LHU .x6 .x23 offset)).getReg .x25 = state.getReg .x25 := by
    simp only [execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ Reg.x25)]
  have first := s6_step state k (by omega) _ load pc
    (by simp [ordinaryStep, memoryArgumentsValid, memAccess, sourceValid]) rfl
  have second := s6_step (execInstrBr state (.LHU .x6 .x23 offset)) (k + 1) inside _ store
    (by rw [← s6_pc_next, ← pc]; rfl)
    (by simp [ordinaryStep, memoryArgumentsValid, memAccess, loadedTarget, targetValid]) rfl
  exact nonce_runs_trans first second

/-- The byte effect of a halfword copy in terms of `NonceCompacted`. -/
theorem s6_copy_pair_compacted (orig state : MachineState) (offset : BitVec 12) (base count n source : Nat)
    (before : NonceCompacted orig base count n state)
    (read : state.getReg .x23 + signExtend12 offset = BitVec.ofNat 64 (base + source))
    (write : state.getReg .x25 + signExtend12 offset = BitVec.ofNat 64 (base + n))
    (first : s6PackSource count n = source) (second : s6PackSource count (n + 1) = source + 1)
    (ahead : n ≤ source) (evenSource : (base + source) % 2 = 0) (evenTarget : (base + n) % 2 = 0)
    (small : base + source + 2 < 2 ^ 64) :
    NonceCompacted orig base count (n + 2) (s6CopyPair offset state) := by
  apply nonce_compacted_pair orig state _ base count n source before _ first second ahead small
  intro query
  rw [s6_copy_pair_byte offset state query
    (by rw [read, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show base + source < 2 ^ 64 by omega)]; exact evenSource)
    (by rw [write, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show base + n < 2 ^ 64 by omega)]; exact evenTarget),
    read, write]

/-! ### The halfword loop (words 217..223) -/

def s6HalfPass (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr (s6CopyPair 0 state)
    (.ADDI .x23 .x23 2)) (.ADDI .x25 .x25 2)) (.ADDI .x28 .x28 4095)) (.BNE .x28 .x0 8172)

/-- Registers of the halfword loop at word 217. -/
structure S6HalvesAt (orig : MachineState) (base count n source remaining : Nat)
    (state : MachineState) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4864 + 4 * 25)
  counter : state.getReg .x28 = BitVec.ofNat 64 remaining
  read : state.getReg .x23 = BitVec.ofNat 64 (base + source)
  write : state.getReg .x25 = BitVec.ofNat 64 (base + n)
  bytes : NonceCompacted orig base count n state

theorem s6_half_pass (orig state : MachineState) (base count n source remaining : Nat)
    (at_ : S6HalvesAt orig base count n source (remaining + 1) state)
    (first : s6PackSource count n = source) (second : s6PackSource count (n + 1) = source + 1)
    (ahead : n ≤ source) (evenBase : base % 2 = 0) (evenSource : source % 2 = 0) (evenN : n % 2 = 0)
    (small : base + source + 2 ≤ MEMORY_BYTES) (counterSmall : remaining + 1 < 2 ^ 64) :
    NonceRuns s6OpeningImage 6 state (s6HalfPass state) ∧
    (s6HalfPass state).pc = (if remaining = 0 then BitVec.ofNat 64 (4864 + 4 * 31)
      else BitVec.ofNat 64 (4864 + 4 * 25)) ∧
    (s6HalfPass state).getReg .x28 = BitVec.ofNat 64 remaining ∧
    (s6HalfPass state).getReg .x23 = BitVec.ofNat 64 (base + source + 2) ∧
    (s6HalfPass state).getReg .x25 = BitVec.ofNat 64 (base + n + 2) ∧
    (∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x28 →
      (s6HalfPass state).getReg reg = state.getReg reg) ∧
    NonceCompacted orig base count (n + 2) (s6HalfPass state) := by
  have bound : base + source + 2 < 2 ^ 64 := by unfold MEMORY_BYTES at small; omega
  have zeroExt : signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 := by decide
  have twoExt : signExtend12 (2 : BitVec 12) = BitVec.ofNat 64 2 := by decide
  let copied := s6CopyPair 0 state
  let s3 := execInstrBr copied (.ADDI .x23 .x23 2)
  let s4 := execInstrBr s3 (.ADDI .x25 .x25 2)
  let s5 := execInstrBr s4 (.ADDI .x28 .x28 4095)
  have copiedRuns := s6_copy_pair_runs state 25 (by omega) 0 rfl rfl at_.pc
    (by rw [at_.read, zeroExt, s6_add_ofNat, Nat.add_zero]; exact s6_valid _ _ (by omega) (by omega))
    (by rw [at_.write, zeroExt, s6_add_ofNat, Nat.add_zero]; exact s6_valid _ _ (by omega) (by omega))
  have copiedPc : copied.pc = BitVec.ofNat 64 (4864 + 4 * 27) := by
    rw [s6_copy_pair_pc, at_.pc, s6_pc_next, s6_pc_next]
  have copiedReg := s6_copy_pair_reg 0 state
  have run3 := s6_step copied 27 (by omega) (.ADDI .x23 .x23 2) rfl copiedPc rfl rfl
  have run4 := s6_step s3 28 (by omega) (.ADDI .x25 .x25 2) rfl (by rw [s6_addi_pc, copiedPc, s6_pc_next]) rfl rfl
  have run5 := s6_step s4 29 (by omega) (.ADDI .x28 .x28 4095) rfl
    (by rw [s6_addi_pc, s6_addi_pc, copiedPc, s6_pc_next, s6_pc_next]) rfl rfl
  have pc5 : s5.pc = BitVec.ofNat 64 (4864 + 4 * 30) := by
    rw [s6_addi_pc, s6_addi_pc, s6_addi_pc, copiedPc, s6_pc_next, s6_pc_next, s6_pc_next]
  have run6 := s6_step s5 30 (by omega) (.BNE .x28 .x0 8172) rfl pc5 rfl rfl
  have counter5 : s5.getReg .x28 = BitVec.ofNat 64 remaining := by
    rw [s6_addi_self _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), copiedReg _ (by decide), at_.counter, s6_decrement _ (by omega)]
    rfl
  have read5 : s5.getReg .x23 = BitVec.ofNat 64 (base + source + 2) := by
    rw [s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      s6_addi_self _ _ _ _ (by decide), copiedReg _ (by decide), at_.read, twoExt, s6_add_ofNat]
  have write5 : s5.getReg .x25 = BitVec.ofNat 64 (base + n + 2) := by
    rw [s6_addi_reg _ _ _ _ _ (by decide), s6_addi_self _ _ _ _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), copiedReg _ (by decide), at_.write, twoExt, s6_add_ofNat]
  have other5 : ∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x28 → s5.getReg reg = state.getReg reg := by
    intro reg r6 r23 r25 r28
    rw [s6_addi_reg _ _ _ _ _ r28, s6_addi_reg _ _ _ _ _ r25, s6_addi_reg _ _ _ _ _ r23, copiedReg _ r6]
  have mem5 : s5.mem = copied.mem := by
    rw [s6_addi_mem, s6_addi_mem, s6_addi_mem]
  have bytes : NonceCompacted orig base count (n + 2) copied :=
    s6_copy_pair_compacted orig state 0 base count n source at_.bytes
      (by rw [at_.read, zeroExt, s6_add_ofNat, Nat.add_zero]) (by rw [at_.write, zeroExt, s6_add_ofNat, Nat.add_zero])
      first second ahead (by omega) (by omega) bound
  have last := s6_branch_reg s5 .x28 .x0 8172
  refine ⟨nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans copiedRuns run3) run4) run5) run6,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (execInstrBr s5 (.BNE .x28 .x0 8172)).pc = _
    rw [s6_bne_pc s5 .x28 8172 remaining (by omega) counter5, pc5]
    by_cases empty : remaining = 0
    · rw [if_pos empty, if_pos empty, s6_pc_next]
    · rw [if_neg empty, if_neg empty]
      decide
  · exact (last .x28).1.trans counter5
  · exact (last .x23).1.trans read5
  · exact (last .x25).1.trans write5
  · intro reg r6 r23 r25 r28
    exact (last reg).1.trans (other5 reg r6 r23 r25 r28)
  · exact nonce_compacted_mem bytes ((s6_branch_mem s5 .x28 .x0 8172).1.trans mem5)

/-- The whole halfword loop and its return: `remaining + 1` halfwords. -/
theorem s6_halves_runs (orig : MachineState) (base count : Nat) :
    ∀ (remaining n source : Nat) (state : MachineState),
    S6HalvesAt orig base count n source (remaining + 1) state →
    (∀ i < 2 * (remaining + 1), s6PackSource count (n + i) = source + i) →
    n ≤ source → base % 2 = 0 → source % 2 = 0 → n % 2 = 0 →
    base + source + 2 * (remaining + 1) ≤ MEMORY_BYTES →
    state.getReg .x1 &&& ~~~(1 : Word) = state.getReg .x1 →
    ∃ next, NonceRuns s6OpeningImage (6 * (remaining + 1) + 1) state next ∧
      next.pc = state.getReg .x1 ∧
      next.getReg .x23 = BitVec.ofNat 64 (base + source + 2 * (remaining + 1)) ∧
      next.getReg .x25 = BitVec.ofNat 64 (base + n + 2 * (remaining + 1)) ∧
      (∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x28 → next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (n + 2 * (remaining + 1)) next := by
  intro remaining
  induction remaining with
  | zero =>
    intro n source state at_ sources ahead evenBase evenSource evenN small aligned
    have pass := s6_half_pass orig state base count n source 0 at_ (by simpa using sources 0 (by omega))
      (sources 1 (by omega)) ahead evenBase evenSource evenN (by omega) (by decide)
    obtain ⟨runs, pc, counter, read, write, other, bytes⟩ := pass
    rw [if_pos rfl] at pc
    have link : (s6HalfPass state).getReg .x1 = state.getReg .x1 := other .x1 (by decide) (by decide) (by decide) (by decide)
    have returned := s6_step (s6HalfPass state) 31 (by omega) (.JALR .x0 .x1 0) rfl pc rfl rfl
    have effect := s6_return_effect (s6HalfPass state) (by rw [link]; exact aligned)
    refine ⟨_, nonce_runs_trans runs returned, ?_, ?_, ?_, ?_, ?_⟩
    · rw [effect.1, link]
    · rw [effect.2.1, read]
    · rw [effect.2.1, write]
    · intro reg r6 r23 r25 r28
      rw [effect.2.1, other reg r6 r23 r25 r28]
    · exact nonce_compacted_mem bytes effect.2.2
  | succ remaining ih =>
    intro n source state at_ sources ahead evenBase evenSource evenN small aligned
    have pass := s6_half_pass orig state base count n source (remaining + 1) at_
      (by simpa using sources 0 (by omega)) (sources 1 (by omega)) ahead evenBase evenSource evenN
      (by omega) (by unfold MEMORY_BYTES at small; omega)
    obtain ⟨runs, pc, counter, read, write, other, bytes⟩ := pass
    rw [if_neg (by omega)] at pc
    have nextAt : S6HalvesAt orig base count (n + 2) (source + 2) (remaining + 1) (s6HalfPass state) :=
      ⟨pc, counter, by rw [read, Nat.add_assoc], by rw [write, Nat.add_assoc], bytes⟩
    have nextSources : ∀ i < 2 * (remaining + 1), s6PackSource count (n + 2 + i) = source + 2 + i := by
      intro i inside
      have shifted := sources (i + 2) (by omega)
      rw [show n + (i + 2) = n + 2 + i by omega] at shifted
      rw [shifted]
      omega
    have link : (s6HalfPass state).getReg .x1 = state.getReg .x1 :=
      other .x1 (by decide) (by decide) (by decide) (by decide)
    obtain ⟨next, nextRuns, nextPc, nextRead, nextWrite, nextOther, nextBytes⟩ :=
      ih (n + 2) (source + 2) (s6HalfPass state) nextAt nextSources (by omega) evenBase (by omega)
        (by omega) (by omega) (by rw [link]; exact aligned)
    refine ⟨next, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have total := nonce_runs_trans runs nextRuns
      rwa [show 6 + (6 * (remaining + 1) + 1) = 6 * (remaining + 1 + 1) + 1 by ring] at total
    · rw [nextPc, link]
    · exact nextRead.trans (congrArg (BitVec.ofNat 64) (by omega))
    · exact nextWrite.trans (congrArg (BitVec.ofNat 64) (by omega))
    · intro reg r6 r23 r25 r28
      rw [nextOther reg r6 r23 r25 r28, other reg r6 r23 r25 r28]
    · rw [show n + 2 * (remaining + 1 + 1) = n + 2 + 2 * (remaining + 1) by ring]
      exact nextBytes

/-! ### The 30-byte field copy (words 224..256) -/

theorem s6_field_pairs (orig state : MachineState) (base count n source : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * 32))
    (read : state.getReg .x23 = BitVec.ofNat 64 (base + source))
    (write : state.getReg .x25 = BitVec.ofNat 64 (base + n))
    (before : NonceCompacted orig base count n state)
    (sources : ∀ i < 30, s6PackSource count (n + i) = source + i)
    (ahead : n ≤ source) (evenBase : base % 2 = 0) (evenSource : source % 2 = 0) (evenN : n % 2 = 0)
    (small : base + source + 30 ≤ MEMORY_BYTES) :
    ∀ j ≤ 15, ∃ next, NonceRuns s6OpeningImage (2 * j) state next ∧
      next.pc = BitVec.ofNat 64 (4864 + 4 * (32 + 2 * j)) ∧
      (∀ reg, reg ≠ .x6 → next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (n + 2 * j) next := by
  unfold MEMORY_BYTES at small
  intro j
  induction j with
  | zero => intro _; exact ⟨state, nonce_runs_zero _ _, pc, fun _ _ => rfl, before⟩
  | succ j ih =>
    intro bound
    obtain ⟨mid, runs, midPc, midReg, midBytes⟩ := ih (by omega)
    have jBound : j < 15 := by omega
    have offsetExt : signExtend12 (BitVec.ofNat 12 (2 * j)) = BitVec.ofNat 64 (2 * j) := by
      interval_cases j <;> decide
    have load : s6CompactInstrs.getD (32 + 2 * j) .EBREAK = .LHU .x6 .x23 (BitVec.ofNat 12 (2 * j)) := by
      interval_cases j <;> rfl
    have store : s6CompactInstrs.getD (32 + 2 * j + 1) .EBREAK = .SH .x25 .x6 (BitVec.ofNat 12 (2 * j)) := by
      interval_cases j <;> rfl
    have midRead : mid.getReg .x23 + signExtend12 (BitVec.ofNat 12 (2 * j)) =
        BitVec.ofNat 64 (base + (source + 2 * j)) := by
      rw [midReg _ (by decide), read, offsetExt, s6_add_ofNat, Nat.add_assoc]
    have midWrite : mid.getReg .x25 + signExtend12 (BitVec.ofNat 12 (2 * j)) =
        BitVec.ofNat 64 (base + (n + 2 * j)) := by
      rw [midReg _ (by decide), write, offsetExt, s6_add_ofNat, Nat.add_assoc]
    have pairRuns := s6_copy_pair_runs mid (32 + 2 * j) (by omega) _ load store midPc
      (by rw [midRead]; exact s6_valid _ _ (by omega) (by unfold MEMORY_BYTES; omega))
      (by rw [midWrite]; exact s6_valid _ _ (by omega) (by unfold MEMORY_BYTES; omega))
    have firstSource : s6PackSource count (n + 2 * j) = source + 2 * j := sources (2 * j) (by omega)
    have secondSource : s6PackSource count (n + 2 * j + 1) = source + 2 * j + 1 := by
      have shifted := sources (2 * j + 1) (by omega)
      rwa [← Nat.add_assoc, ← Nat.add_assoc] at shifted
    have pairBytes := s6_copy_pair_compacted orig mid _ base count (n + 2 * j) (source + 2 * j) midBytes
      midRead midWrite firstSource secondSource (by omega) (by omega) (by omega) (by omega)
    refine ⟨s6CopyPair (BitVec.ofNat 12 (2 * j)) mid, ?_, ?_, ?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring]
      exact nonce_runs_trans runs pairRuns
    · rw [s6_copy_pair_pc, midPc, s6_pc_next, s6_pc_next]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · intro reg outside
      rw [s6_copy_pair_reg _ _ _ outside, midReg _ outside]
    · rw [show n + 2 * (j + 1) = n + 2 * j + 2 by ring]
      exact pairBytes

theorem s6_field_runs (orig state : MachineState) (base count n source : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * 32))
    (read : state.getReg .x23 = BitVec.ofNat 64 (base + source))
    (write : state.getReg .x25 = BitVec.ofNat 64 (base + n))
    (aligned : state.getReg .x1 &&& ~~~(1 : Word) = state.getReg .x1)
    (before : NonceCompacted orig base count n state)
    (sources : ∀ i < 30, s6PackSource count (n + i) = source + i)
    (ahead : n ≤ source) (evenBase : base % 2 = 0) (evenSource : source % 2 = 0) (evenN : n % 2 = 0)
    (small : base + source + 30 ≤ MEMORY_BYTES) :
    ∃ next, NonceRuns s6OpeningImage 33 state next ∧ next.pc = state.getReg .x1 ∧
      next.getReg .x23 = BitVec.ofNat 64 (base + source + 30) ∧
      next.getReg .x25 = BitVec.ofNat 64 (base + n + 30) ∧
      (∀ reg, reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (n + 30) next := by
  obtain ⟨paired, runs, pairedPc, pairedReg, pairedBytes⟩ :=
    s6_field_pairs orig state base count n source pc read write before sources ahead evenBase
      evenSource evenN small 15 (le_refl 15)
  have thirtyExt : signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 := by decide
  let s1 := execInstrBr paired (.ADDI .x23 .x23 30)
  let s2 := execInstrBr s1 (.ADDI .x25 .x25 30)
  have run1 := s6_step paired 62 (by omega) (.ADDI .x23 .x23 30) rfl pairedPc rfl rfl
  have run2 := s6_step s1 63 (by omega) (.ADDI .x25 .x25 30) rfl
    (by rw [s6_addi_pc, pairedPc, s6_pc_next]) rfl rfl
  have pc2 : s2.pc = BitVec.ofNat 64 (4864 + 4 * 64) := by
    rw [s6_addi_pc, s6_addi_pc, pairedPc, s6_pc_next, s6_pc_next]
  have run3 := s6_step s2 64 (by omega) (.JALR .x0 .x1 0) rfl pc2 rfl rfl
  have link : s2.getReg .x1 = state.getReg .x1 := by
    rw [s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), pairedReg _ (by decide)]
  have effect := s6_return_effect s2 (by rw [link]; exact aligned)
  refine ⟨_, nonce_runs_trans (nonce_runs_trans (nonce_runs_trans runs run1) run2) run3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [effect.1, link]
  · rw [effect.2.1, s6_addi_reg _ _ _ _ _ (by decide), s6_addi_self _ _ _ _ (by decide),
      pairedReg _ (by decide), read, thirtyExt, s6_add_ofNat]
  · rw [effect.2.1, s6_addi_self _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      pairedReg _ (by decide), write, thirtyExt, s6_add_ofNat]
  · intro reg r6 r23 r25
    rw [effect.2.1, s6_addi_reg _ _ _ _ _ r25, s6_addi_reg _ _ _ _ _ r23, pairedReg _ r6]
  · exact nonce_compacted_mem pairedBytes (by rw [effect.2.2, s6_addi_mem, s6_addi_mem])

end CommitGolfCandidate
