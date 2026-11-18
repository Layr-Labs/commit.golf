import CommitGolfCandidate.CapMarkImage

/-! Straight-line runs of loads, stores and immediate operations, one branch,
and one permutation call, on an arbitrary image. Every fetch, access check and
cost is derived from the interpreter; nothing is assumed about oracle replies. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] readBuffer

/-- Loads, stores and immediate operations: one cycle each, falling through. -/
def s3Plain : Instr → Bool
  | .LD _ _ _ | .SD _ _ _ | .ADDI _ _ _ | .ANDI _ _ _ | .SLLI _ _ _ | .SRLI _ _ _ => true
  | _ => false

/-- The register a plain instruction writes. -/
def s3Target : Instr → Option Reg
  | .LD rd _ _ | .ADDI rd _ _ | .ANDI rd _ _ | .SLLI rd _ _ | .SRLI rd _ _ => some rd
  | _ => none

/-- Base register and offset of a plain memory access. -/
def s3Access : Instr → Option (Reg × BitVec 12)
  | .LD _ base offset | .SD base _ offset => some (base, offset)
  | _ => none

def s3Run (instructions : List Instr) (state : MachineState) : MachineState :=
  instructions.foldl execInstrBr state

/-- Static admission of a straight-line run: every access is absolute (base
x0, checked numerically) or one of the first `words` words at the window
register while that register is intact. -/
def s3Checked (window : Reg) (words : Nat) : Bool → List Instr → Bool
  | _, [] => true
  | intact, instruction :: rest =>
      s3Plain instruction &&
      (match s3Access instruction with
        | none => true
        | some (base, offset) =>
          (decide (base = .x0) && accessValid (signExtend12 offset) 8) ||
          (intact && decide (base = window) &&
            (List.range words).any fun word => offset == BitVec.ofNat 12 (8 * word))) &&
      s3Checked window words (intact && decide (s3Target instruction ≠ some window)) rest

private theorem store_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem s3_run_append (left right : List Instr) (state : MachineState) :
    s3Run (left ++ right) state = s3Run right (s3Run left state) := by
  simp only [s3Run, List.foldl_append]

theorem s3_plain_pc (state : MachineState) (instruction : Instr)
    (plain : s3Plain instruction = true) :
    (execInstrBr state instruction).pc = state.pc + 4 := by
  cases instruction <;>
    first
    | (simp only [s3Plain, Bool.false_eq_true] at plain; done)
    | rfl

theorem s3_plain_register (state : MachineState) (instruction : Instr) (reg : Reg)
    (plain : s3Plain instruction = true) (untouched : s3Target instruction ≠ some reg) :
    (execInstrBr state instruction).getReg reg = state.getReg reg := by
  cases instruction <;>
    first
    | (simp only [s3Plain, Bool.false_eq_true] at plain; done)
    | (simp only [execInstrBr, MachineState.getReg_setPC, store_register]; done)
    | (simp only [s3Target, ne_eq, Option.some.injEq] at untouched
       simp only [execInstrBr, MachineState.getReg_setPC,
         MachineState.getReg_setReg_ne _ _ _ _ untouched])

theorem s3_plain_step (state : MachineState) (instruction : Instr)
    (plain : s3Plain instruction = true)
    (valid : memoryArgumentsValid state instruction = true) :
    ordinaryStep state (.base instruction) = some (execInstrBr state instruction) := by
  cases instruction <;>
    first
    | (simp only [s3Plain, Bool.false_eq_true] at plain; done)
    | (simp only [ordinaryStep, valid, ↓reduceIte]; done)

theorem s3_plain_cycles (instruction : Instr) (plain : s3Plain instruction = true) :
    instructionCycles (.base instruction) = 1 := by
  cases instruction <;>
    first
    | (simp only [s3Plain, Bool.false_eq_true] at plain; done)
    | rfl

theorem s3_plain_valid (state : MachineState) (instruction : Instr)
    (plain : s3Plain instruction = true)
    (admitted : ∀ base offset, s3Access instruction = some (base, offset) →
      accessValid (state.getReg base + signExtend12 offset) 8 = true) :
    memoryArgumentsValid state instruction = true := by
  cases instruction <;>
    first
    | (simp only [s3Plain, Bool.false_eq_true] at plain; done)
    | rfl
    | (simp only [memoryArgumentsValid, memAccess]; exact admitted _ _ rfl)

theorem s3_value_offset (word : Nat) (small : word < 32) :
    signExtend12 (BitVec.ofNat 12 (8 * word)) = BitVec.ofNat 64 (8 * word) := by
  interval_cases word <;> rfl

theorem s3_run_register (instructions : List Instr) (window : Reg) (words : Nat)
    (intact : Bool) (state : MachineState)
    (reg : Reg) (checked : s3Checked window words intact instructions = true)
    (untouched : ∀ instruction ∈ instructions, s3Target instruction ≠ some reg) :
    (s3Run instructions state).getReg reg = state.getReg reg := by
  induction instructions generalizing intact state with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [s3Checked, Bool.and_eq_true] at checked
    change (s3Run rest (execInstrBr state instruction)).getReg reg = _
    rw [ih _ _ checked.2 (fun other inside => untouched other (List.mem_cons_of_mem _ inside)),
      s3_plain_register state instruction reg checked.1.1
        (untouched instruction List.mem_cons_self)]

theorem s3_run_pc (instructions : List Instr) (window : Reg) (words : Nat) (intact : Bool)
    (state : MachineState) (checked : s3Checked window words intact instructions = true) :
    (s3Run instructions state).pc = state.pc + BitVec.ofNat 64 (4 * instructions.length) := by
  induction instructions generalizing intact state with
  | nil => simp [s3Run]
  | cons instruction rest ih =>
    simp only [s3Checked, Bool.and_eq_true] at checked
    change (s3Run rest (execInstrBr state instruction)).pc = _
    rw [ih _ _ checked.2, s3_plain_pc state instruction checked.1.1, List.length_cons,
      Nat.mul_succ, Nat.add_comm (4 * rest.length) 4, BitVec.ofNat_add, BitVec.add_assoc]
    rfl

/-- A checked straight-line run: one cycle per instruction, no oracle call. -/
theorem s3_run_execute (image : Image) (instructions : List Instr) (window : Reg)
    (words : Nat) (fewWords : words ≤ 32) (intact : Bool)
    (index : Nat) (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (bounded : index + instructions.length ≤ 512)
    (decoded : ∀ i (inside : i < instructions.length),
      (image.code[index + i]?).bind decodeInstruction = some (.base instructions[i]))
    (checked : s3Checked window words intact instructions = true)
    (source : intact = true → ∀ word < words,
      accessValid (state.getReg window + BitVec.ofNat 64 (8 * word)) 8 = true) :
    execute image (instructions.length + fuel) state allowCoins =
      (do let result ← execute image fuel (s3Run instructions state) allowCoins
          return result.charge instructions.length 0) := by
  induction instructions generalizing intact index state with
  | nil => simp [s3Run, Execution.charge]
  | cons instruction rest ih =>
    simp only [s3Checked, Bool.and_eq_true] at checked
    obtain ⟨⟨plain, access⟩, restChecked⟩ := checked
    have inside : index < 512 := by
      simp only [List.length_cons] at bounded
      omega
    have fetched : fetch image state = some (.base instruction) := by
      apply cap_image_fetch image state index instruction inside pc
      have first := decoded 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at first
      exact first
    have valid : memoryArgumentsValid state instruction = true := by
      apply s3_plain_valid state instruction plain
      intro base offset equal
      simp only [equal, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.mem_range, beq_iff_eq] at access
      rcases access with ⟨rfl, absolute⟩ | ⟨⟨whole, rfl⟩, word, small, rfl⟩
      · change accessValid ((0#64) + signExtend12 offset) 8 = true
        rw [BitVec.zero_add]
        exact absolute
      · rw [s3_value_offset word (by omega)]
        exact source whole word small
    have next : (execInstrBr state instruction).pc =
        BitVec.ofNat 64 (4096 + 4 * (index + 1)) := by
      rw [s3_plain_pc state instruction plain, pc,
        show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have nextSource : (intact && decide (s3Target instruction ≠ some window)) = true →
        ∀ word < words, accessValid ((execInstrBr state instruction).getReg window +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      intro both
      simp only [Bool.and_eq_true, decide_eq_true_eq] at both
      rw [s3_plain_register state instruction window plain both.2]
      exact source both.1
    have tail := ih (intact && decide (s3Target instruction ≠ some window)) (index + 1)
      (execInstrBr state instruction) next
      (by simp only [List.length_cons] at bounded; omega)
      (fun i inside => by
        have shifted := decoded (i + 1) (by simpa using inside)
        simp only [List.getElem_cons_succ] at shifted
        rw [show index + 1 + i = index + (i + 1) by omega]
        exact shifted)
      restChecked nextSource
    rw [show (instruction :: rest).length + fuel = (rest.length + fuel) + 1 by
        simp only [List.length_cons]; omega,
      execute_ordinary_step image _ state _ _ allowCoins fetched
        (s3_plain_step state instruction plain valid),
      s3_plain_cycles instruction plain, tail]
    simp only [bind_assoc, pure_bind]
    simp [s3Run, Execution.charge, Nat.add_assoc, Nat.add_comm]

/-! ### One conditional branch -/

/-- A `BEQ`: one cycle, no memory access; the next PC is chosen by the interpreter. -/
theorem s3_branch_execute (image : Image) (state : MachineState) (index : Nat)
    (left right : Reg) (offset : BitVec 13) (fuel : Nat) (allowCoins : Bool)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index)) (inside : index < 512)
    (decoded : (image.code[index]?).bind decodeInstruction =
      some (.base (.BEQ left right offset))) :
    execute image (1 + fuel) state allowCoins =
      (do let result ← execute image fuel (execInstrBr state (.BEQ left right offset))
            allowCoins
          return result.charge 1 0) := by
  have fetched := cap_image_fetch image state index _ inside pc decoded
  have stepped : ordinaryStep state (.base (.BEQ left right offset)) =
      some (execInstrBr state (.BEQ left right offset)) := rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step image _ state _ _ allowCoins fetched stepped]
  rfl

theorem s3_branch_register (state : MachineState) (left right : Reg) (offset : BitVec 13)
    (reg : Reg) : (execInstrBr state (.BEQ left right offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> rfl

theorem s3_branch_mem (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BEQ left right offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem s3_branch_taken (state : MachineState) (left right : Reg) (offset : BitVec 13)
    (equal : state.getReg left = state.getReg right) :
    (execInstrBr state (.BEQ left right offset)).pc = state.pc + signExtend13 offset := by
  simp [execInstrBr, equal, MachineState.setPC]

theorem s3_branch_fall (state : MachineState) (left right : Reg) (offset : BitVec 13)
    (different : state.getReg left ≠ state.getReg right) :
    (execInstrBr state (.BEQ left right offset)).pc = state.pc + 4 := by
  simp [execInstrBr, different, MachineState.setPC]

/-! ### One permutation call -/

def s3PermutationQuery (input : BitVec 1600) : OracleComp World (BitVec 1600) :=
  World.query (.inr (.inr (.inl input)))

def s3PermutationAnswer (state : MachineState) (answer : BitVec 1600) : MachineState :=
  writeBits state (state.getReg .x12) answer

/-- One real ECALL with the forward-permutation selectors: eight cycles and
one public query; the 200-byte input is read before the reply is written. -/
theorem s3_permutation_execute (image : Image) (state : MachineState)
    (fetched : fetch image state = some (.base .ECALL))
    (selectors : state.getReg .x5 = 0 ∧ state.getReg .x11 = 200 ∧ state.getReg .x13 = 1)
    (sourceValid : rangeValid (state.getReg .x10) 200 = true)
    (destinationValid : rangeValid (state.getReg .x12) 200 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1 + fuel) state allowCoins =
      (do let answer ← s3PermutationQuery (readBuffer state (state.getReg .x10).toNat 200)
          let result ← execute image fuel (s3PermutationAnswer state answer) allowCoins
          return result.charge 8 1) := by
  have input : oracleInput state =
      some (.inr (.inl (readBuffer state (state.getReg .x10).toNat 200))) := by
    simp [oracleInput, selectors.2.2, selectors.2.1, COMPRESSION_INPUT_LENGTH,
      COMPRESSION_OUTPUT_LENGTH, PERMUTATION_WIDTH, sourceValid, destinationValid]
    refine ⟨⟨sourceAligned, destinationAligned⟩, ?_⟩
    rw [selectors.2.2]
    exact BitVec.setWidth_eq _
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos selectors.1, input]
  simp [s3PermutationQuery, s3PermutationAnswer, writeOracleAnswer, oracleCycles,
    PERMUTATION_CYCLES, Execution.charge]
  rfl

theorem s3_permutation_register (state : MachineState) (answer : BitVec 1600) (reg : Reg) :
    (s3PermutationAnswer state answer).getReg reg = state.getReg reg :=
  writeBits_register state _ answer reg

theorem s3_permutation_pc (state : MachineState) (answer : BitVec 1600) :
    (s3PermutationAnswer state answer).pc = state.pc + 4 := by
  simp [s3PermutationAnswer, writeBits, MachineState.setPC]

end CommitGolfCandidate
