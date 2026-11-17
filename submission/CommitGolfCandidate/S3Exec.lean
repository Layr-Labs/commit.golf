import CommitGolfCandidate.S3Image

/-! Interpreter bridges for the appended stage-3 code: straight-line runs of checked
loads, stores and additions, and the forward permutation syscall. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Fall-through, unit-cost instructions whose only fault is a checked memory access. -/
def s3Straight : Instr → Bool
  | .LD _ _ _ => true
  | .SD _ _ _ => true
  | .ADDI _ _ _ => true
  | .ADD _ _ _ => true
  | _ => false

theorem s3_straight_step (state : MachineState) (instruction : Instr)
    (straight : s3Straight instruction = true)
    (valid : memoryArgumentsValid state instruction = true) :
    ordinaryStep state (.base instruction) = some (execInstrBr state instruction) ∧
    instructionCycles (.base instruction) = 1 ∧
    (execInstrBr state instruction).pc = state.pc + 4 := by
  cases instruction <;> simp only [s3Straight, Bool.false_eq_true] at straight
  all_goals
    refine ⟨?_, rfl, rfl⟩
    simp only [ordinaryStep, valid, ↓reduceIte]

/-- A straight-line block: every fetch is tied to the image, every access is checked. -/
theorem s3_straight_execute (image : Image) (instructions : List Instr) (count start : Nat)
    (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (length : instructions.length = count)
    (pc : state.pc = BitVec.ofNat 64 start)
    (straight : ∀ instruction ∈ instructions, s3Straight instruction = true)
    (fetched : ∀ k, k < count → ∀ current : MachineState,
      current.pc = BitVec.ofNat 64 (start + 4 * k) →
      fetch image current = some (.base ((instructions[k]?).getD .EBREAK)))
    (valid : ∀ k, k < count →
      memoryArgumentsValid ((instructions.take k).foldl execInstrBr state)
        ((instructions[k]?).getD .EBREAK) = true) :
    execute image (count + fuel) state allowCoins =
      (do let result ← execute image fuel (instructions.foldl execInstrBr state) allowCoins
          return result.charge count 0) ∧
    (instructions.foldl execInstrBr state).pc = BitVec.ofNat 64 (start + 4 * count) := by
  induction instructions generalizing count start state with
  | nil =>
    subst length
    refine ⟨?_, by simpa using pc⟩
    simp [Execution.charge]
  | cons head tail ih =>
    subst length
    have step := s3_straight_step state head (straight head (by simp))
      (by simpa using valid 0 (by simp))
    have fetchedHead : fetch image state = some (.base head) := by
      simpa using fetched 0 (by simp) state (by simpa using pc)
    have nextPC : (execInstrBr state head).pc = BitVec.ofNat 64 (start + 4) := by
      rw [step.2.2, pc, BitVec.ofNat_add]
      rfl
    have rest := ih tail.length (start + 4) (execInstrBr state head) rfl nextPC
      (fun instruction member => straight instruction (by simp [member]))
      (fun k bound current currentPC => by
        have := fetched (k + 1) (by simp; omega) current
          (by rw [currentPC]; congr 1; omega)
        simpa using this)
      (fun k bound => by
        have := valid (k + 1) (by simp; omega)
        simpa using this)
    refine ⟨?_, by rw [List.foldl_cons, rest.2]; congr 1; simp; omega⟩
    rw [List.length_cons, show tail.length + 1 + fuel = (tail.length + fuel) + 1 by omega,
      execute_ordinary_step image (.base head) state _ _ _ fetchedHead step.1, step.2.1, rest.1]
    simp only [bind_assoc, pure_bind, List.foldl_cons]
    simp [Execution.charge, Nat.add_comm, Nat.add_assoc]

/-- Selector, width and primitive of the forward permutation call. -/
def S3PermReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x11 = 200 ∧ state.getReg .x13 = 1

/-- The permutation width simplifies without expanding the byte reader. -/
theorem s3_read_width (state : MachineState) (address kind : Nat) (one : kind = 1) :
    BitVec.setWidth 1600 (readBuffer state address
      (((if kind = 0 then 512 else 1600) + 7) / 8)) =
      readBuffer state address 200 := by
  subst one
  exact BitVec.setWidth_eq _

/-- The real `oracleInput` accepts an aligned 200-byte window and an aligned 200-byte reply. -/
theorem s3_oracle_input (state : MachineState) (ready : S3PermReady state)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceBound : (state.getReg .x10).toNat + 200 ≤ MEMORY_BYTES)
    (destinationBound : (state.getReg .x12).toNat + 200 ≤ MEMORY_BYTES) :
    oracleInput state = some (.inr (.inl (s3PermInput state))) := by
  rcases ready with ⟨_, width, kind⟩
  have kindNat : (state.getReg .x13).toNat = 1 := by rw [kind]; rfl
  have widthNat : (state.getReg .x11).toNat = 200 := by rw [width]; rfl
  simp [oracleInput, kindNat, widthNat, rangeValid, sourceAligned, destinationAligned,
    sourceBound, destinationBound, PERMUTATION_WIDTH, COMPRESSION_INPUT_LENGTH, s3PermInput]
  exact s3_read_width state _ _ kindNat

/-- One forward permutation syscall: eight cycles, one query, any 1600-bit reply. -/
theorem s3_perm_call (image : Image) (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (fetched : fetch image state = some (.base .ECALL))
    (ready : S3PermReady state)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (sourceBound : (state.getReg .x10).toNat + 200 ≤ MEMORY_BYTES)
    (destinationBound : (state.getReg .x12).toNat + 200 ≤ MEMORY_BYTES) :
    execute image (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inr (.inl (s3PermInput state))))
          let result ← execute image fuel (s3PermReply state answer) allowCoins
          return result.charge 8 1) := by
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos ready.1,
    s3_oracle_input state ready sourceAligned destinationAligned sourceBound destinationBound]
  rfl

/-- A checked doubleword access at a register plus a small immediate. -/
theorem s3_access_valid (register immediate : Word) (base offset : Nat)
    (value : register = BitVec.ofNat 64 base) (extended : immediate = BitVec.ofNat 64 offset)
    (aligned : base % 8 = 0) (offsetAligned : offset % 8 = 0)
    (bounded : base + offset + 8 ≤ MEMORY_BYTES) :
    accessValid (register + immediate) 8 = true := by
  subst value extended
  have total : base + offset < 2 ^ 64 := by dsimp [MEMORY_BYTES] at bounded; omega
  rw [← BitVec.ofNat_add]
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt total,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

end CommitGolfCandidate
