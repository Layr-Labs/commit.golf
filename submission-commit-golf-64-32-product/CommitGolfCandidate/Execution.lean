import CommitGolfCandidate.Programs

/-! Execution composition for the actual challenge interpreter. Splitting a run at
an instruction boundary preserves its output, randomness, oracle calls, and cycles.
This is the basis for proving loop bodies separately without changing the machine. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Continue only a fuel-exhausted run, retaining its accumulated costs. -/
def resume (image : Image) (steps : Nat) (allowCoins : Bool) (result : Execution) :
    OracleComp World Execution := do
  if result.exit = .unfinished then
    let next ← execute image steps result.state allowCoins
    return next.charge result.cycles result.oracleCalls
  else pure result

private theorem resume_charge (image : Image) (steps : Nat) (allowCoins : Bool)
    (result : Execution) (cycles calls : Nat) :
    resume image steps allowCoins (result.charge cycles calls) =
      (do let next ← resume image steps allowCoins result
          return next.charge cycles calls) := by
  unfold resume
  by_cases h : result.exit = .unfinished
  · simp [Execution.charge, h, Nat.add_left_comm, Nat.add_comm]
  · simp [Execution.charge, h]

/-- Fuel can be split into consecutive runs without altering the computation. -/
theorem execute_add (image : Image) (steps extra : Nat) (state : MachineState)
    (allowCoins : Bool) :
    execute image (steps + extra) state allowCoins =
      (do let result ← execute image steps state allowCoins
          resume image extra allowCoins result) := by
  induction steps generalizing state with
  | zero =>
    simp [execute, resume, Execution.charge]
  | succ steps ih =>
    rw [Nat.succ_add]
    simp only [execute]
    split
    · simp [resume]
    · split
      · split
        · simp [resume]
        · simp only [ih, bind_assoc, pure_bind, resume_charge]
      · split
        · simp only [pure_bind, resume]
          split <;> simp
        · split
          · simp only [ih, bind_assoc, pure_bind, resume_charge]
          · simp [resume]
    · split
      · simp [resume]
      · simp only [ih, bind_assoc, pure_bind, resume_charge]

/-- Once every execution has halted, extra fuel changes neither results nor costs.
A loop proof can therefore use its exact instruction count and then extend it to
one of the larger instruction allowances declared by the submitted image. -/
theorem execute_extra_fuel (image : Image) (steps extra : Nat) (state : MachineState)
    (allowCoins : Bool)
    (finished : ∀ result ∈ support (execute image steps state allowCoins),
      result.exit ≠ .unfinished) :
    execute image (steps + extra) state allowCoins = execute image steps state allowCoins := by
  rw [execute_add]
  calc
    _ = (execute image steps state allowCoins >>= pure) :=
      bind_congr_of_forall_mem_support _ fun result h => by
        simp [resume, finished result h]
    _ = _ := bind_pure _

/-- Every possible execution makes at most one public query per instruction.
This holds for arbitrary oracle replies and private coins, not just their averages. -/
theorem execute_calls_le_steps (image : Image) (steps : Nat) (state : MachineState)
    (allowCoins : Bool) (result : Execution)
    (h : result ∈ support (execute image steps state allowCoins)) :
    result.oracleCalls ≤ steps := by
  induction steps generalizing state result with
  | zero =>
    simp only [execute, support_pure, Set.mem_singleton_iff] at h
    subst result
    exact Nat.zero_le _
  | succ steps ih =>
    simp only [execute] at h
    split at h
    · simp only [support_pure, Set.mem_singleton_iff] at h
      subst result
      simp
    · split at h
      · split at h
        · simp only [support_pure, Set.mem_singleton_iff] at h
          subst result
          simp
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
          obtain ⟨answer, _, next, hnext, rfl⟩ := h
          have := ih _ _ hnext
          simp only [Execution.charge]
          omega
      · split at h
        · simp only [support_pure, Set.mem_singleton_iff] at h
          subst result
          simp
        · split at h
          · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
            obtain ⟨answer, _, next, hnext, rfl⟩ := h
            have := ih _ _ hnext
            simp only [Execution.charge]
            omega
          · simp only [support_pure, Set.mem_singleton_iff] at h
            subst result
            simp
    · split at h
      · simp only [support_pure, Set.mem_singleton_iff] at h
        subst result
        simp
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
        obtain ⟨next, hnext, rfl⟩ := h
        have := ih _ _ hnext
        simp only [Execution.charge]
        omega

private theorem instructionCycles_le_four (instruction : Instruction) :
    instructionCycles instruction ≤ 4 := by
  cases instruction with
  | base instruction => cases instruction <;> simp [instructionCycles]
  | word op rd rs1 rs2 => cases op <;> simp [instructionCycles]
  | sraiw rd rs shift => simp [instructionCycles]

private theorem oracleCycles_le_thirty (input : PublicSpec.Domain) : oracleCycles input ≤ 30 := by
  cases input <;> simp [oracleCycles, COMPRESSION_CYCLES, PERMUTATION_CYCLES]

/-- Without private randomness, each step costs at most thirty abstract cycles.
This applies to the checker, including malformed inputs and early failure paths. -/
theorem execute_cycles_le_steps (image : Image) (steps : Nat) (state : MachineState)
    (result : Execution) (h : result ∈ support (execute image steps state false)) :
    result.cycles ≤ 30 * steps := by
  induction steps generalizing state result with
  | zero =>
    simp only [execute, support_pure, Set.mem_singleton_iff] at h
    subst result
    exact Nat.zero_le _
  | succ steps ih =>
    simp only [execute, Bool.false_and, Bool.false_eq_true, ite_false] at h
    split at h
    · simp only [support_pure, Set.mem_singleton_iff] at h
      subst result
      simp
    · split at h
      · split at h
        · simp only [support_pure, Set.mem_singleton_iff] at h
          subst result
          change 1 ≤ 30 * (steps + 1)
          omega
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
          obtain ⟨answer, _, next, hnext, rfl⟩ := h
          rename_i input hInput hmem
          have := ih _ _ hnext
          have price := oracleCycles_le_thirty input
          simp only [Execution.charge]
          omega
      · split at h
        · simp only [support_pure, Set.mem_singleton_iff] at h
          subst result
          change 1 ≤ 30 * (steps + 1)
          omega
        · simp only [support_pure, Set.mem_singleton_iff] at h
          subst result
          change 1 ≤ 30 * (steps + 1)
          omega
    · split at h
      · simp only [support_pure, Set.mem_singleton_iff] at h
        subst result
        change 1 ≤ 30 * (steps + 1)
        omega
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
        obtain ⟨next, hnext, rfl⟩ := h
        have := ih _ _ hnext
        have := instructionCycles_le_four (by assumption)
        simp only [Execution.charge]
        omega

/-- The query bound also covers the ABI's oversized-proof rejection path. -/
theorem run_calls_le_steps (s : Submission) (program : Program)
    (input : Input s.sizes program) (result : Execution)
    (h : result ∈ support (s.run program input)) : result.oracleCalls ≤ s.steps program := by
  cases program with
  | commit => exact execute_calls_le_steps _ _ _ _ _ (by simpa [Submission.run] using h)
  | opening => exact execute_calls_le_steps _ _ _ _ _ (by simpa [Submission.run] using h)
  | check =>
    simp only [Submission.run] at h
    split at h
    · exact execute_calls_le_steps _ _ _ _ _ h
    · simp only [support_pure, Set.mem_singleton_iff] at h
      subst result
      exact Nat.zero_le _

/-- A universal checker bound for the real ABI, regardless of proof validity.
It bounds charged cycles; termination still needs a separate proof. -/
theorem run_check_cycles_le_steps (s : Submission) (input : Input s.sizes .check)
    (result : Execution) (h : result ∈ support (s.run .check input)) :
    result.cycles ≤ 30 * s.steps .check := by
  simp only [Submission.run] at h
  split at h
  · exact execute_cycles_le_steps _ _ _ _ h
  · simp only [support_pure, Set.mem_singleton_iff] at h
    subst result
    exact Nat.zero_le _

/-- One checked ordinary instruction, with its exact interpreter cost. -/
theorem execute_ordinary_step (image : Image) (instruction : Instruction)
    (state next : MachineState) (fuel : Nat) (allowCoins : Bool)
    (fetched : fetch image state = some instruction)
    (stepped : ordinaryStep state instruction = some next) :
    execute image (fuel + 1) state allowCoins =
      (do let result ← execute image fuel next allowCoins
          return result.charge (instructionCycles instruction) 0) := by
  cases instruction with
  | base instruction =>
    cases instruction <;> simp_all [execute, ordinaryStep]
  | word op rd rs1 rs2 => simp only [execute, fetched, stepped]
  | sraiw rd rs shift => simp only [execute, fetched, stepped]

/-- Compose a concrete trace of one-cycle ordinary instructions. The premise checks
both fetching and stepping at every state, so the trace is tied to the image bytes. -/
theorem execute_unit_steps (image : Image) (count fuel : Nat)
    (states : Nat → MachineState) (allowCoins : Bool)
    (trace : ∀ i < count, ∃ instruction,
      fetch image (states i) = some instruction ∧
      ordinaryStep (states i) instruction = some (states (i + 1)) ∧
      instructionCycles instruction = 1) :
    execute image (count + fuel) (states 0) allowCoins =
      (do let result ← execute image fuel (states count) allowCoins
          return result.charge count 0) := by
  induction count generalizing states with
  | zero => simp [Execution.charge]
  | succ count ih =>
    obtain ⟨instruction, fetched, stepped, cost⟩ := trace 0 (by omega)
    rw [Nat.succ_add, execute_ordinary_step image instruction _ _ _ _ fetched stepped, cost]
    have tail := ih (fun i => states (i + 1)) (by
      intro i hi
      exact trace (i + 1) (by omega))
    simp only [tail, bind_assoc, pure_bind]
    simp [Execution.charge, ← Nat.add_assoc, Nat.add_comm 1 count]

/-- Writing an oracle reply changes memory and the PC, never a register. -/
theorem writeBits_register {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (reg : Reg) :
    (writeBits state address answer).getReg reg = state.getReg reg := by
  unfold writeBits
  rw [MachineState.getReg_setPC]
  have preserved (indices : List Nat) (state : MachineState) :
      (indices.foldl (fun current i => current.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) state).getReg reg = state.getReg reg := by
    induction indices generalizing state with
    | nil => rfl
    | cons index indices ih =>
      rw [List.foldl_cons, ih]
      cases reg <;> rfl
  exact preserved _ state

/-- Byte-wise reply writes preserve every word outside their destination words. -/
theorem writeBits_memory_outside {bits : Nat} (state : MachineState) (address query : Word)
    (answer : BitVec bits)
    (outside : ∀ i < (bits + 7) / 8, query ≠ alignToDword (address + BitVec.ofNat 64 i)) :
    (writeBits state address answer).getMem query = state.getMem query := by
  unfold writeBits
  change ((List.range ((bits + 7) / 8)).foldl _ state).getMem query = _
  have preserved (indices : List Nat) (state : MachineState)
      (separate : ∀ i ∈ indices, query ≠ alignToDword (address + BitVec.ofNat 64 i)) :
      (indices.foldl (fun current i => current.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) state).getMem query = state.getMem query := by
    induction indices generalizing state with
    | nil => rfl
    | cons index indices ih =>
      rw [List.foldl_cons, ih _ (fun i hi => separate i (by simp [hi]))]
      simp [MachineState.setByte, MachineState.setMem, MachineState.getMem,
        separate index (by simp)]
  exact preserved _ state (fun i hi => outside i (List.mem_range.mp hi))

end CommitGolfCandidate
