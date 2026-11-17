import CommitGolfCandidate.T1Image
import CommitGolfCandidate.HoistHelpers

/-! Relocation of one leaf body. Leaf `u` of the unrolled group is the original
31-instruction body with the nonce offset `24u` and the heap offset `32u` folded
into four immediates. Run on a state whose nonce and heap registers lag by exactly
those amounts, it performs the same loads, stores and queries as the original body,
for every reply and on every fault path. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Leaf `u` sees nonce and heap registers lagging by `24u` and `32u`. -/
def unrolledShift (u : Nat) (state : MachineState) (pc : Word) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18 - BitVec.ofNat 64 (24 * u))).setReg .x23
    (state.getReg .x23 - BitVec.ofNat 64 (32 * u))).setPC pc

/-- The lagging state at a displaced program counter. -/
def unrolledMove (u : Nat) (delta : Word) (state : MachineState) : MachineState :=
  unrolledShift u state (state.pc + delta)

/-- Displacement from the original body (PC 4456) to leaf `u` of the group. -/
def unrolledDelta (u : Nat) : Word := BitVec.ofNat 64 (1006948 + 124 * u)

def unrolledLift (move : MachineState → MachineState) (result : Execution) : Execution :=
  { result with state := move result.state }

theorem unrolled_pc_comm (pc delta : Word) : pc + delta + 4 = pc + 4 + delta := by
  rw [BitVec.add_assoc, BitVec.add_comm delta 4, ← BitVec.add_assoc]

theorem unrolled_state_congr (base : MachineState) (regs regs' : Reg → Word)
    (mem mem' : Word → Word) (pc pc' : Word)
    (sameRegs : regs = regs') (sameMem : mem = mem') (samePC : pc = pc') :
    ({ base with regs := regs, mem := mem, pc := pc } : MachineState) =
      { base with regs := regs', mem := mem', pc := pc' } := by
  subst sameRegs sameMem samePC
  rfl

theorem unrolled_sub_add (x a b : Word) : x - a + (a + b) = x + b := by
  rw [← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem unrolled_nonce_address (u k : Nat) (hu : u < 64) (hk : k = 0 ∨ k = 8 ∨ k = 16)
    (x : Word) :
    x - BitVec.ofNat 64 (24 * u) + signExtend12 (BitVec.ofNat 12 (24 * u + k)) =
      x + signExtend12 (BitVec.ofNat 12 k) := by
  have extended : signExtend12 (BitVec.ofNat 12 (24 * u + k)) =
      BitVec.ofNat 64 (24 * u) + signExtend12 (BitVec.ofNat 12 k) := by
    rcases hk with rfl | rfl | rfl <;> interval_cases u <;> rfl
  rw [extended, unrolled_sub_add]

theorem unrolled_heap_address (u : Nat) (hu : u < 64) (x : Word) :
    x - BitVec.ofNat 64 (32 * u) + signExtend12 (BitVec.ofNat 12 (32 * u)) =
      x + signExtend12 (BitVec.ofNat 12 0) := by
  have extended : signExtend12 (BitVec.ofNat 12 (32 * u)) =
      BitVec.ofNat 64 (32 * u) + signExtend12 (BitVec.ofNat 12 0) := by
    interval_cases u <;> rfl
  rw [extended, unrolled_sub_add]

/-- A register write outside the two lagging registers commutes with the lag. -/
theorem unrolled_move_set (u : Nat) (delta : Word) (state : MachineState) (reg : Reg)
    (value : Word) (h18 : reg ≠ .x18) (h23 : reg ≠ .x23) :
    ((unrolledMove u delta state).setReg reg value).setPC ((unrolledMove u delta state).pc + 4) =
      unrolledMove u delta ((state.setReg reg value).setPC (state.pc + 4)) := by
  cases reg <;> first
    | exact absurd rfl h18
    | exact absurd rfl h23
    | exact unrolled_state_congr state _ _ _ _ _ _ (by funext r; cases r <;> rfl) rfl
        (unrolled_pc_comm _ _)

/-- A memory write commutes with the lag. -/
theorem unrolled_move_store (u : Nat) (delta : Word) (state : MachineState)
    (address value : Word) :
    ((unrolledMove u delta state).setMem address value).setPC
        ((unrolledMove u delta state).pc + 4) =
      unrolledMove u delta ((state.setMem address value).setPC (state.pc + 4)) :=
  unrolled_state_congr state _ _ _ _ _ _ rfl rfl (unrolled_pc_comm _ _)

theorem unrolled_shift_fold (u : Nat) (step : MachineState → Nat → MachineState)
    (commute : ∀ (current : MachineState) (pc : Word) (i : Nat),
      step (unrolledShift u current pc) i = unrolledShift u (step current i) pc)
    (indices : List Nat) (current : MachineState) (pc : Word) :
    indices.foldl step (unrolledShift u current pc) =
      unrolledShift u (indices.foldl step current) pc := by
  induction indices generalizing current with
  | nil => rfl
  | cons i rest ih => rw [List.foldl_cons, List.foldl_cons, commute, ih]

/-- Reply bytes are written to the same addresses with the same values. -/
theorem unrolled_move_write_bits {bits : Nat} (u : Nat) (delta : Word) (state : MachineState)
    (address : Word) (answer : BitVec bits) :
    writeBits (unrolledMove u delta state) address answer =
      unrolledMove u delta (writeBits state address answer) := by
  unfold writeBits
  rw [show unrolledMove u delta state = unrolledShift u state (state.pc + delta) from rfl,
    unrolled_shift_fold u _ (fun _ _ _ => rfl)]
  exact congrArg (unrolledShift u _) (unrolled_pc_comm state.pc delta)

theorem unrolled_move_oracle_answer (u : Nat) (delta : Word) (state : MachineState)
    (address : Word) (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    writeOracleAnswer (unrolledMove u delta state) address query answer =
      unrolledMove u delta (writeOracleAnswer state address query answer) := by
  rcases query with input | input | input <;>
    exact unrolled_move_write_bits u delta state address answer

theorem unrolled_oracle_answer_pc (state : MachineState) (address : Word)
    (query : PublicSpec.Domain) (answer : PublicSpec.Range query) :
    (writeOracleAnswer state address query answer).pc = state.pc + 4 := by
  rcases query with input | input | input <;> rfl

/-! ### Single instructions -/

theorem unrolled_step_of (move : MachineState → MachineState) (state : MachineState)
    (old new : Instr)
    (oldStep : ordinaryStep state (.base old) =
      if memoryArgumentsValid state old = true then some (execInstrBr state old) else none)
    (newStep : ordinaryStep (move state) (.base new) =
      if memoryArgumentsValid (move state) new = true then
        some (execInstrBr (move state) new) else none)
    (valid : memoryArgumentsValid (move state) new = memoryArgumentsValid state old)
    (stepped : execInstrBr (move state) new = move (execInstrBr state old)) :
    ordinaryStep (move state) (.base new) = (ordinaryStep state (.base old)).map move := by
  rw [oldStep, newStep, valid, stepped]
  cases memoryArgumentsValid state old <;> rfl

theorem unrolled_step_load (u : Nat) (delta : Word) (state : MachineState)
    (offset offset' : BitVec 12)
    (address : ∀ x : Word, x - BitVec.ofNat 64 (24 * u) + signExtend12 offset' =
      x + signExtend12 offset) :
    ordinaryStep (unrolledMove u delta state) (.base (.LD .x6 .x18 offset')) =
      (ordinaryStep state (.base (.LD .x6 .x18 offset))).map (unrolledMove u delta) := by
  have located : (unrolledMove u delta state).getReg .x18 + signExtend12 offset' =
      state.getReg .x18 + signExtend12 offset := address (state.getReg .x18)
  apply unrolled_step_of (unrolledMove u delta) state _ _ rfl rfl
  · exact congrArg (fun a => accessValid a 8) located
  · show ((unrolledMove u delta state).setReg .x6 ((unrolledMove u delta state).getMem
        ((unrolledMove u delta state).getReg .x18 + signExtend12 offset'))).setPC
          ((unrolledMove u delta state).pc + 4) =
      unrolledMove u delta ((state.setReg .x6 (state.getMem
        (state.getReg .x18 + signExtend12 offset))).setPC (state.pc + 4))
    rw [located]
    exact unrolled_move_set u delta state .x6 _ (by decide) (by decide)

theorem unrolled_step_store (u : Nat) (delta : Word) (state : MachineState) (source : Reg)
    (offset : BitVec 12) (h18 : source ≠ .x18) (h23 : source ≠ .x23) :
    ordinaryStep (unrolledMove u delta state) (.base (.SD .x10 source offset)) =
      (ordinaryStep state (.base (.SD .x10 source offset))).map (unrolledMove u delta) := by
  apply unrolled_step_of (unrolledMove u delta) state _ _ rfl rfl rfl
  cases source <;> first
    | exact absurd rfl h18
    | exact absurd rfl h23
    | exact unrolled_move_store u delta state _ _

theorem unrolled_step_add (u : Nat) (delta : Word) (state : MachineState) (target : Reg)
    (value : BitVec 12) (h18 : target ≠ .x18) (h23 : target ≠ .x23) :
    ordinaryStep (unrolledMove u delta state) (.base (.ADDI target .x10 value)) =
      (ordinaryStep state (.base (.ADDI target .x10 value))).map (unrolledMove u delta) := by
  apply unrolled_step_of (unrolledMove u delta) state _ _ rfl rfl rfl
  exact unrolled_move_set u delta state target _ h18 h23

theorem unrolled_step_heap (u : Nat) (delta : Word) (state : MachineState)
    (value value' : BitVec 12)
    (address : ∀ x : Word, x - BitVec.ofNat 64 (32 * u) + signExtend12 value' =
      x + signExtend12 value) :
    ordinaryStep (unrolledMove u delta state) (.base (.ADDI .x12 .x23 value')) =
      (ordinaryStep state (.base (.ADDI .x12 .x23 value))).map (unrolledMove u delta) := by
  have located : (unrolledMove u delta state).getReg .x23 + signExtend12 value' =
      state.getReg .x23 + signExtend12 value := address (state.getReg .x23)
  apply unrolled_step_of (unrolledMove u delta) state _ _ rfl rfl rfl
  show ((unrolledMove u delta state).setReg .x12
      ((unrolledMove u delta state).getReg .x23 + signExtend12 value')).setPC
        ((unrolledMove u delta state).pc + 4) =
    unrolledMove u delta ((state.setReg .x12
      (state.getReg .x23 + signExtend12 value)).setPC (state.pc + 4))
  rw [located]
  exact unrolled_move_set u delta state .x12 _ (by decide) (by decide)

/-! ### Execution -/

theorem unrolled_execute_fault (image : Image) (instruction : Instr) (state : MachineState)
    (fuel : Nat) (allowCoins : Bool) (ordinary : instruction ≠ .ECALL)
    (fetched : fetch image state = some (.base instruction))
    (stepped : ordinaryStep state (.base instruction) = none) :
    execute image (fuel + 1) state allowCoins =
      pure { exit := .failure, state := state, cycles := 1, oracleCalls := 0 } := by
  cases instruction <;> first
    | exact absurd rfl ordinary
    | simp only [execute, fetched, stepped]

theorem unrolled_execute_ordinary (image : Image) (move : MachineState → MachineState)
    (old new : Instr) (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (oldOrdinary : old ≠ .ECALL) (newOrdinary : new ≠ .ECALL)
    (oldFetched : fetch image state = some (.base old))
    (newFetched : fetch image (move state) = some (.base new))
    (step : ordinaryStep (move state) (.base new) = (ordinaryStep state (.base old)).map move)
    (cycles : instructionCycles (.base new) = instructionCycles (.base old))
    (rest : ∀ next, ordinaryStep state (.base old) = some next →
      execute image fuel (move next) allowCoins =
        unrolledLift move <$> execute image fuel next allowCoins) :
    execute image (fuel + 1) (move state) allowCoins =
      unrolledLift move <$> execute image (fuel + 1) state allowCoins := by
  cases stepped : ordinaryStep state (.base old) with
  | none =>
    rw [stepped] at step
    rw [unrolled_execute_fault image new (move state) fuel allowCoins newOrdinary newFetched step,
      unrolled_execute_fault image old state fuel allowCoins oldOrdinary oldFetched stepped,
      map_pure]
    rfl
  | some next =>
    rw [stepped] at step
    rw [execute_ordinary_step image (.base new) (move state) (move next) fuel allowCoins
        newFetched step,
      execute_ordinary_step image (.base old) state next fuel allowCoins oldFetched stepped,
      rest next stepped, cycles]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    rfl

theorem unrolled_ordinary_pc (state next : MachineState) (instruction : Instr)
    (advances : (execInstrBr state instruction).pc = state.pc + 4)
    (stepForm : ordinaryStep state (.base instruction) =
      if memoryArgumentsValid state instruction = true then
        some (execInstrBr state instruction) else none)
    (stepped : ordinaryStep state (.base instruction) = some next) :
    next.pc = state.pc + 4 := by
  rw [stepForm] at stepped
  split at stepped
  · cases stepped
    exact advances
  · cases stepped

/-- The oracle, halt and randomness arms read only registers and memory outside the lag. -/
theorem unrolled_execute_call (image : Image) (u : Nat) (delta : Word) (state : MachineState)
    (fuel : Nat) (allowCoins : Bool)
    (oldFetched : fetch image state = some (.base .ECALL))
    (newFetched : fetch image (unrolledMove u delta state) = some (.base .ECALL))
    (rest : ∀ next : MachineState, next.pc = state.pc + 4 →
      execute image fuel (unrolledMove u delta next) allowCoins =
        unrolledLift (unrolledMove u delta) <$> execute image fuel next allowCoins) :
    execute image (fuel + 1) (unrolledMove u delta state) allowCoins =
      unrolledLift (unrolledMove u delta) <$> execute image (fuel + 1) state allowCoins := by
  have r5 : (unrolledMove u delta state).getReg .x5 = state.getReg .x5 := rfl
  have r10 : (unrolledMove u delta state).getReg .x10 = state.getReg .x10 := rfl
  have r11 : (unrolledMove u delta state).getReg .x11 = state.getReg .x11 := rfl
  have r12 : (unrolledMove u delta state).getReg .x12 = state.getReg .x12 := rfl
  have input : oracleInput (unrolledMove u delta state) = oracleInput state := rfl
  have random : randomArgumentsValid (unrolledMove u delta state) =
      randomArgumentsValid state := rfl
  simp only [execute, oldFetched, newFetched]
  rw [r5, input, random]
  by_cases oracle : state.getReg .x5 = 0
  · rw [if_pos oracle, if_pos oracle]
    cases query : oracleInput state with
    | none =>
      simp only [map_pure]
      rfl
    | some question =>
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, r12]
      refine bind_congr (fun answer => ?_)
      rw [unrolled_move_oracle_answer,
        rest _ (unrolled_oracle_answer_pc state _ question answer)]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
      rfl
  · rw [if_neg oracle, if_neg oracle]
    by_cases halt : state.getReg .x5 = 1
    · rw [if_pos halt, if_pos halt, map_pure, r10]
      rfl
    · rw [if_neg halt, if_neg halt]
      split
      · simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp, r10, r11]
        refine bind_congr (fun answer => ?_)
        rw [unrolled_move_write_bits, rest _ rfl]
        simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
        rfl
      · rw [map_pure]
        rfl

/-! ### The 31-instruction body -/

theorem unrolled_run_load (image : Image) (u : Nat) (delta : Word) (offset offset' : BitVec 12)
    (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (address : ∀ x : Word, x - BitVec.ofNat 64 (24 * u) + signExtend12 offset' =
      x + signExtend12 offset)
    (oldFetched : fetch image state = some (.base (.LD .x6 .x18 offset)))
    (newFetched : fetch image (unrolledMove u delta state) = some (.base (.LD .x6 .x18 offset')))
    (rest : ∀ next : MachineState, next.pc = state.pc + 4 →
      execute image fuel (unrolledMove u delta next) allowCoins =
        unrolledLift (unrolledMove u delta) <$> execute image fuel next allowCoins) :
    execute image (fuel + 1) (unrolledMove u delta state) allowCoins =
      unrolledLift (unrolledMove u delta) <$> execute image (fuel + 1) state allowCoins :=
  unrolled_execute_ordinary image _ _ _ state fuel allowCoins (by intro h; cases h)
    (by intro h; cases h) oldFetched newFetched
    (unrolled_step_load u delta state offset offset' address) rfl
    (fun next stepped => rest next (unrolled_ordinary_pc state next _ rfl rfl stepped))

theorem unrolled_run_store (image : Image) (u : Nat) (delta : Word) (source : Reg)
    (offset : BitVec 12) (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (h18 : source ≠ .x18) (h23 : source ≠ .x23)
    (oldFetched : fetch image state = some (.base (.SD .x10 source offset)))
    (newFetched : fetch image (unrolledMove u delta state) =
      some (.base (.SD .x10 source offset)))
    (rest : ∀ next : MachineState, next.pc = state.pc + 4 →
      execute image fuel (unrolledMove u delta next) allowCoins =
        unrolledLift (unrolledMove u delta) <$> execute image fuel next allowCoins) :
    execute image (fuel + 1) (unrolledMove u delta state) allowCoins =
      unrolledLift (unrolledMove u delta) <$> execute image (fuel + 1) state allowCoins :=
  unrolled_execute_ordinary image _ _ _ state fuel allowCoins (by intro h; cases h)
    (by intro h; cases h) oldFetched newFetched
    (unrolled_step_store u delta state source offset h18 h23) rfl
    (fun next stepped => rest next (unrolled_ordinary_pc state next _ rfl rfl stepped))

theorem unrolled_run_add (image : Image) (u : Nat) (delta : Word) (target : Reg)
    (value : BitVec 12) (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (h18 : target ≠ .x18) (h23 : target ≠ .x23)
    (oldFetched : fetch image state = some (.base (.ADDI target .x10 value)))
    (newFetched : fetch image (unrolledMove u delta state) =
      some (.base (.ADDI target .x10 value)))
    (rest : ∀ next : MachineState, next.pc = state.pc + 4 →
      execute image fuel (unrolledMove u delta next) allowCoins =
        unrolledLift (unrolledMove u delta) <$> execute image fuel next allowCoins) :
    execute image (fuel + 1) (unrolledMove u delta state) allowCoins =
      unrolledLift (unrolledMove u delta) <$> execute image (fuel + 1) state allowCoins :=
  unrolled_execute_ordinary image _ _ _ state fuel allowCoins (by intro h; cases h)
    (by intro h; cases h) oldFetched newFetched
    (unrolled_step_add u delta state target value h18 h23) rfl
    (fun next stepped => rest next (unrolled_ordinary_pc state next _ rfl rfl stepped))

theorem unrolled_run_heap (image : Image) (u : Nat) (delta : Word) (value value' : BitVec 12)
    (state : MachineState) (fuel : Nat) (allowCoins : Bool)
    (address : ∀ x : Word, x - BitVec.ofNat 64 (32 * u) + signExtend12 value' =
      x + signExtend12 value)
    (oldFetched : fetch image state = some (.base (.ADDI .x12 .x23 value)))
    (newFetched : fetch image (unrolledMove u delta state) =
      some (.base (.ADDI .x12 .x23 value')))
    (rest : ∀ next : MachineState, next.pc = state.pc + 4 →
      execute image fuel (unrolledMove u delta next) allowCoins =
        unrolledLift (unrolledMove u delta) <$> execute image fuel next allowCoins) :
    execute image (fuel + 1) (unrolledMove u delta state) allowCoins =
      unrolledLift (unrolledMove u delta) <$> execute image (fuel + 1) state allowCoins :=
  unrolled_execute_ordinary image _ _ _ state fuel allowCoins (by intro h; cases h)
    (by intro h; cases h) oldFetched newFetched
    (unrolled_step_heap u delta state value value' address) rfl
    (fun next stepped => rest next (unrolled_ordinary_pc state next _ rfl rfl stepped))

/-- One instruction of leaf `u` simulates the same instruction of the original body. -/
theorem unrolled_reloc_step (u : Nat) (hu : u < 64) (i : Nat) (hi : i < 31) (fuel : Nat)
    (allowCoins : Bool) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4456 + 4 * i))
    (rest : ∀ next : MachineState, next.pc = BitVec.ofNat 64 (4456 + 4 * (i + 1)) →
      execute (submission.image .commit) fuel (unrolledMove u (unrolledDelta u) next) allowCoins =
        unrolledLift (unrolledMove u (unrolledDelta u)) <$>
          execute (submission.image .commit) fuel next allowCoins) :
    execute (submission.image .commit) (fuel + 1)
        (unrolledMove u (unrolledDelta u) state) allowCoins =
      unrolledLift (unrolledMove u (unrolledDelta u)) <$>
        execute (submission.image .commit) (fuel + 1) state allowCoins := by
  have oldFetched := t1_image_base_leaf i hi state pc
  have newFetched := t1_image_leaf u i hu hi (unrolledMove u (unrolledDelta u) state) (by
    show state.pc + unrolledDelta u = _
    rw [pc, unrolledDelta, ← BitVec.ofNat_add]
    congr 1
    omega)
  have advance : ∀ next : MachineState, next.pc = state.pc + 4 →
      execute (submission.image .commit) fuel (unrolledMove u (unrolledDelta u) next) allowCoins =
        unrolledLift (unrolledMove u (unrolledDelta u)) <$>
          execute (submission.image .commit) fuel next allowCoins := by
    intro next nextPC
    apply rest
    rw [nextPC, pc]
    show BitVec.ofNat 64 (4456 + 4 * i) + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1
  clear rest pc
  interval_cases i <;> first
    | exact unrolled_run_load _ u _ _ _ state fuel allowCoins
        (unrolled_nonce_address u 0 hu (Or.inl rfl)) oldFetched newFetched advance
    | exact unrolled_run_load _ u _ _ _ state fuel allowCoins
        (unrolled_nonce_address u 8 hu (Or.inr (Or.inl rfl))) oldFetched newFetched advance
    | exact unrolled_run_load _ u _ _ _ state fuel allowCoins
        (unrolled_nonce_address u 16 hu (Or.inr (Or.inr rfl))) oldFetched newFetched advance
    | exact unrolled_run_store _ u _ .x6 _ state fuel allowCoins (by decide) (by decide)
        oldFetched newFetched advance
    | exact unrolled_run_store _ u _ .x0 _ state fuel allowCoins (by decide) (by decide)
        oldFetched newFetched advance
    | exact unrolled_run_add _ u _ .x12 _ state fuel allowCoins (by decide) (by decide)
        oldFetched newFetched advance
    | exact unrolled_run_add _ u _ .x10 _ state fuel allowCoins (by decide) (by decide)
        oldFetched newFetched advance
    | exact unrolled_run_heap _ u _ _ _ state fuel allowCoins
        (unrolled_heap_address u hu) oldFetched newFetched advance
    | exact unrolled_execute_call _ u _ state fuel allowCoins oldFetched newFetched advance

/-- Leaf `u` of the group and the original body run in lockstep from any instruction. -/
theorem unrolled_reloc (u : Nat) (hu : u < 64) (allowCoins : Bool) (fuel : Nat) :
    ∀ i : Nat, i + fuel = 31 → ∀ state : MachineState,
      state.pc = BitVec.ofNat 64 (4456 + 4 * i) →
      execute (submission.image .commit) fuel
          (unrolledMove u (unrolledDelta u) state) allowCoins =
        unrolledLift (unrolledMove u (unrolledDelta u)) <$>
          execute (submission.image .commit) fuel state allowCoins := by
  induction fuel with
  | zero =>
    intro i _ state _
    simp only [execute, map_pure]
    rfl
  | succ fuel ih =>
    intro i total state pc
    exact unrolled_reloc_step u hu i (by omega) fuel allowCoins state pc
      (fun next nextPC => ih (i + 1) (by omega) next nextPC)

end CommitGolfCandidate
