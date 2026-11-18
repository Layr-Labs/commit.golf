import CommitGolfCandidate.CapMarkImage
import CommitGolfCandidate.CostedExecution
import CommitGolfCandidate.Memory

/-! The opening's group stub (words 138..191), entered with x20 = position and
left through x1. The head computes the position's cell base
`x9 + 2^28 + 328 + 368 * (position / 4)` and the place `position % 4`; each of
the four blocks either skips its place (two instructions) or copies that leaf
digest of the cell to x25 and advances x25 by 32 (eleven instructions); the
tail sets x20 = position / 4 + x19 and returns. 45 instructions, 48 cycles. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def capStubHeadInstructions : List Instr :=
  [.SRLI .x7 .x20 2, .ADDI .x6 .x0 368, .MUL .x23 .x7 .x6, .LUI .x6 65536,
   .ADD .x23 .x23 .x6, .ADD .x23 .x23 .x9, .ADDI .x23 .x23 328, .ANDI .x30 .x20 3]

def capStubHeadPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capStubHeadInstructions.take count).foldl execInstrBr state

def capStubHeadState (state : MachineState) : MachineState := capStubHeadPrefix state 8

def capStubBlockInstructions (place : Nat) : List Instr :=
  [.ADDI .x6 .x0 (BitVec.ofNat 12 place), .BEQ .x6 .x30 40,
   .LD .x6 .x23 (BitVec.ofNat 12 (32*place)), .SD .x25 .x6 0,
   .LD .x6 .x23 (BitVec.ofNat 12 (32*place+8)), .SD .x25 .x6 8,
   .LD .x6 .x23 (BitVec.ofNat 12 (32*place+16)), .SD .x25 .x6 16,
   .LD .x6 .x23 (BitVec.ofNat 12 (32*place+24)), .SD .x25 .x6 24,
   .ADDI .x25 .x25 32]

def capStubBlockPrefix (place : Nat) (state : MachineState) (count : Nat) : MachineState :=
  ((capStubBlockInstructions place).take count).foldl execInstrBr state

/-- Instructions executed by block `place`: two when it is the record's own place. -/
def capStubBlockSteps (place : Nat) (state : MachineState) : Nat :=
  if state.getReg .x30 = BitVec.ofNat 64 place then 2 else 11

def capStubBlockState (place : Nat) (state : MachineState) : MachineState :=
  capStubBlockPrefix place state (capStubBlockSteps place state)

def capStubTailInstructions : List Instr := [.ADD .x20 .x7 .x19, .JALR .x0 .x1 0]

def capStubTailState (state : MachineState) : MachineState :=
  capStubTailInstructions.foldl execInstrBr state

/-- The complete stub, from its entry to the return. -/
def capOpenStubState (state : MachineState) : MachineState :=
  capStubTailState (capStubBlockState 3 (capStubBlockState 2 (capStubBlockState 1
    (capStubBlockState 0 (capStubHeadState state)))))

private theorem stub_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

private theorem stub_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query =
      (if query = address then value else state.getMem query) := by
  simp [MachineState.getMem, MachineState.setMem]

private theorem fold_take_next {A S : Type} (step : S → A → S)
    (code : List A) (state : S) (fallback : A) (i : Nat) (hi : i < code.length) :
    (code.take (i+1)).foldl step state =
      step ((code.take i).foldl step state) ((code[i]?).getD fallback) := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos code i hi, Option.getD_some]

theorem cap_stub_sign_extend (value : Nat) (small : value < 2048) :
    signExtend12 (BitVec.ofNat 12 value) = BitVec.ofNat 64 value := by
  have msb : (BitVec.ofNat 12 value).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : value < 2^12)]
    simp only [decide_eq_false_iff_not, not_le]
    omega
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-! ### Head -/

theorem cap_stub_head_pc (state : MachineState) (count : Nat) (bounded : count ≤ 8) :
    (capStubHeadPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capStubHeadPrefix, capStubHeadInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_stub_head_memory (state : MachineState) :
    (capStubHeadState state).mem = state.mem := rfl

theorem cap_stub_head_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x30) :
    (capStubHeadState state).getReg reg = state.getReg reg := by
  simp only [capStubHeadState, capStubHeadPrefix, capStubHeadInstructions, List.take,
    List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2)]

theorem cap_stub_head_values (state : MachineState) (position rootBase : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 position) (positionBound : position < 2^24)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase) (rootBound : rootBase + 2^31 ≤ 2^64) :
    (capStubHeadState state).getReg .x7 = BitVec.ofNat 64 (position / 4) ∧
    (capStubHeadState state).getReg .x23 =
      BitVec.ofNat 64 (rootBase + 268435784 + 368 * (position / 4)) ∧
    (capStubHeadState state).getReg .x30 = BitVec.ofNat 64 (position % 4) := by
  have shifted : BitVec.ofNat 64 position >>> (2 : BitVec 6).toNat = BitVec.ofNat 64 (position / 4) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, show (2 : BitVec 6).toNat = 2 by decide,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : position < 2^64),
      Nat.mod_eq_of_lt (by omega : position / 4 < 2^64)]
  have masked : BitVec.ofNat 64 position &&& signExtend12 3 = BitVec.ofNat 64 (position % 4) := by
    rw [show signExtend12 3 = BitVec.ofNat 64 3 by decide]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : position < 2^64),
      Nat.mod_eq_of_lt (by omega : position % 4 < 2^64), Nat.mod_eq_of_lt (by omega : 3 < 2^64)]
    exact Nat.and_two_pow_sub_one_eq_mod position 2
  have cell : BitVec.ofNat 64 (position / 4) * BitVec.ofNat 64 368 +
      ((65536 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 + BitVec.ofNat 64 rootBase +
      signExtend12 328 = BitVec.ofNat 64 (rootBase + 268435784 + 368 * (position / 4)) := by
    rw [show ((65536 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 268435456 by decide,
      show signExtend12 328 = BitVec.ofNat 64 328 by decide, ← BitVec.ofNat_mul,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := decide) only [capStubHeadState, capStubHeadPrefix, capStubHeadInstructions,
      List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, index, shifted]
  · simp (disch := decide) only [capStubHeadState, capStubHeadPrefix, capStubHeadInstructions,
      List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, index, roots, shifted,
      show (0 : Word) + signExtend12 368 = BitVec.ofNat 64 368 by decide]
    exact cell
  · simp (disch := decide) only [capStubHeadState, capStubHeadPrefix, capStubHeadInstructions,
      List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, index, masked]

theorem cap_stub_head_succ (state : MachineState) (count : Nat) (bounded : count < 8) :
    capStubHeadPrefix state (count+1) =
      execInstrBr (capStubHeadPrefix state count) ((capStubHeadInstructions[count]?).getD .EBREAK) :=
  fold_take_next execInstrBr capStubHeadInstructions state .EBREAK count
    (by simpa [capStubHeadInstructions] using bounded)

theorem cap_stub_block_succ (place : Nat) (state : MachineState) (count : Nat) (bounded : count < 11) :
    capStubBlockPrefix place state (count+1) =
      execInstrBr (capStubBlockPrefix place state count)
        (((capStubBlockInstructions place)[count]?).getD .EBREAK) :=
  fold_take_next execInstrBr (capStubBlockInstructions place) state .EBREAK count
    (by simp [capStubBlockInstructions]; omega)

theorem cap_stub_head_execute (state : MachineState) (pc : state.pc = 4648)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (8+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capStubHeadState state) allowCoins
          return result.charge 11 0) := by
  change _ = (do
    let result ← execute ((capExperimental 24).image .opening) fuel
      (capStubHeadPrefix state 8) allowCoins
    return result.charge (linearTraceCost 8 (fun i => if i = 2 then 4 else 1)) 0)
  apply execute_costed_steps (states := capStubHeadPrefix state)
    (costs := fun i => if i = 2 then 4 else 1)
  intro i bounded
  refine ⟨.base ((capStubHeadInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (138+i) _ (by omega)
    · rw [cap_stub_head_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · rw [cap_stub_head_succ state i bounded]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-! ### Blocks -/

private theorem stub_getMem_setReg (state : MachineState) (reg : Reg) (value query : Word) :
    (state.setReg reg value).getMem query = state.getMem query := by
  cases reg <;> rfl

private theorem stub_getMem_setPC (state : MachineState) (value query : Word) :
    (state.setPC value).getMem query = state.getMem query := rfl

private theorem stub_branch_register (state : MachineState) (left right : Reg) (offset : BitVec 13)
    (reg : Reg) : (execInstrBr state (.BEQ left right offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> rfl

private theorem stub_branch_memory (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BEQ left right offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem stub_x0 (state : MachineState) : state.getReg .x0 = 0 := rfl

theorem cap_stub_block_first (place : Nat) (inside : place < 4) (state : MachineState) :
    (capStubBlockPrefix place state 1).getReg .x6 = BitVec.ofNat 64 place ∧
    (capStubBlockPrefix place state 1).pc = state.pc + 4 ∧
    (capStubBlockPrefix place state 1).mem = state.mem ∧
    ∀ reg, reg ≠ .x6 → (capStubBlockPrefix place state 1).getReg reg = state.getReg reg := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · simp (disch := decide) only [capStubBlockPrefix, capStubBlockInstructions, List.take,
      List.foldl, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      cap_stub_sign_extend place (by omega), stub_x0]
    first | exact BitVec.zero_add _ | simp
  · intro reg outside
    simp only [capStubBlockPrefix, capStubBlockInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_stub_block_skip_state (place : Nat) (inside : place < 4) (state : MachineState)
    (own : state.getReg .x30 = BitVec.ofNat 64 place) :
    capStubBlockState place state =
      ((capStubBlockPrefix place state 1).setPC (state.pc + 44)) := by
  have first := cap_stub_block_first place inside state
  have taken : ((capStubBlockPrefix place state 1).getReg .x6 ==
      (capStubBlockPrefix place state 1).getReg .x30) = true := by
    rw [first.1, first.2.2.2 .x30 (by decide), own]
    exact beq_self_eq_true _
  rw [capStubBlockState, capStubBlockSteps, if_pos own, cap_stub_block_succ place state 1 (by decide)]
  change execInstrBr (capStubBlockPrefix place state 1) (.BEQ .x6 .x30 40) = _
  simp only [execInstrBr, taken, ↓reduceIte, first.2.1]
  congr 1
  rw [BitVec.add_assoc]
  rfl

theorem cap_stub_block_two (place : Nat) (inside : place < 4) (state : MachineState)
    (other : state.getReg .x30 ≠ BitVec.ofNat 64 place) :
    (capStubBlockPrefix place state 2).pc = state.pc + 8 ∧
    (capStubBlockPrefix place state 2).mem = state.mem ∧
    ∀ reg, reg ≠ .x6 → (capStubBlockPrefix place state 2).getReg reg = state.getReg reg := by
  have first := cap_stub_block_first place inside state
  have notTaken : ((capStubBlockPrefix place state 1).getReg .x6 ==
      (capStubBlockPrefix place state 1).getReg .x30) = false := by
    rw [first.1, first.2.2.2 .x30 (by decide)]
    simpa only [beq_eq_false_iff_ne, ne_eq] using Ne.symm other
  rw [cap_stub_block_succ place state 1 (by decide)]
  change (execInstrBr (capStubBlockPrefix place state 1) (.BEQ .x6 .x30 40)).pc = _ ∧
    (execInstrBr (capStubBlockPrefix place state 1) (.BEQ .x6 .x30 40)).mem = _ ∧ _
  refine ⟨?_, (stub_branch_memory _ _ _ _).trans first.2.2.1, ?_⟩
  · simp only [execInstrBr, notTaken, Bool.false_eq_true, ↓reduceIte, MachineState.setPC, first.2.1,
      BitVec.add_assoc]
    rfl
  · intro reg outside
    exact (stub_branch_register _ _ _ _ reg).trans (first.2.2.2 reg outside)

theorem cap_stub_block_copy_pc (place : Nat) (inside : place < 4) (state : MachineState)
    (other : state.getReg .x30 ≠ BitVec.ofNat 64 place) (count : Nat) (bounded : count ≤ 11) :
    (capStubBlockPrefix place state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  have first := cap_stub_block_first place inside state
  have two := cap_stub_block_two place inside state other
  have after (more : Nat) (small : more ≤ 9) :
      (capStubBlockPrefix place state (2+more)).pc = state.pc + BitVec.ofNat 64 (8+4*more) := by
    induction more with
    | zero => simpa using two.1
    | succ more ih =>
      rw [show 2+(more+1) = (2+more)+1 by omega, cap_stub_block_succ place state (2+more) (by omega)]
      have previous := ih (by omega)
      have smallMore : more ≤ 8 := by omega
      interval_cases more <;>
        simp only [capStubBlockInstructions, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some, execInstrBr, MachineState.setPC, previous, BitVec.add_assoc] <;> rfl
  by_cases low : count < 2
  · interval_cases count
    · simp [capStubBlockPrefix]
    · rw [first.2.1]; rfl
  · have shape := after (count-2) (by omega)
    rw [show 2+(count-2) = count by omega, show 8+4*(count-2) = 4*count by omega] at shape
    exact shape

theorem cap_stub_block_copy_register (place : Nat) (inside : place < 4) (state : MachineState)
    (other : state.getReg .x30 ≠ BitVec.ofNat 64 place) (count : Nat) (bounded : count ≤ 10)
    (reg : Reg) (outside : reg ≠ .x6) :
    (capStubBlockPrefix place state count).getReg reg = state.getReg reg := by
  have first := cap_stub_block_first place inside state
  have two := cap_stub_block_two place inside state other
  induction count with
  | zero => rfl
  | succ count ih =>
    by_cases small : count < 2
    · interval_cases count
      · exact first.2.2.2 reg outside
      · exact two.2.2 reg outside
    have previous := ih (by omega)
    rw [cap_stub_block_succ place state count (by omega)]
    have smallCount : count ≤ 9 := by omega
    interval_cases count <;>
      simp only [capStubBlockInstructions, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some, execInstrBr, MachineState.getReg_setPC, stub_getReg_setMem,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside), previous]

private theorem pc_word (base offset index : Nat) (equal : base + offset = 4096 + 4*index) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 offset = BitVec.ofNat 64 (4096 + 4*index) := by
  rw [← BitVec.ofNat_add, equal]

theorem cap_stub_block_execute (place : Nat) (inside : place < 4) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4680 + 44*place))
    (sourceValid : state.getReg .x30 ≠ BitVec.ofNat 64 place → ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (32*place + 8*word.val)) 8 = true)
    (destinationValid : state.getReg .x30 ≠ BitVec.ofNat 64 place → ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (capStubBlockSteps place state+fuel)
        state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capStubBlockState place state) allowCoins
          return result.charge (capStubBlockSteps place state) 0) := by
  have first := cap_stub_block_first place inside state
  by_cases own : state.getReg .x30 = BitVec.ofNat 64 place
  · have steps : capStubBlockSteps place state = 2 := if_pos own
    rw [steps, capStubBlockState, steps]
    apply execute_unit_steps (states := capStubBlockPrefix place state)
    intro i bounded
    refine ⟨.base (((capStubBlockInstructions place)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply cap_image_fetch _ _ (146+11*place+i) _ (by omega)
      · interval_cases i
        · change state.pc = _
          rw [pc]
          congr 1
          omega
        · rw [first.2.1, pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl]
          exact pc_word _ _ _ (by omega)
      · interval_cases place <;> interval_cases i <;> rfl
    · rw [cap_stub_block_succ place state i (by omega)]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · have steps : capStubBlockSteps place state = 11 := if_neg own
    rw [steps, capStubBlockState, steps]
    apply execute_unit_steps (states := capStubBlockPrefix place state)
    intro i bounded
    refine ⟨.base (((capStubBlockInstructions place)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply cap_image_fetch _ _ (146+11*place+i) _ (by omega)
      · rw [cap_stub_block_copy_pc place inside state own i (by omega), pc]
        exact pc_word _ _ _ (by omega)
      · interval_cases place <;> interval_cases i <;> rfl
    · rw [cap_stub_block_succ place state i (by omega)]
      have source := cap_stub_block_copy_register place inside state own i (by omega) .x23 (by decide)
      have destination := cap_stub_block_copy_register place inside state own i (by omega) .x25
        (by decide)
      have s := sourceValid own
      have d := destinationValid own
      have s0 := s ⟨0, by decide⟩
      have s1 := s ⟨1, by decide⟩
      have s2 := s ⟨2, by decide⟩
      have s3 := s ⟨3, by decide⟩
      have d0 : accessValid (state.getReg .x25) 8 = true := by
        have zero := d ⟨0, by decide⟩
        simpa using zero
      have d1 := d ⟨1, by decide⟩
      have d2 := d ⟨2, by decide⟩
      have d3 := d ⟨3, by decide⟩
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at s0 s1 s2 s3 d1 d2 d3
      interval_cases i <;>
        simp only [capStubBlockInstructions, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some, ordinaryStep, memoryArgumentsValid, memAccess, source, destination,
          cap_stub_sign_extend _ (by omega : 32*place < 2048),
          cap_stub_sign_extend _ (by omega : 32*place+8 < 2048),
          cap_stub_sign_extend _ (by omega : 32*place+16 < 2048),
          cap_stub_sign_extend _ (by omega : 32*place+24 < 2048),
          show signExtend12 (0 : BitVec 12) = 0#64 from rfl, BitVec.add_zero,
          show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 from rfl,
          show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from rfl,
          show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from rfl,
          s0, s1, s2, s3, d0, d1, d2, d3, ↓reduceIte]
    · interval_cases i <;> rfl

theorem cap_stub_word_ne (left right : Nat) (leftBound : left < 2^64) (rightBound : right < 2^64)
    (different : left ≠ right) : BitVec.ofNat 64 left ≠ BitVec.ofNat 64 right := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] at natural
  exact different natural

theorem cap_stub_block_skip_facts (place : Nat) (inside : place < 4) (state : MachineState)
    (own : state.getReg .x30 = BitVec.ofNat 64 place) :
    (capStubBlockState place state).pc = state.pc + 44 ∧
    (capStubBlockState place state).mem = state.mem ∧
    ∀ reg, reg ≠ .x6 → (capStubBlockState place state).getReg reg = state.getReg reg := by
  have first := cap_stub_block_first place inside state
  rw [cap_stub_block_skip_state place inside state own]
  refine ⟨rfl, first.2.2.1, ?_⟩
  intro reg outside
  rw [MachineState.getReg_setPC]
  exact first.2.2.2 reg outside

/-- A load from x23 followed by a store at x25 copies one word. -/
private theorem stub_pair_memory (state : MachineState) (off off' : BitVec 12) (query : Word) :
    (execInstrBr (execInstrBr state (.LD .x6 .x23 off)) (.SD .x25 .x6 off')).getMem query =
      if query = state.getReg .x25 + signExtend12 off' then
        state.getMem (state.getReg .x23 + signExtend12 off) else state.getMem query := by
  simp only [execInstrBr, stub_getMem_setPC, stub_getMem_setMem, stub_getMem_setReg,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x25)]

theorem cap_stub_block_copy_facts (place : Nat) (inside : place < 4) (state : MachineState)
    (other : state.getReg .x30 ≠ BitVec.ofNat 64 place)
    (source destination : Nat)
    (sourcePointer : state.getReg .x23 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (sourceBound : source + 128 ≤ 2^64) (destinationBound : destination + 32 ≤ 2^64)
    (separate : source + 128 ≤ destination ∨ destination + 32 ≤ source) :
    (capStubBlockState place state).pc = state.pc + 44 ∧
    (capStubBlockState place state).getReg .x25 = BitVec.ofNat 64 (destination + 32) ∧
    (∀ reg, reg ≠ .x6 → reg ≠ .x25 →
      (capStubBlockState place state).getReg reg = state.getReg reg) ∧
    (∀ word < 4, (capStubBlockState place state).getMem (BitVec.ofNat 64 (destination + 8*word)) =
      state.getMem (BitVec.ofNat 64 (source + 32*place + 8*word))) ∧
    (∀ address : Nat, address < 2^64 → (address < destination ∨ destination + 32 ≤ address) →
      (capStubBlockState place state).getMem (BitVec.ofNat 64 address) =
        state.getMem (BitVec.ofNat 64 address)) := by
  have steps : capStubBlockSteps place state = 11 := if_neg other
  have two := cap_stub_block_two place inside state other
  have reg10 := cap_stub_block_copy_register place inside state other
  have ne (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (h : a ≠ b) :=
    cap_stub_word_ne a b ha hb h
  have e10 := ne (source+32*place+8) destination (by omega) (by omega) (by omega)
  have e20 := ne (source+32*place+16) destination (by omega) (by omega) (by omega)
  have e21 := ne (source+32*place+16) (destination+8) (by omega) (by omega) (by omega)
  have e30 := ne (source+32*place+24) destination (by omega) (by omega) (by omega)
  have e31 := ne (source+32*place+24) (destination+8) (by omega) (by omega) (by omega)
  have e32 := ne (source+32*place+24) (destination+16) (by omega) (by omega) (by omega)
  have src (k : Nat) (small : 32*place+k < 2048) (pointer : ∀ count ≤ 10, count = count →
      (capStubBlockPrefix place state count).getReg .x23 = BitVec.ofNat 64 source) (count : Nat)
      (bounded : count ≤ 10) :
      (capStubBlockPrefix place state count).getReg .x23 + signExtend12 (BitVec.ofNat 12 (32*place+k)) =
        BitVec.ofNat 64 (source+32*place+k) := by
    rw [pointer count bounded rfl, cap_stub_sign_extend _ small, ← BitVec.ofNat_add, Nat.add_assoc]
  have srcPointer : ∀ count ≤ 10, count = count →
      (capStubBlockPrefix place state count).getReg .x23 = BitVec.ofNat 64 source :=
    fun count bounded _ => (reg10 count bounded .x23 (by decide)).trans sourcePointer
  have dst (count : Nat) (bounded : count ≤ 10) (off : BitVec 12) (k : Nat)
      (extended : signExtend12 off = BitVec.ofNat 64 k) :
      (capStubBlockPrefix place state count).getReg .x25 + signExtend12 off =
        BitVec.ofNat 64 (destination+k) := by
    rw [(reg10 count bounded .x25 (by decide)).trans destinationPointer, extended,
      ← BitVec.ofNat_add]
  have pairStep (count : Nat) (bounded : count + 2 ≤ 10) (off off' : BitVec 12)
      (first : (capStubBlockInstructions place)[count]? = some (.LD .x6 .x23 off))
      (second : (capStubBlockInstructions place)[count+1]? = some (.SD .x25 .x6 off')) (query : Word) :
      (capStubBlockPrefix place state (count+2)).getMem query =
        if query = (capStubBlockPrefix place state count).getReg .x25 + signExtend12 off' then
          (capStubBlockPrefix place state count).getMem
            ((capStubBlockPrefix place state count).getReg .x23 + signExtend12 off)
        else (capStubBlockPrefix place state count).getMem query := by
    rw [cap_stub_block_succ place state (count+1) (by omega), cap_stub_block_succ place state count (by omega),
      first, second]
    exact stub_pair_memory _ off off' query
  have m4 := pairStep 2 (by omega) (BitVec.ofNat 12 (32*place)) 0 rfl rfl
  have m6 := pairStep 4 (by omega) (BitVec.ofNat 12 (32*place+8)) 8 rfl rfl
  have m8 := pairStep 6 (by omega) (BitVec.ofNat 12 (32*place+16)) 16 rfl rfl
  have m10 := pairStep 8 (by omega) (BitVec.ofNat 12 (32*place+24)) 24 rfl rfl
  have src0 := src 0 (by omega) srcPointer 2 (by omega)
  simp only [Nat.add_zero] at src0
  rw [dst 2 (by omega) 0 0 rfl, Nat.add_zero, src0] at m4
  rw [dst 4 (by omega) 8 8 rfl, src 8 (by omega) srcPointer 4 (by omega)] at m6
  rw [dst 6 (by omega) 16 16 rfl, src 16 (by omega) srcPointer 6 (by omega)] at m8
  rw [dst 8 (by omega) 24 24 rfl, src 24 (by omega) srcPointer 8 (by omega)] at m10
  have m2 : ∀ query, (capStubBlockPrefix place state 2).getMem query = state.getMem query := by
    intro query
    simp only [MachineState.getMem, two.2.1]
  have m11 : ∀ query, (capStubBlockPrefix place state 11).getMem query =
      (capStubBlockPrefix place state 10).getMem query := by
    intro query
    rw [cap_stub_block_succ place state 10 (by decide)]
    rfl
  have memory : ∀ query : Word, (capStubBlockState place state).getMem query =
      if query = BitVec.ofNat 64 (destination+24) then state.getMem (BitVec.ofNat 64 (source+32*place+24))
      else if query = BitVec.ofNat 64 (destination+16) then state.getMem (BitVec.ofNat 64 (source+32*place+16))
      else if query = BitVec.ofNat 64 (destination+8) then state.getMem (BitVec.ofNat 64 (source+32*place+8))
      else if query = BitVec.ofNat 64 destination then state.getMem (BitVec.ofNat 64 (source+32*place))
      else state.getMem query := by
    intro query
    rw [capStubBlockState, steps, m11, m10, m8, m8, m6, m6, m6, m4, m4, m4, m4]
    simp only [m2, Nat.add_zero, e10, e20, e21, e30, e31, e32, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [capStubBlockState, steps, cap_stub_block_copy_pc place inside state other 11 (by decide)]
    rfl
  · rw [capStubBlockState, steps, cap_stub_block_succ place state 10 (by decide)]
    change (execInstrBr (capStubBlockPrefix place state 10) (.ADDI .x25 .x25 32)).getReg .x25 = _
    simp only [execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0)]
    exact dst 10 (by decide) 32 32 rfl
  · intro reg notSix notCursor
    rw [capStubBlockState, steps, cap_stub_block_succ place state 10 (by decide)]
    change (execInstrBr (capStubBlockPrefix place state 10) (.ADDI .x25 .x25 32)).getReg reg = _
    simp only [execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCursor)]
    exact reg10 10 (by decide) reg notSix
  · intro word bounded
    rw [memory]
    interval_cases word
    · have a := ne destination (destination+24) (by omega) (by omega) (by omega)
      have b := ne destination (destination+16) (by omega) (by omega) (by omega)
      have c := ne destination (destination+8) (by omega) (by omega) (by omega)
      simp only [Nat.mul_zero, Nat.add_zero, a, b, c, ↓reduceIte]
    · have a := ne (destination+8) (destination+24) (by omega) (by omega) (by omega)
      have b := ne (destination+8) (destination+16) (by omega) (by omega) (by omega)
      simp only [Nat.mul_one, a, b, ↓reduceIte]
    · have a := ne (destination+16) (destination+24) (by omega) (by omega) (by omega)
      simp only [Nat.reduceMul, a, ↓reduceIte]
    · simp only [Nat.reduceMul, ↓reduceIte]
  · intro address bounded outside
    rw [memory]
    have a := ne address (destination+24) bounded (by omega) (by omega)
    have b := ne address (destination+16) bounded (by omega) (by omega)
    have c := ne address (destination+8) bounded (by omega) (by omega)
    have d := ne address destination bounded (by omega) (by omega)
    simp only [a, b, c, d, ↓reduceIte]

/-! ### Tail -/

theorem cap_stub_tail_facts (state : MachineState) (link : state.getReg .x1 = 4264) :
    (capStubTailState state).pc = 4264 ∧
    (capStubTailState state).mem = state.mem ∧
    (capStubTailState state).getReg .x20 = state.getReg .x7 + state.getReg .x19 ∧
    ∀ reg, reg ≠ .x20 → (capStubTailState state).getReg reg = state.getReg reg := by
  have link' : ((state.setReg .x20 (state.getReg .x7 + state.getReg .x19)).setPC (state.pc + 4)).getReg .x1 =
      4264 := by
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide), link]
  refine ⟨?_, rfl, ?_, ?_⟩
  · change ((((state.setReg .x20 (state.getReg .x7 + state.getReg .x19)).setPC (state.pc + 4)).setReg .x0 _).setPC
      ((((state.setReg .x20 (state.getReg .x7 + state.getReg .x19)).setPC (state.pc + 4)).getReg .x1 +
        signExtend12 0) &&& ~~~1#64)).pc = 4264
    rw [link']
    rfl
  · change ((((state.setReg .x20 (state.getReg .x7 + state.getReg .x19)).setPC (state.pc + 4)).setReg .x0 _).setPC _).getReg .x20 = _
    rfl
  · intro reg outside
    change ((((state.setReg .x20 (state.getReg .x7 + state.getReg .x19)).setPC (state.pc + 4)).setReg .x0 _).setPC _).getReg reg = _
    simp only [MachineState.getReg_setPC]
    change ((state.setReg .x20 (state.getReg .x7 + state.getReg .x19)).setPC (state.pc + 4)).getReg reg = _
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_stub_tail_execute (state : MachineState) (pc : state.pc = 4856)
    (link : state.getReg .x1 = 4264) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (2+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capStubTailState state) allowCoins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := fun i => (capStubTailInstructions.take i).foldl execInstrBr state)
  intro i bounded
  refine ⟨.base ((capStubTailInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (190+i) _ (by omega)
    · interval_cases i
      · simpa using pc
      · simp only [capStubTailInstructions, List.take, List.foldl, execInstrBr, MachineState.setPC, pc]
        rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-! ### The whole stub -/

theorem cap_stub_word_access (address : Nat) (aligned : address % 8 = 0)
    (bounded : address + 8 ≤ MEMORY_BYTES) : accessValid (BitVec.ofNat 64 address) 8 = true := by
  have small : address < 2^64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, bounded, aligned,
    decide_true, Bool.true_and]

/-- Three successive copies to `cursor`, `cursor + 32`, `cursor + 64` from sources below `cursor`. -/
theorem cap_stub_chain (m0 m1 m2 m3 : Word → Word) (cursor : Nat) (source : Nat → Nat)
    (bound : cursor + 96 ≤ 2^64) (below : ∀ k < 3, source k + 32 ≤ cursor)
    (w1 : ∀ w < 4, m1 (BitVec.ofNat 64 (cursor + 8*w)) = m0 (BitVec.ofNat 64 (source 0 + 8*w)))
    (o1 : ∀ a < 2^64, (a < cursor ∨ cursor + 32 ≤ a) → m1 (BitVec.ofNat 64 a) = m0 (BitVec.ofNat 64 a))
    (w2 : ∀ w < 4, m2 (BitVec.ofNat 64 (cursor + 32 + 8*w)) = m1 (BitVec.ofNat 64 (source 1 + 8*w)))
    (o2 : ∀ a < 2^64, (a < cursor + 32 ∨ cursor + 32 + 32 ≤ a) →
      m2 (BitVec.ofNat 64 a) = m1 (BitVec.ofNat 64 a))
    (w3 : ∀ w < 4, m3 (BitVec.ofNat 64 (cursor + 64 + 8*w)) = m2 (BitVec.ofNat 64 (source 2 + 8*w)))
    (o3 : ∀ a < 2^64, (a < cursor + 64 ∨ cursor + 64 + 32 ≤ a) →
      m3 (BitVec.ofNat 64 a) = m2 (BitVec.ofNat 64 a)) :
    (∀ k < 3, ∀ w < 4, m3 (BitVec.ofNat 64 (cursor + 32*k + 8*w)) =
      m0 (BitVec.ofNat 64 (source k + 8*w))) ∧
    (∀ a < 2^64, (a < cursor ∨ cursor + 96 ≤ a) → m3 (BitVec.ofNat 64 a) = m0 (BitVec.ofNat 64 a)) := by
  have b0 := below 0 (by decide)
  have b1 := below 1 (by decide)
  have b2 := below 2 (by decide)
  refine ⟨?_, ?_⟩
  · intro k hk w hw
    interval_cases k
    · rw [o3 _ (by omega) (by omega), o2 _ (by omega) (by omega)]
      simpa using w1 w hw
    · rw [o3 _ (by omega) (by omega), show cursor + 32*1 + 8*w = cursor + 32 + 8*w by omega, w2 w hw,
        o1 _ (by omega) (by omega)]
    · rw [show cursor + 32*2 + 8*w = cursor + 64 + 8*w by omega, w3 w hw, o2 _ (by omega) (by omega),
        o1 _ (by omega) (by omega)]
  · intro a ha outside
    rw [o3 a ha (by omega), o2 a ha (by omega), o1 a ha (by omega)]

/-- Place in the cell of the `k`-th copied digest (`k < 3`) for own place `own`. -/
def capStubPlace (own k : Nat) : Nat := if k < own then k else k+1

theorem cap_stub_block_any (place own cell cursor : Nat) (inside : place < 4) (ownBound : own < 4)
    (state : MachineState) (rest : state.getReg .x30 = BitVec.ofNat 64 own)
    (source : state.getReg .x23 = BitVec.ofNat 64 cell)
    (destination : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (separate : cell + 128 ≤ cursor) (bound : cursor + 32 ≤ 2^64) :
    (capStubBlockState place state).pc = state.pc + 44 ∧
    (capStubBlockState place state).getReg .x25 =
      BitVec.ofNat 64 (cursor + if place = own then 0 else 32) ∧
    (∀ reg, reg ≠ .x6 → reg ≠ .x25 →
      (capStubBlockState place state).getReg reg = state.getReg reg) ∧
    (place ≠ own → ∀ w < 4, (capStubBlockState place state).getMem (BitVec.ofNat 64 (cursor + 8*w)) =
      state.getMem (BitVec.ofNat 64 (cell + 32*place + 8*w))) ∧
    (∀ a < 2^64, (place = own ∨ a < cursor ∨ cursor + 32 ≤ a) →
      (capStubBlockState place state).getMem (BitVec.ofNat 64 a) = state.getMem (BitVec.ofNat 64 a)) := by
  by_cases same : place = own
  · subst same
    have facts := cap_stub_block_skip_facts place inside state rest
    refine ⟨facts.1, ?_, fun reg h _ => facts.2.2 reg h, fun h => absurd rfl h, ?_⟩
    · rw [facts.2.2 .x25 (by decide), destination]
      simp
    · intro a _ _
      simp only [MachineState.getMem, facts.2.1]
  · have other : state.getReg .x30 ≠ BitVec.ofNat 64 place := by
      rw [rest]
      exact cap_stub_word_ne _ _ (by omega) (by omega) (Ne.symm same)
    have facts := cap_stub_block_copy_facts place inside state other cell cursor source destination
      (by omega) bound (Or.inl separate)
    refine ⟨facts.1, ?_, facts.2.2.1, fun _ => facts.2.2.2.1, ?_⟩
    · rw [facts.2.1, if_neg same]
    · intro a ha outside
      exact facts.2.2.2.2 a ha (outside.resolve_left same)

theorem cap_open_stub_facts (state : MachineState) (position rootBase cursor : Nat)
    (link : state.getReg .x1 = 4264)
    (index : state.getReg .x20 = BitVec.ofNat 64 position) (positionBound : position < 2^24)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (groups : state.getReg .x19 = BitVec.ofNat 64 4194304)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (separate : rootBase + 2^31 ≤ cursor) (bound : cursor + 128 ≤ 2^64) :
    (capOpenStubState state).pc = 4264 ∧
    (capOpenStubState state).getReg .x20 = BitVec.ofNat 64 (position/4 + 4194304) ∧
    (capOpenStubState state).getReg .x25 = BitVec.ofNat 64 (cursor + 96) ∧
    (∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x23 → reg ≠ .x30 → reg ≠ .x20 → reg ≠ .x25 →
      (capOpenStubState state).getReg reg = state.getReg reg) ∧
    (∀ k < 3, ∀ w < 4, (capOpenStubState state).getMem (BitVec.ofNat 64 (cursor + 32*k + 8*w)) =
      state.getMem (BitVec.ofNat 64 (rootBase + 268435784 + 368*(position/4) +
        32*capStubPlace (position%4) k + 8*w))) ∧
    (∀ a < 2^64, (a < cursor ∨ cursor + 96 ≤ a) →
      (capOpenStubState state).getMem (BitVec.ofNat 64 a) = state.getMem (BitVec.ofNat 64 a)) := by
  obtain ⟨hx7, hx23, hx30⟩ := cap_stub_head_values state position rootBase index positionBound roots
    (by omega)
  obtain ⟨cell, hcell⟩ : ∃ cell, cell = rootBase + 268435784 + 368*(position/4) := ⟨_, rfl⟩
  rw [← hcell] at hx23 ⊢
  have cellBound : cell + 128 ≤ cursor := by
    have : 368*(position/4) ≤ 368*(2^22) := Nat.mul_le_mul_left _ (by omega)
    omega
  let t0 := capStubHeadState state
  have t0reg : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x23 → reg ≠ .x30 → t0.getReg reg = state.getReg reg :=
    fun reg a b c d => cap_stub_head_register state reg ⟨a, b, c, d⟩
  have t0mem : t0.getMem = state.getMem := by
    funext query
    simp only [MachineState.getMem, t0, cap_stub_head_memory]
  have own := Nat.mod_lt position (by decide : 4 > 0)
  obtain ⟨c1, hc1⟩ : ∃ c, c = cursor + (if 0 = position%4 then 0 else 32) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = c1 + (if 1 = position%4 then 0 else 32) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c, c = c2 + (if 2 = position%4 then 0 else 32) := ⟨_, rfl⟩
  have offsets : (position%4 = 0 ∧ c1 = cursor ∧ c2 = cursor+32 ∧ c3 = cursor+64) ∨
      (position%4 = 1 ∧ c1 = cursor+32 ∧ c2 = cursor+32 ∧ c3 = cursor+64) ∨
      (position%4 = 2 ∧ c1 = cursor+32 ∧ c2 = cursor+64 ∧ c3 = cursor+64) ∨
      (position%4 = 3 ∧ c1 = cursor+32 ∧ c2 = cursor+64 ∧ c3 = cursor+96) := by
    subst hc3 hc2 hc1
    rcases (by omega : position%4 = 0 ∨ position%4 = 1 ∨ position%4 = 2 ∨ position%4 = 3)
      with h | h | h | h <;> simp [h]
  have k0 := cap_stub_block_any 0 (position%4) cell cursor (by decide) own t0 hx30 hx23
    ((t0reg .x25 (by decide) (by decide) (by decide) (by decide)).trans pointer) (by omega) (by omega)
  rw [← hc1] at k0
  let t1 := capStubBlockState 0 t0
  have k1 := cap_stub_block_any 1 (position%4) cell c1 (by decide) own t1
    ((k0.2.2.1 .x30 (by decide) (by decide)).trans hx30)
    ((k0.2.2.1 .x23 (by decide) (by decide)).trans hx23) k0.2.1
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
  rw [← hc2] at k1
  let t2 := capStubBlockState 1 t1
  have k2 := cap_stub_block_any 2 (position%4) cell c2 (by decide) own t2
    ((k1.2.2.1 .x30 (by decide) (by decide)).trans ((k0.2.2.1 .x30 (by decide) (by decide)).trans hx30))
    ((k1.2.2.1 .x23 (by decide) (by decide)).trans ((k0.2.2.1 .x23 (by decide) (by decide)).trans hx23))
    k1.2.1
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
  rw [← hc3] at k2
  let t3 := capStubBlockState 2 t2
  have k3 := cap_stub_block_any 3 (position%4) cell c3 (by decide) own t3
    ((k2.2.2.1 .x30 (by decide) (by decide)).trans ((k1.2.2.1 .x30 (by decide) (by decide)).trans
      ((k0.2.2.1 .x30 (by decide) (by decide)).trans hx30)))
    ((k2.2.2.1 .x23 (by decide) (by decide)).trans ((k1.2.2.1 .x23 (by decide) (by decide)).trans
      ((k0.2.2.1 .x23 (by decide) (by decide)).trans hx23)))
    k2.2.1
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
  let t4 := capStubBlockState 3 t3
  have t4reg : ∀ reg, reg ≠ .x6 → reg ≠ .x25 → t4.getReg reg = t0.getReg reg := fun reg a b =>
    (k3.2.2.1 reg a b).trans ((k2.2.2.1 reg a b).trans ((k1.2.2.1 reg a b).trans (k0.2.2.1 reg a b)))
  have t4link : t4.getReg .x1 = 4264 :=
    (t4reg .x1 (by decide) (by decide)).trans ((t0reg .x1 (by decide) (by decide) (by decide) (by decide)).trans link)
  have tail := cap_stub_tail_facts t4 t4link
  have final : capOpenStubState state = capStubTailState t4 := rfl
  have tailMem : (capStubTailState t4).getMem = t4.getMem := by
    funext query
    simp only [MachineState.getMem, tail.2.1]
  have total : c3 + (if 3 = position%4 then 0 else 32) = cursor + 96 := by
    rcases offsets with ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ | ⟨h, _, _, _⟩ <;> simp [h] <;> omega
  have skipMem (place : Nat) (inside : place < 4) (t : MachineState)
      (rest : t.getReg .x30 = BitVec.ofNat 64 place) : (capStubBlockState place t).getMem = t.getMem := by
    funext query
    simp only [MachineState.getMem, (cap_stub_block_skip_facts place inside t rest).2.1]
  have x30at1 : t1.getReg .x30 = BitVec.ofNat 64 (position%4) := (k0.2.2.1 .x30 (by decide) (by decide)).trans hx30
  have x30at2 : t2.getReg .x30 = BitVec.ofNat 64 (position%4) := (k1.2.2.1 .x30 (by decide) (by decide)).trans x30at1
  have x30at3 : t3.getReg .x30 = BitVec.ofNat 64 (position%4) := (k2.2.2.1 .x30 (by decide) (by decide)).trans x30at2
  have chain (m0 m1 m2 m3 : Word → Word) := cap_stub_chain m0 m1 m2 m3 cursor
      (fun k => cell + 32*capStubPlace (position%4) k) (by omega)
      (by intro k hk
          have : capStubPlace (position%4) k ≤ 3 := by unfold capStubPlace; split <;> omega
          omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [final]; exact tail.1
  · rw [final, tail.2.2.1, t4reg .x7 (by decide) (by decide), t4reg .x19 (by decide) (by decide),
      hx7, t0reg .x19 (by decide) (by decide) (by decide) (by decide), groups, ← BitVec.ofNat_add]
  · rw [final, tail.2.2.2 .x25 (by decide), k3.2.1, total]
  · intro reg a b c d e f
    rw [final, tail.2.2.2 reg e, t4reg reg a f, t0reg reg a b c d]
  · rw [final, tailMem]
    rcases offsets with ⟨h, e1, e2, e3⟩ | ⟨h, e1, e2, e3⟩ | ⟨h, e1, e2, e3⟩ | ⟨h, e1, e2, e3⟩
    · have s1 : t1.getMem = t0.getMem := skipMem 0 (by decide) t0 (by rw [hx30, h])
      have c := chain t1.getMem t2.getMem t3.getMem t4.getMem
        (by intro w hw; have k := k1.2.2.2.1 (by omega) w hw; rw [e1] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k1.2.2.2.2 a ha (by omega))
        (by intro w hw; have k := k2.2.2.2.1 (by omega) w hw; rw [e2] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k2.2.2.2.2 a ha (by omega))
        (by intro w hw; have k := k3.2.2.2.1 (by omega) w hw; rw [e3] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k3.2.2.2.2 a ha (by omega))
      intro k hk w hw
      rw [c.1 k hk w hw, s1, t0mem]
    · have s2 : t2.getMem = t1.getMem := skipMem 1 (by decide) t1 (by rw [x30at1, h])
      have c := chain t0.getMem t1.getMem t3.getMem t4.getMem
        (by intro w hw; have k := k0.2.2.2.1 (by omega) w hw; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k0.2.2.2.2 a ha (Or.inr o))
        (by intro w hw; have k := k2.2.2.2.1 (by omega) w hw; rw [e2, s2] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; rw [k2.2.2.2.2 a ha (by omega), s2])
        (by intro w hw; have k := k3.2.2.2.1 (by omega) w hw; rw [e3] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k3.2.2.2.2 a ha (by omega))
      intro k hk w hw
      rw [c.1 k hk w hw, t0mem]
    · have s3 : t3.getMem = t2.getMem := skipMem 2 (by decide) t2 (by rw [x30at2, h])
      have c := chain t0.getMem t1.getMem t2.getMem t4.getMem
        (by intro w hw; have k := k0.2.2.2.1 (by omega) w hw; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k0.2.2.2.2 a ha (Or.inr o))
        (by intro w hw; have k := k1.2.2.2.1 (by omega) w hw; rw [e1] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k1.2.2.2.2 a ha (by omega))
        (by intro w hw; have k := k3.2.2.2.1 (by omega) w hw; rw [e3, s3] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; rw [k3.2.2.2.2 a ha (by omega), s3])
      intro k hk w hw
      rw [c.1 k hk w hw, t0mem]
    · have s4 : t4.getMem = t3.getMem := skipMem 3 (by decide) t3 (by rw [x30at3, h])
      have c := chain t0.getMem t1.getMem t2.getMem t3.getMem
        (by intro w hw; have k := k0.2.2.2.1 (by omega) w hw; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k0.2.2.2.2 a ha (Or.inr o))
        (by intro w hw; have k := k1.2.2.2.1 (by omega) w hw; rw [e1] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k1.2.2.2.2 a ha (by omega))
        (by intro w hw; have k := k2.2.2.2.1 (by omega) w hw; rw [e2] at k; simpa [capStubPlace, h] using k)
        (by intro a ha o; exact k2.2.2.2.2 a ha (by omega))
      intro k hk w hw
      rw [s4, c.1 k hk w hw, t0mem]
  · intro a ha outside
    rw [final, tailMem,
      k3.2.2.2.2 a ha (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega),
      k2.2.2.2.2 a ha (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega),
      k1.2.2.2.2 a ha (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega),
      k0.2.2.2.2 a ha (by omega), t0mem]

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

set_option maxHeartbeats 8000000 in
theorem cap_open_stub_execute (state : MachineState) (position rootBase cursor : Nat)
    (pc : state.pc = 4648) (index : state.getReg .x20 = BitVec.ofNat 64 position)
    (positionBound : position < 2^24) (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor) (link : state.getReg .x1 = 4264)
    (rootAligned : rootBase % 8 = 0) (cursorAligned : cursor % 8 = 0)
    (separate : rootBase + 2^31 ≤ cursor) (bound : cursor + 128 ≤ MEMORY_BYTES)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (45+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenStubState state) allowCoins
          return result.charge 48 0) := by
  have memory : MEMORY_BYTES ≤ 2^64 := by simp only [MEMORY_BYTES]; omega
  obtain ⟨hx7, hx23, hx30⟩ := cap_stub_head_values state position rootBase index positionBound roots
    (by omega)
  obtain ⟨cell, hcell⟩ : ∃ cell, cell = rootBase + 268435784 + 368*(position/4) := ⟨_, rfl⟩
  rw [← hcell] at hx23
  have cellBound : cell + 128 ≤ cursor := by
    have : 368*(position/4) ≤ 368*(2^22) := Nat.mul_le_mul_left _ (by omega)
    omega
  have cellAligned : cell % 8 = 0 := by omega
  obtain ⟨t0, ht0⟩ : ∃ t, t = capStubHeadState state := ⟨_, rfl⟩
  have t0reg : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x23 → reg ≠ .x30 → t0.getReg reg = state.getReg reg :=
    fun reg a b c d => by rw [ht0]; exact cap_stub_head_register state reg ⟨a, b, c, d⟩
  have t0pc : t0.pc = BitVec.ofNat 64 (4680 + 44*0) := by
    rw [ht0]
    change (capStubHeadPrefix state 8).pc = _
    rw [cap_stub_head_pc state 8 (by decide), pc]; rfl
  have own := Nat.mod_lt position (by decide : 4 > 0)
  obtain ⟨c1, hc1⟩ : ∃ c, c = cursor + (if 0 = position%4 then 0 else 32) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c, c = c1 + (if 1 = position%4 then 0 else 32) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c, c = c2 + (if 2 = position%4 then 0 else 32) := ⟨_, rfl⟩
  have offsets : (position%4 = 0 ∧ c1 = cursor ∧ c2 = cursor+32 ∧ c3 = cursor+64) ∨
      (position%4 = 1 ∧ c1 = cursor+32 ∧ c2 = cursor+32 ∧ c3 = cursor+64) ∨
      (position%4 = 2 ∧ c1 = cursor+32 ∧ c2 = cursor+64 ∧ c3 = cursor+64) ∨
      (position%4 = 3 ∧ c1 = cursor+32 ∧ c2 = cursor+64 ∧ c3 = cursor+96) := by
    subst hc3 hc2 hc1
    rcases (by omega : position%4 = 0 ∨ position%4 = 1 ∨ position%4 = 2 ∨ position%4 = 3)
      with h | h | h | h <;> simp [h]
  have t0x25 : t0.getReg .x25 = BitVec.ofNat 64 cursor :=
    (t0reg .x25 (by decide) (by decide) (by decide) (by decide)).trans pointer
  rw [← ht0] at hx30 hx23
  have k0 := cap_stub_block_any 0 (position%4) cell cursor (by decide) own t0 hx30 hx23 t0x25
    (by omega) (by omega)
  rw [← hc1] at k0
  obtain ⟨t1, ht1⟩ : ∃ t, t = capStubBlockState 0 t0 := ⟨_, rfl⟩
  rw [← ht1] at k0
  have x30at1 : t1.getReg .x30 = BitVec.ofNat 64 (position%4) := (k0.2.2.1 .x30 (by decide) (by decide)).trans hx30
  have x23at1 : t1.getReg .x23 = BitVec.ofNat 64 cell := (k0.2.2.1 .x23 (by decide) (by decide)).trans hx23
  have k1 := cap_stub_block_any 1 (position%4) cell c1 (by decide) own t1 x30at1 x23at1 k0.2.1
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
  rw [← hc2] at k1
  obtain ⟨t2, ht2⟩ : ∃ t, t = capStubBlockState 1 t1 := ⟨_, rfl⟩
  rw [← ht2] at k1
  have x30at2 : t2.getReg .x30 = BitVec.ofNat 64 (position%4) := (k1.2.2.1 .x30 (by decide) (by decide)).trans x30at1
  have x23at2 : t2.getReg .x23 = BitVec.ofNat 64 cell := (k1.2.2.1 .x23 (by decide) (by decide)).trans x23at1
  have k2 := cap_stub_block_any 2 (position%4) cell c2 (by decide) own t2 x30at2 x23at2 k1.2.1
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
  rw [← hc3] at k2
  obtain ⟨t3, ht3⟩ : ∃ t, t = capStubBlockState 2 t2 := ⟨_, rfl⟩
  rw [← ht3] at k2
  have x30at3 : t3.getReg .x30 = BitVec.ofNat 64 (position%4) := (k2.2.2.1 .x30 (by decide) (by decide)).trans x30at2
  have x23at3 : t3.getReg .x23 = BitVec.ofNat 64 cell := (k2.2.2.1 .x23 (by decide) (by decide)).trans x23at2
  have k3 := cap_stub_block_any 3 (position%4) cell c3 (by decide) own t3 x30at3 x23at3 k2.2.1
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
    (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
  obtain ⟨t4, ht4⟩ : ∃ t, t = capStubBlockState 3 t3 := ⟨_, rfl⟩
  rw [← ht4] at k3
  have t4link : t4.getReg .x1 = 4264 :=
    (k3.2.2.1 .x1 (by decide) (by decide)).trans ((k2.2.2.1 .x1 (by decide) (by decide)).trans
      ((k1.2.2.1 .x1 (by decide) (by decide)).trans ((k0.2.2.1 .x1 (by decide) (by decide)).trans
        ((t0reg .x1 (by decide) (by decide) (by decide) (by decide)).trans link))))
  have pcStep (u : Nat) (t : MachineState) (next : MachineState) (equal : next.pc = t.pc + 44)
      (current : t.pc = BitVec.ofNat 64 (4680 + 44*u)) : next.pc = BitVec.ofNat 64 (4680 + 44*(u+1)) := by
    rw [equal, current, show (44 : Word) = BitVec.ofNat 64 44 from rfl, ← BitVec.ofNat_add,
      show 4680 + 44*u + 44 = 4680 + 44*(u+1) by omega]
  have t1pc := pcStep 0 t0 t1 k0.1 t0pc
  have t2pc := pcStep 1 t1 t2 k1.1 t1pc
  have t3pc := pcStep 2 t2 t3 k2.1 t2pc
  have t4pc : t4.pc = 4856 := by rw [pcStep 3 t3 t4 k3.1 t3pc]; rfl
  have source (u : Nat) (small : u < 4) (t : MachineState) (pointer : t.getReg .x23 = BitVec.ofNat 64 cell) :
      t.getReg .x30 ≠ BitVec.ofNat 64 u → ∀ word : Fin 4,
        accessValid (t.getReg .x23 + BitVec.ofNat 64 (32*u + 8*word.val)) 8 = true := by
    intro _ word
    rw [pointer, ← BitVec.ofNat_add]
    exact cap_stub_word_access _ (by omega) (by have := word.isLt; omega)
  have target (t : MachineState) (c : Nat) (pointer : t.getReg .x25 = BitVec.ofNat 64 c)
      (aligned : c % 8 = 0) (room : c + 32 ≤ MEMORY_BYTES) (u : Nat) :
      t.getReg .x30 ≠ BitVec.ofNat 64 u → ∀ word : Fin 4,
        accessValid (t.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true := by
    intro _ word
    rw [pointer, ← BitVec.ofNat_add]
    exact cap_stub_word_access _ (by omega) (by have := word.isLt; omega)
  have run0 := cap_stub_block_execute 0 (by decide) t0 t0pc (source 0 (by decide) t0 hx23)
    (target t0 cursor t0x25 cursorAligned (by omega) 0)
  have run1 := cap_stub_block_execute 1 (by decide) t1 t1pc (source 1 (by decide) t1 x23at1)
    (target t1 c1 k0.2.1
      (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
      (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega) 1)
  have run2 := cap_stub_block_execute 2 (by decide) t2 t2pc (source 2 (by decide) t2 x23at2)
    (target t2 c2 k1.2.1
      (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
      (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega) 2)
  have run3 := cap_stub_block_execute 3 (by decide) t3 t3pc (source 3 (by decide) t3 x23at3)
    (target t3 c3 k2.2.1
      (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega)
      (by rcases offsets with ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ | ⟨_, _, _, _⟩ <;> omega) 3)
  have stepValue (u : Nat) (small : u < 4) (t : MachineState)
      (rest : t.getReg .x30 = BitVec.ofNat 64 (position%4)) :
      capStubBlockSteps u t = if u = position%4 then 2 else 11 := by
    unfold capStubBlockSteps
    rw [rest]
    by_cases same : u = position%4
    · rw [if_pos same, if_pos (by rw [same])]
    · rw [if_neg same, if_neg (cap_stub_word_ne _ _ (by omega) (by omega) (Ne.symm same))]
  have total : capStubBlockSteps 0 t0 + (capStubBlockSteps 1 t1 + (capStubBlockSteps 2 t2 +
      capStubBlockSteps 3 t3)) = 35 := by
    rw [stepValue 0 (by decide) t0 hx30, stepValue 1 (by decide) t1 x30at1,
      stepValue 2 (by decide) t2 x30at2, stepValue 3 (by decide) t3 x30at3]
    rcases (by omega : position%4 = 0 ∨ position%4 = 1 ∨ position%4 = 2 ∨ position%4 = 3)
      with h | h | h | h <;> simp [h]
  have final : capOpenStubState state = capStubTailState t4 := by rw [ht4, ht3, ht2, ht1, ht0]; rfl
  rw [show 45+fuel = 8+(capStubBlockSteps 0 t0+(capStubBlockSteps 1 t1+(capStubBlockSteps 2 t2+
      (capStubBlockSteps 3 t3+(2+fuel))))) by omega,
    cap_stub_head_execute state pc, ← ht0, run0, ← ht1, run1, ← ht2, run2, ← ht3, run3, ← ht4,
    cap_stub_tail_execute t4 t4pc t4link, final]
  simp only [bind_assoc, pure_bind, charge_pair]
  congr 1
  funext result
  congr 2
  omega

end CommitGolfCandidate
