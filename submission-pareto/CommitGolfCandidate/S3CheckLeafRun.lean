import CommitGolfCandidate.CapCheckLeafImage

/-! Execution of the checker leaf on the cap check image: checked
straight-line segments, four place blocks of which the leaf's own place is
skipped, three permutation calls with arbitrary replies, and the return.
174 instructions, 195 cycles, three public queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer

/-! ### Program points -/

/-- At the first ECALL: first window built at 0..200, selectors loaded. -/
def s3LeafFirst (state : MachineState) : MachineState := s3Run s3LeafBuild state

/-- After the first reply was written at address 0. -/
def s3LeafMiddle (state : MachineState) (first : BitVec 1600) : MachineState :=
  s3PermutationAnswer (s3LeafFirst state) first

/-- At the second ECALL: chaining bytes and value tail placed at 56..256. -/
def s3LeafSecond (state : MachineState) (first : BitVec 1600) : MachineState :=
  s3Run s3LeafChain (s3LeafMiddle state first)

/-- After the second reply (the leaf digest in its low 32 bytes) was written at address 0. -/
def s3LeafLast (state : MachineState) (first second : BitVec 1600) : MachineState :=
  s3PermutationAnswer (s3LeafSecond state first) second

/-- At the first place block: the leaf digest copied to its own place. -/
def s6LeafOwned (state : MachineState) (first second : BitVec 1600) : MachineState :=
  s3Run s6LeafOwn (s3Run s6LeafSlot (s3LeafLast state first second))

/-- One place block: skipped after its test when x7 selects it, otherwise it
copies the next record digest. -/
def s6PlaceBlock (place : Nat) (state : MachineState) : MachineState :=
  if state.getReg .x7 = BitVec.ofNat 64 (32 * place) then s3Run (s6PlaceTest place) state
  else s3Run (s6PlaceCopy place) (s3Run (s6PlaceTest place) state)

/-- The first `count` place blocks. -/
def s6PlacesUpTo : Nat → MachineState → MachineState
  | 0, state => state
  | count + 1, state => s6PlaceBlock count (s6PlacesUpTo count state)

/-- Instructions executed by the first `count` place blocks. -/
def s6PlaceSteps (slot : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => s6PlaceSteps slot count + (if count = slot then 2 else 11)

/-- At the third ECALL: 72 zero bytes and the four digests at 56..256. -/
def s6LeafGroup (state : MachineState) (first second : BitVec 1600) : MachineState :=
  s3Run s6LeafClear (s6PlacesUpTo 4 (s6LeafOwned state first second))

/-- After the third reply (the group digest in its low 32 bytes) was written at address 0. -/
def s6LeafReply (state : MachineState) (first second third : BitVec 1600) : MachineState :=
  s3PermutationAnswer (s6LeafGroup state first second) third

/-- At the return instruction: group digest copied to scratch, x20 and x8 advanced. -/
def s3LeafDone (state : MachineState) (first second third : BitVec 1600) : MachineState :=
  s3Run s3LeafFinish (s6LeafReply state first second third)

/-- The leaf routine as an oracle computation over arbitrary replies. -/
def capCheckLeaf (state : MachineState) : OracleComp World MachineState := do
  let first ← s3PermutationQuery (readBuffer (s3LeafFirst state) 0 200)
  let second ← s3PermutationQuery (readBuffer (s3LeafSecond state first) 56 200)
  let third ← s3PermutationQuery (readBuffer (s6LeafGroup state first second) 56 200)
  return s3LeafDone state first second third

/-! ### Arithmetic helpers -/

theorem s6_pc_advance (address : Word) (index count : Nat)
    (pc : address = BitVec.ofNat 64 (4096 + 4 * index)) :
    address + BitVec.ofNat 64 (4 * count) = BitVec.ofNat 64 (4096 + 4 * (index + count)) := by
  rw [pc, ← BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 64) (by omega)

theorem s6_check_pc_next (address : Word) (index : Nat)
    (pc : address = BitVec.ofNat 64 (4096 + 4 * index)) :
    address + 4 = BitVec.ofNat 64 (4096 + 4 * (index + 1)) :=
  s6_pc_advance address index 1 pc

theorem s6_slot_word_eq (left right : Nat) (leftSmall : left < 4) (rightSmall : right < 4) :
    BitVec.ofNat 64 (32 * left) = BitVec.ofNat 64 (32 * right) ↔ left = right := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at numeric
    omega
  · rintro rfl
    rfl

theorem s6_place_immediate (place : Nat) (small : place < 4) :
    signExtend12 (BitVec.ofNat 12 (32 * place)) = BitVec.ofNat 64 (32 * place) := by
  interval_cases place <;> rfl

/-- A low aligned word lies in memory. -/
theorem s6_low_access (address : Nat) (small : address + 8 ≤ 2 ^ 36) (aligned : address % 8 = 0) :
    accessValid (BitVec.ofNat 64 address) 8 = true := by
  have memory : MEMORY_BYTES = 2 ^ 36 := rfl
  have numeric : (BitVec.ofNat 64 address).toNat = address := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq, numeric, memory]
  exact ⟨small, aligned⟩

/-- The leaf's place in its group: the position modulo 4. -/
def s6SlotOf (state : MachineState) : Nat := (state.getReg .x20).toNat % 4

theorem s6_slot_small (state : MachineState) : s6SlotOf state < 4 := Nat.mod_lt _ (by decide)

theorem s3_store_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

def s3CopyStep (base : Reg) (pair : Nat × Nat) (state : MachineState) : MachineState :=
  execInstrBr (execInstrBr state (.LD .x6 base (BitVec.ofNat 12 pair.1)))
    (.SD .x0 .x6 (BitVec.ofNat 12 pair.2))

theorem s3_copy_cons (base : Reg) (pair : Nat × Nat) (rest : List (Nat × Nat))
    (state : MachineState) :
    s3Run (s3Copy base (pair :: rest)) state =
      s3Run (s3Copy base rest) (s3CopyStep base pair state) := rfl

theorem s3_copy_step_register (base : Reg) (pair : Nat × Nat) (state : MachineState)
    (reg : Reg) (outside : reg ≠ .x6) :
    (s3CopyStep base pair state).getReg reg = state.getReg reg := by
  simp only [s3CopyStep, execInstrBr, MachineState.getReg_setPC, s3_store_register,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem s3_copy_register (base : Reg) (pairs : List (Nat × Nat)) (state : MachineState)
    (reg : Reg) (outside : reg ≠ .x6) :
    (s3Run (s3Copy base pairs) state).getReg reg = state.getReg reg := by
  induction pairs generalizing state with
  | nil => rfl
  | cons pair rest ih => rw [s3_copy_cons, ih, s3_copy_step_register _ _ _ _ outside]

/-! ### Registers through the segments -/

theorem s3_run_register_frame (instructions : List Instr) (window : Reg) (words : Nat)
    (intact : Bool) (state : MachineState) (reg : Reg)
    (checked : s3Checked window words intact instructions = true)
    (targets : List Reg)
    (written : ∀ target ∈ instructions.filterMap s3Target, target ∈ targets)
    (outside : reg ∉ targets) :
    (s3Run instructions state).getReg reg = state.getReg reg :=
  s3_run_register instructions window words intact state reg checked (fun instruction inside equal =>
    outside (written reg (List.mem_filterMap.mpr ⟨instruction, inside, equal⟩)))

theorem s3_leaf_first_register (state : MachineState) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x5, .x10, .x11, .x12, .x13]) :
    (s3LeafFirst state).getReg reg = state.getReg reg :=
  s3_run_register_frame s3LeafBuild .x8 32 true state reg s3_leaf_build_checked _ (by decide)
    outside

theorem s3_leaf_first_selectors (state : MachineState) :
    (s3LeafFirst state).getReg .x5 = 0 ∧ (s3LeafFirst state).getReg .x10 = 0 ∧
    (s3LeafFirst state).getReg .x11 = 200 ∧ (s3LeafFirst state).getReg .x12 = 0 ∧
    (s3LeafFirst state).getReg .x13 = 1 := by
  unfold s3LeafFirst s3LeafBuild
  rw [s3_run_append]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem s3_leaf_first_pc (state : MachineState) (pc : state.pc = 5124) :
    (s3LeafFirst state).pc = BitVec.ofNat 64 (4096 + 4 * 312) := by
  rw [s3LeafFirst, s3_run_pc _ .x8 32 true _ s3_leaf_build_checked, pc, s3_leaf_build_length]
  rfl

theorem s3_leaf_middle_register (state : MachineState) (first : BitVec 1600) (reg : Reg) :
    (s3LeafMiddle state first).getReg reg = (s3LeafFirst state).getReg reg :=
  s3_permutation_register _ first reg

theorem s3_leaf_second_register (state : MachineState) (first : BitVec 1600) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x10]) :
    (s3LeafSecond state first).getReg reg = (s3LeafFirst state).getReg reg :=
  (s3_run_register_frame s3LeafChain .x8 32 true _ reg s3_leaf_chain_checked _ (by decide)
    outside).trans (s3_leaf_middle_register state first reg)

theorem s3_leaf_second_input (state : MachineState) (first : BitVec 1600) :
    (s3LeafSecond state first).getReg .x10 = 56 := by
  unfold s3LeafSecond s3LeafChain
  rw [s3_run_append]
  rfl

theorem s3_leaf_last_register (state : MachineState) (first second : BitVec 1600) (reg : Reg) :
    (s3LeafLast state first second).getReg reg = (s3LeafSecond state first).getReg reg :=
  s3_permutation_register _ second reg

/-- x7 after the slot words: 32 times the position modulo 4. -/
theorem s6_leaf_slot_value (state : MachineState) :
    (s3Run s6LeafSlot state).getReg .x7 = BitVec.ofNat 64 (32 * s6SlotOf state) := by
  have value : (s3Run s6LeafSlot state).getReg .x7 =
      (state.getReg .x20 &&& BitVec.ofNat 64 3) <<< 5 := rfl
  rw [value]
  apply BitVec.eq_of_toNat_eq
  have masked : (state.getReg .x20 &&& BitVec.ofNat 64 3).toNat =
      (state.getReg .x20).toNat % 2 ^ 2 := by
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 3).toNat = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_shiftLeft, masked, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  unfold s6SlotOf
  omega

theorem s6_leaf_slot_register (state : MachineState) (reg : Reg) (outside : reg ≠ .x7) :
    (s3Run s6LeafSlot state).getReg reg = state.getReg reg :=
  s3_run_register_frame s6LeafSlot .x7 20 false state reg s6_leaf_slot_checked [Reg.x7]
    (by decide) (by simpa using outside)

theorem s6_leaf_own_register (state : MachineState) (reg : Reg) (outside : reg ≠ .x6) :
    (s3Run s6LeafOwn state).getReg reg = state.getReg reg :=
  s3_run_register_frame s6LeafOwn .x7 20 true state reg s6_leaf_own_checked [Reg.x6]
    (by decide) (by simpa using outside)

/-! ### Place blocks -/

theorem s6_place_test_x6 (state : MachineState) (place : Nat) (small : place < 4) :
    (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).getReg .x6 =
      BitVec.ofNat 64 (32 * place) := by
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), s6_place_immediate place small]
  exact BitVec.zero_add _

theorem s6_place_test_eq (state : MachineState) (place : Nat) :
    s3Run (s6PlaceTest place) state =
      execInstrBr (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place))))
        (.BEQ .x6 .x7 40) := rfl

theorem s6_place_test_register (state : MachineState) (place : Nat) (reg : Reg)
    (outside : reg ≠ .x6) :
    (s3Run (s6PlaceTest place) state).getReg reg = state.getReg reg := by
  rw [s6_place_test_eq, s3_branch_register]
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem s6_place_test_mem (state : MachineState) (place : Nat) :
    (s3Run (s6PlaceTest place) state).mem = state.mem := by
  rw [s6_place_test_eq, s3_branch_mem]
  rfl

theorem s6_place_test_pc (state : MachineState) (place slot : Nat) (placeSmall : place < 4)
    (slotSmall : slot < 4) (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot)) :
    (s3Run (s6PlaceTest place) state).pc =
      if place = slot then state.pc + 44 else state.pc + 8 := by
  rw [s6_place_test_eq]
  have tested := s6_place_test_x6 state place placeSmall
  have kept : (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).getReg .x7 =
      BitVec.ofNat 64 (32 * slot) := by
    simp only [execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x7)]
    exact x7
  have stepped : (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).pc =
      state.pc + 4 := rfl
  by_cases same : place = slot
  · have equal : (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).getReg .x6 =
        (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).getReg .x7 := by
      rw [tested, kept, same]
    rw [if_pos same, s3_branch_taken _ _ _ _ equal, stepped, BitVec.add_assoc]
    rfl
  · have different :
        (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).getReg .x6 ≠
        (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).getReg .x7 := by
      rw [tested, kept]
      exact fun equal => same ((s6_slot_word_eq place slot placeSmall slotSmall).mp equal)
    rw [if_neg same, s3_branch_fall _ _ _ _ different, stepped, BitVec.add_assoc]
    rfl

theorem s6_place_copy_register (state : MachineState) (place : Nat) (small : place < 4)
    (reg : Reg) (outside : reg ∉ [Reg.x6, .x25]) :
    (s3Run (s6PlaceCopy place) state).getReg reg = state.getReg reg :=
  s3_run_register_frame (s6PlaceCopy place) .x25 4 true state reg
    (s6_place_copy_checked place small) [Reg.x6, .x25]
    (by interval_cases place <;> decide) outside

theorem s6_place_copy_cursor (state : MachineState) (place : Nat) :
    (s3Run (s6PlaceCopy place) state).getReg .x25 = state.getReg .x25 + 32 := by
  unfold s6PlaceCopy
  rw [s3_run_append]
  change (s3Run (s3Copy .x25 (s6PlacePairs place)) state).getReg .x25 + signExtend12 32 = _
  rw [s3_copy_register .x25 _ state .x25 (by decide)]
  rfl

theorem s6_place_copy_pc (state : MachineState) (place : Nat) (small : place < 4) :
    (s3Run (s6PlaceCopy place) state).pc = state.pc + 36 := by
  rw [s3_run_pc _ .x25 4 true _ (s6_place_copy_checked place small), s6_place_copy_length]
  rfl

theorem s6_place_block_taken (state : MachineState) (place slot : Nat)
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot)) (same : place = slot) :
    s6PlaceBlock place state = s3Run (s6PlaceTest place) state := by
  unfold s6PlaceBlock
  rw [if_pos (show state.getReg .x7 = BitVec.ofNat 64 (32 * place) by rw [x7, same])]

theorem s6_place_block_fall (state : MachineState) (place slot : Nat) (placeSmall : place < 4)
    (slotSmall : slot < 4) (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot))
    (same : place ≠ slot) :
    s6PlaceBlock place state = s3Run (s6PlaceCopy place) (s3Run (s6PlaceTest place) state) := by
  unfold s6PlaceBlock
  rw [if_neg (show ¬ state.getReg .x7 = BitVec.ofNat 64 (32 * place) by
    rw [x7]
    exact fun equal => same ((s6_slot_word_eq slot place slotSmall placeSmall).mp equal).symm)]

theorem s6_place_block_register (state : MachineState) (place : Nat) (small : place < 4)
    (reg : Reg) (outside : reg ∉ [Reg.x6, .x25]) :
    (s6PlaceBlock place state).getReg reg = state.getReg reg := by
  have notSix : reg ≠ .x6 := fun equal => outside (by simp [equal])
  unfold s6PlaceBlock
  split
  · exact s6_place_test_register state place reg notSix
  · rw [s6_place_copy_register _ place small reg outside,
      s6_place_test_register state place reg notSix]

theorem s6_place_block_cursor (state : MachineState) (place slot : Nat) (placeSmall : place < 4)
    (slotSmall : slot < 4) (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot)) :
    (s6PlaceBlock place state).getReg .x25 =
      if place = slot then state.getReg .x25 else state.getReg .x25 + 32 := by
  by_cases same : place = slot
  · rw [if_pos same, s6_place_block_taken state place slot x7 same,
      s6_place_test_register state place .x25 (by decide)]
  · rw [if_neg same, s6_place_block_fall state place slot placeSmall slotSmall x7 same,
      s6_place_copy_cursor, s6_place_test_register state place .x25 (by decide)]

theorem s6_place_block_pc (state : MachineState) (place slot : Nat) (placeSmall : place < 4)
    (slotSmall : slot < 4) (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot)) :
    (s6PlaceBlock place state).pc = state.pc + 44 := by
  have tested := s6_place_test_pc state place slot placeSmall slotSmall x7
  by_cases same : place = slot
  · rw [s6_place_block_taken state place slot x7 same, tested, if_pos same]
  · rw [s6_place_block_fall state place slot placeSmall slotSmall x7 same,
      s6_place_copy_pc _ place placeSmall, tested, if_neg same, BitVec.add_assoc]
    rfl

/-- One place block: two instructions when it is the leaf's own place, eleven otherwise. -/
theorem s6_place_block_execute (state : MachineState) (place slot : Nat) (placeSmall : place < 4)
    (slotSmall : slot < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (375 + 11 * place)))
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot))
    (copyValid : place ≠ slot → ∀ word < 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) ((if place = slot then 2 else 11) + fuel)
        state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (s6PlaceBlock place state) allowCoins
          return result.charge (if place = slot then 2 else 11) 0) := by
  have addi (rest : Nat) : execute ((capExperimental 24).image .check) (1 + rest) state
      allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))) allowCoins
          return result.charge 1 0) :=
    s3_run_execute ((capExperimental 24).image .check)
      [.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place))] .x8 32 (by decide) false
      (375 + 11 * place) state rest allowCoins pc
      (by simp only [List.length_cons, List.length_nil]; omega)
      (fun i inside => by
        have zero : i = 0 := by simpa using inside
        subst zero
        exact s6_place_addi_decoded place placeSmall)
      rfl (fun impossible => by cases impossible)
  have testedPC : (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).pc =
      BitVec.ofNat 64 (4096 + 4 * (376 + 11 * place)) := by
    rw [show (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))).pc =
      state.pc + 4 from rfl, s6_check_pc_next _ _ pc]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have branch (rest : Nat) : execute ((capExperimental 24).image .check) (1 + rest)
      (execInstrBr state (.ADDI .x6 .x0 (BitVec.ofNat 12 (32 * place)))) allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (s3Run (s6PlaceTest place) state) allowCoins
          return result.charge 1 0) :=
    s3_branch_execute _ _ (376 + 11 * place) .x6 .x7 40 rest allowCoins testedPC
      (by omega) (s6_place_branch_decoded place placeSmall)
  by_cases same : place = slot
  · rw [if_pos same, show 2 + fuel = 1 + (1 + fuel) by omega, addi,
      s6_place_block_taken state place slot x7 same]
    simp only [branch, bind_assoc, pure_bind]
    simp [Execution.charge, ← Nat.add_assoc]
  · have branchedPC : (s3Run (s6PlaceTest place) state).pc =
        BitVec.ofNat 64 (4096 + 4 * (377 + 11 * place)) := by
      have fell := s6_place_test_pc state place slot placeSmall slotSmall x7
      rw [if_neg same] at fell
      rw [fell, show (8 : Word) = BitVec.ofNat 64 (4 * 2) from rfl, s6_pc_advance _ _ 2 pc]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have copy := s3_run_execute ((capExperimental 24).image .check) (s6PlaceCopy place) .x25 4
      (by decide) true (377 + 11 * place) (s3Run (s6PlaceTest place) state) fuel allowCoins
      branchedPC (by rw [s6_place_copy_length]; omega) (s6_place_copy_decoded place placeSmall)
      (s6_place_copy_checked place placeSmall)
      (fun _ => by rw [s6_place_test_register state place .x25 (by decide)]; exact copyValid same)
    rw [s6_place_copy_length] at copy
    rw [if_neg same, show 11 + fuel = 1 + (1 + (9 + fuel)) by omega, addi,
      s6_place_block_fall state place slot placeSmall slotSmall x7 same]
    simp only [branch, copy, bind_assoc, pure_bind]
    simp [Execution.charge, ← Nat.add_assoc]

theorem s6_places_register (state : MachineState) (count : Nat) (few : count ≤ 4) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x25]) :
    (s6PlacesUpTo count state).getReg reg = state.getReg reg := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (s6PlaceBlock count (s6PlacesUpTo count state)).getReg reg = _
    rw [s6_place_block_register _ count (by omega) reg outside, ih (by omega)]

theorem s6_places_x7 (state : MachineState) (count : Nat) (few : count ≤ 4) :
    (s6PlacesUpTo count state).getReg .x7 = state.getReg .x7 :=
  s6_places_register state count few .x7 (by decide)

theorem s6_places_pc (state : MachineState) (slot : Nat) (slotSmall : slot < 4)
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot))
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 375)) (count : Nat) (few : count ≤ 4) :
    (s6PlacesUpTo count state).pc = BitVec.ofNat 64 (4096 + 4 * (375 + 11 * count)) := by
  induction count with
  | zero => exact pc
  | succ count ih =>
    change (s6PlaceBlock count (s6PlacesUpTo count state)).pc = _
    rw [s6_place_block_pc _ count slot (by omega) slotSmall
        ((s6_places_x7 state count (by omega)).trans x7),
      show (44 : Word) = BitVec.ofNat 64 (4 * 11) from rfl,
      s6_pc_advance _ _ 11 (ih (by omega)),
      show 375 + 11 * count + 11 = 375 + 11 * (count + 1) by omega]

/-- The record cursor after `count` blocks: one digest per copied place. -/
theorem s6_places_cursor (state : MachineState) (slot : Nat) (slotSmall : slot < 4)
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot)) (count : Nat) (few : count ≤ 4) :
    (s6PlacesUpTo count state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (32 * (count - if slot < count then 1 else 0)) := by
  induction count with
  | zero => simp [s6PlacesUpTo]
  | succ count ih =>
    change (s6PlaceBlock count (s6PlacesUpTo count state)).getReg .x25 = _
    rw [s6_place_block_cursor _ count slot (by omega) slotSmall
        ((s6_places_x7 state count (by omega)).trans x7), ih (by omega)]
    by_cases same : count = slot
    · rw [if_pos same, if_neg (show ¬ slot < count by omega),
        if_pos (show slot < count + 1 by omega),
        show count - 0 = count + 1 - 1 by omega]
    · rw [if_neg same, BitVec.add_assoc, show (32 : Word) = BitVec.ofNat 64 32 from rfl,
        ← BitVec.ofNat_add]
      by_cases below : slot < count
      · rw [if_pos below, if_pos (show slot < count + 1 by omega),
          show 32 * (count - 1) + 32 = 32 * (count + 1 - 1) by omega]
      · rw [if_neg below, if_neg (show ¬ slot < count + 1 by omega),
          show 32 * (count - 0) + 32 = 32 * (count + 1 - 0) by omega]

theorem s6_place_steps_four (slot : Nat) (small : slot < 4) : s6PlaceSteps slot 4 = 35 := by
  interval_cases slot <;> rfl

theorem s6_place_steps_succ (slot count : Nat) :
    s6PlaceSteps slot (count + 1) = s6PlaceSteps slot count + (if count = slot then 2 else 11) :=
  rfl

/-- The first `count` place blocks from word 375. -/
theorem s6_places_execute (state : MachineState) (slot : Nat) (slotSmall : slot < 4)
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot))
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 375))
    (groupValid : ∀ word < 12,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (allowCoins : Bool) (count : Nat) (few : count ≤ 4) (fuel : Nat) :
    execute ((capExperimental 24).image .check) (s6PlaceSteps slot count + fuel) state
        allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (s6PlacesUpTo count state) allowCoins
          return result.charge (s6PlaceSteps slot count) 0) := by
  induction count generalizing fuel with
  | zero => simp [s6PlaceSteps, s6PlacesUpTo, Execution.charge]
  | succ count ih =>
    have block := s6_place_block_execute (s6PlacesUpTo count state) count slot (by omega)
      slotSmall (s6_places_pc state slot slotSmall x7 pc count (by omega))
      ((s6_places_x7 state count (by omega)).trans x7)
      (fun different word small => by
        rw [s6_places_cursor state slot slotSmall x7 count (by omega), BitVec.add_assoc,
          ← BitVec.ofNat_add,
          show 32 * (count - (if slot < count then 1 else 0)) + 8 * word =
            8 * (4 * (count - (if slot < count then 1 else 0)) + word) by omega]
        apply groupValid
        split <;> omega) fuel allowCoins
    have previous := ih (by omega) ((if count = slot then 2 else 11) + fuel)
    rw [s6_place_steps_succ, Nat.add_assoc, previous, block,
      show s6PlacesUpTo (count + 1) state = s6PlaceBlock count (s6PlacesUpTo count state) from rfl]
    simp only [bind_assoc, pure_bind]
    simp [Execution.charge, Nat.add_assoc]

theorem s6_places_steps_execute (state : MachineState) (slot : Nat) (slotSmall : slot < 4)
    (x7 : state.getReg .x7 = BitVec.ofNat 64 (32 * slot))
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 375))
    (groupValid : ∀ word < 12,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (35 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (s6PlacesUpTo 4 state) allowCoins
          return result.charge 35 0) := by
  have run := s6_places_execute state slot slotSmall x7 pc groupValid allowCoins 4 (by decide)
    fuel
  rw [s6_place_steps_four slot slotSmall] at run
  exact run

/-! ### Registers at the end -/

theorem s6_leaf_owned_register (state : MachineState) (first second : BitVec 1600) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x7, .x10]) :
    (s6LeafOwned state first second).getReg reg = (s3LeafFirst state).getReg reg := by
  have notSix : reg ≠ .x6 := fun equal => outside (by simp [equal])
  have notSeven : reg ≠ .x7 := fun equal => outside (by simp [equal])
  rw [s6LeafOwned, s6_leaf_own_register _ reg notSix, s6_leaf_slot_register _ reg notSeven,
    s3_leaf_last_register, s3_leaf_second_register state first reg (by simp_all)]

theorem s6_leaf_group_register (state : MachineState) (first second : BitVec 1600) (reg : Reg)
    (outside : reg ∉ [Reg.x6, .x7, .x10, .x25]) :
    (s6LeafGroup state first second).getReg reg = (s3LeafFirst state).getReg reg := by
  rw [s6LeafGroup, s3_run_register_frame s6LeafClear .x8 32 false _ reg s6_leaf_clear_checked []
      (by decide) (by simp), s6_places_register _ 4 (by decide) reg (by simp_all),
    s6_leaf_owned_register state first second reg (by simp_all)]

theorem s6_leaf_group_input (state : MachineState) (first second : BitVec 1600) :
    (s6LeafGroup state first second).getReg .x10 = 56 := by
  rw [s6LeafGroup, s3_run_register_frame s6LeafClear .x8 32 false _ .x10 s6_leaf_clear_checked []
      (by decide) (by simp), s6_places_register _ 4 (by decide) .x10 (by decide), s6LeafOwned,
    s6_leaf_own_register _ .x10 (by decide), s6_leaf_slot_register _ .x10 (by decide),
    s3_leaf_last_register, s3_leaf_second_input]

theorem s6_leaf_owned_x7 (state : MachineState) (first second : BitVec 1600) :
    (s6LeafOwned state first second).getReg .x7 =
      BitVec.ofNat 64 (32 * s6SlotOf (s3LeafLast state first second)) := by
  rw [s6LeafOwned, s6_leaf_own_register _ .x7 (by decide), s6_leaf_slot_value]

theorem s3_leaf_done_register (state : MachineState) (first second third : BitVec 1600)
    (reg : Reg)
    (outside : reg ∉ [Reg.x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x20, .x25]) :
    (s3LeafDone state first second third).getReg reg = state.getReg reg := by
  rw [s3LeafDone, s3_run_register_frame s3LeafFinish .x8 32 false _ reg s3_leaf_finish_checked
      [Reg.x6, .x20, .x8] (by decide) (by simp_all), s6LeafReply, s3_permutation_register,
    s6_leaf_group_register state first second reg (by simp_all),
    s3_leaf_first_register state reg (by simp_all)]

theorem s3_leaf_done_source (state : MachineState) (first second third : BitVec 1600) :
    (s3LeafDone state first second third).getReg .x8 = state.getReg .x8 + 256 := by
  have advanced : (s3LeafDone state first second third).getReg .x8 =
      (s3Run (s3Copy .x0 s3OutputPairs ++ [.SRLI .x20 .x20 2])
        (s6LeafReply state first second third)).getReg .x8 + 256 := by
    unfold s3LeafDone s3LeafFinish
    rw [show s3Copy .x0 s3OutputPairs ++ [Instr.SRLI .x20 .x20 2, .ADDI .x8 .x8 256] =
      (s3Copy .x0 s3OutputPairs ++ [.SRLI .x20 .x20 2]) ++ [.ADDI .x8 .x8 256] by simp,
      s3_run_append]
    rfl
  rw [advanced, s3_run_append, show ∀ current : MachineState,
      (s3Run [Instr.SRLI .x20 .x20 2] current).getReg .x8 = current.getReg .x8 from
      fun current => s3_plain_register current (.SRLI .x20 .x20 2) .x8 rfl (by decide),
    s3_copy_register .x0 _ _ .x8 (by decide), s6LeafReply,
    s3_permutation_register, s6_leaf_group_register state first second .x8 (by decide),
    s3_leaf_first_register state .x8 (by decide)]

theorem s3_leaf_done_index (state : MachineState) (first second third : BitVec 1600) :
    (s3LeafDone state first second third).getReg .x20 = state.getReg .x20 >>> 2 := by
  have shifted : (s3LeafDone state first second third).getReg .x20 =
      (s3Run (s3Copy .x0 s3OutputPairs) (s6LeafReply state first second third)).getReg .x20 >>>
        2 := by
    unfold s3LeafDone s3LeafFinish
    rw [s3_run_append]
    rfl
  rw [shifted, s3_copy_register .x0 _ _ .x20 (by decide), s6LeafReply, s3_permutation_register,
    s6_leaf_group_register state first second .x20 (by decide),
    s3_leaf_first_register state .x20 (by decide)]

theorem s3_leaf_done_cursor (state : MachineState) (first second third : BitVec 1600) :
    (s3LeafDone state first second third).getReg .x25 = state.getReg .x25 + 96 := by
  rw [s3LeafDone, s3_run_register_frame s3LeafFinish .x8 32 false _ .x25 s3_leaf_finish_checked
      [Reg.x6, .x20, .x8] (by decide) (by decide), s6LeafReply, s3_permutation_register,
    s6LeafGroup, s3_run_register_frame s6LeafClear .x8 32 false _ .x25 s6_leaf_clear_checked []
      (by decide) (by simp),
    s6_places_cursor _ _ (s6_slot_small _) (s6_leaf_owned_x7 state first second) 4 (by decide),
    if_pos (s6_slot_small _), s6LeafOwned, s6_leaf_own_register _ .x25 (by decide),
    s6_leaf_slot_register _ .x25 (by decide), s3_leaf_last_register,
    s3_leaf_second_register state first .x25 (by decide),
    s3_leaf_first_register state .x25 (by decide)]
  rfl

/-! ### The whole routine -/

theorem s3_leaf_return_execute (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 439))
    (link : state.getReg .x1 = 4256) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (1 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (state.setPC 4256) allowCoins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) =
      some (state.setPC 4256) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
    (s3_leaf_return_fetched state pc) stepped]
  rfl

/-- The complete routine from its entry at word 257: 174 instructions, 195
cycles and three permutation calls, for arbitrary replies. -/
theorem cap_check_leaf_execute (state : MachineState) (pc : state.pc = 5124)
    (link : state.getReg .x1 = 4256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (groupValid : ∀ word < 12,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (174 + fuel) state allowCoins =
      (do let finished ← capCheckLeaf state
          let result ← execute ((capExperimental 24).image .check) fuel
            (finished.setPC 4256) allowCoins
          return result.charge 195 3) := by
  have ready := s3_leaf_first_selectors state
  have firstPC := s3_leaf_first_pc state pc
  -- words 257..311
  have build (rest : Nat) : execute ((capExperimental 24).image .check) (55 + rest) state
      allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest (s3LeafFirst state)
            allowCoins
          return result.charge 55 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s3LeafBuild .x8 32
      (by decide) true 257 state rest allowCoins pc (by decide) s3_leaf_build_decoded
      s3_leaf_build_checked (fun _ => sourceValid)
    rw [s3_leaf_build_length] at run
    exact run
  -- word 312
  have call (rest : Nat) : execute ((capExperimental 24).image .check) (1 + rest)
      (s3LeafFirst state) allowCoins =
      (do let first ← s3PermutationQuery (readBuffer (s3LeafFirst state) 0 200)
          let result ← execute ((capExperimental 24).image .check) rest
            (s3LeafMiddle state first) allowCoins
          return result.charge 8 1) := by
    have raw := s3_permutation_execute ((capExperimental 24).image .check) (s3LeafFirst state)
      (s3_leaf_call_fetched _ (Or.inl firstPC)) ⟨ready.1, ready.2.2.1, ready.2.2.2.2⟩
      (by rw [ready.2.1]; decide) (by rw [ready.2.2.2.1]; decide)
      (by rw [ready.2.1]; decide) (by rw [ready.2.2.2.1]; decide) rest allowCoins
    rw [show ((s3LeafFirst state).getReg .x10).toNat = 0 by rw [ready.2.1]; rfl] at raw
    exact raw
  have middlePC (first : BitVec 1600) :
      (s3LeafMiddle state first).pc = BitVec.ofNat 64 (4096 + 4 * 313) := by
    rw [s3LeafMiddle, s3_permutation_pc, firstPC]
    rfl
  have middleSource (first : BitVec 1600) : ∀ word < 32,
      accessValid ((s3LeafMiddle state first).getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 =
        true := by
    rw [s3_leaf_middle_register, s3_leaf_first_register state .x8 (by decide)]
    exact sourceValid
  -- words 313..363
  have chain (first : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (51 + rest) (s3LeafMiddle state first)
        allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (s3LeafSecond state first) allowCoins
          return result.charge 51 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s3LeafChain .x8 32
      (by decide) true 313 (s3LeafMiddle state first) rest allowCoins (middlePC first)
      (by decide) s3_leaf_chain_decoded s3_leaf_chain_checked (fun _ => middleSource first)
    rw [s3_leaf_chain_length] at run
    exact run
  have secondPC (first : BitVec 1600) :
      (s3LeafSecond state first).pc = BitVec.ofNat 64 (4096 + 4 * 364) := by
    rw [s3LeafSecond, s3_run_pc _ .x8 32 true _ s3_leaf_chain_checked, middlePC,
      s3_leaf_chain_length]
    rfl
  have secondInput := s3_leaf_second_input state
  have secondOutput (first : BitVec 1600) : (s3LeafSecond state first).getReg .x12 = 0 :=
    (s3_leaf_second_register state first .x12 (by decide)).trans ready.2.2.2.1
  -- word 364
  have call2 (first : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (1 + rest) (s3LeafSecond state first)
        allowCoins =
      (do let second ← s3PermutationQuery (readBuffer (s3LeafSecond state first) 56 200)
          let result ← execute ((capExperimental 24).image .check) rest
            (s3LeafLast state first second) allowCoins
          return result.charge 8 1) := by
    have raw := s3_permutation_execute ((capExperimental 24).image .check)
      (s3LeafSecond state first) (s3_leaf_call_fetched _ (Or.inr (Or.inl (secondPC first))))
      ⟨(s3_leaf_second_register state first .x5 (by decide)).trans ready.1,
        (s3_leaf_second_register state first .x11 (by decide)).trans ready.2.2.1,
        (s3_leaf_second_register state first .x13 (by decide)).trans ready.2.2.2.2⟩
      (by rw [secondInput]; decide) (by rw [secondOutput]; decide)
      (by rw [secondInput]; decide) (by rw [secondOutput]; decide) rest allowCoins
    rw [show ((s3LeafSecond state first).getReg .x10).toNat = 56 by
      rw [secondInput]; rfl] at raw
    exact raw
  have lastPC (first second : BitVec 1600) :
      (s3LeafLast state first second).pc = BitVec.ofNat 64 (4096 + 4 * 365) := by
    rw [s3LeafLast, s3_permutation_pc, secondPC]
    rfl
  -- words 365..366
  have slot (first second : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (2 + rest) (s3LeafLast state first second)
        allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (s3Run s6LeafSlot (s3LeafLast state first second)) allowCoins
          return result.charge 2 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s6LeafSlot .x7 20
      (by decide) false 365 (s3LeafLast state first second) rest allowCoins
      (lastPC first second) (by decide) s6_leaf_slot_decoded s6_leaf_slot_checked
      (fun impossible => by cases impossible)
    rw [s6_leaf_slot_length] at run
    exact run
  have slotPC (first second : BitVec 1600) :
      (s3Run s6LeafSlot (s3LeafLast state first second)).pc =
        BitVec.ofNat 64 (4096 + 4 * 367) := by
    rw [s3_run_pc _ .x7 20 false _ s6_leaf_slot_checked, lastPC, s6_leaf_slot_length]
    rfl
  -- words 367..374
  have own (first second : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (8 + rest)
        (s3Run s6LeafSlot (s3LeafLast state first second)) allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (s6LeafOwned state first second) allowCoins
          return result.charge 8 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s6LeafOwn .x7 20
      (by decide) true 367 (s3Run s6LeafSlot (s3LeafLast state first second)) rest allowCoins
      (slotPC first second) (by decide) s6_leaf_own_decoded s6_leaf_own_checked
      (fun _ word small => by
        rw [s6_leaf_slot_value, ← BitVec.ofNat_add]
        have := s6_slot_small (s3LeafLast state first second)
        exact s6_low_access _ (by omega) (by omega))
    rw [s6_leaf_own_length] at run
    exact run
  have ownedPC (first second : BitVec 1600) :
      (s6LeafOwned state first second).pc = BitVec.ofNat 64 (4096 + 4 * 375) := by
    rw [s6LeafOwned, s3_run_pc _ .x7 20 true _ s6_leaf_own_checked, slotPC, s6_leaf_own_length]
    rfl
  have ownedCursor (first second : BitVec 1600) :
      (s6LeafOwned state first second).getReg .x25 = state.getReg .x25 := by
    rw [s6_leaf_owned_register state first second .x25 (by decide),
      s3_leaf_first_register state .x25 (by decide)]
  -- words 375..418
  have places (first second : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (35 + rest) (s6LeafOwned state first second)
        allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (s6PlacesUpTo 4 (s6LeafOwned state first second)) allowCoins
          return result.charge 35 0) :=
    s6_places_steps_execute _ _ (s6_slot_small (s3LeafLast state first second))
      (s6_leaf_owned_x7 state first second) (ownedPC first second)
      (by rw [ownedCursor]; exact groupValid) rest allowCoins
  have placedPC (first second : BitVec 1600) :
      (s6PlacesUpTo 4 (s6LeafOwned state first second)).pc =
        BitVec.ofNat 64 (4096 + 4 * 419) :=
    s6_places_pc _ _ (s6_slot_small (s3LeafLast state first second))
      (s6_leaf_owned_x7 state first second) (ownedPC first second) 4 (by decide)
  -- words 419..427
  have clear (first second : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (9 + rest)
        (s6PlacesUpTo 4 (s6LeafOwned state first second)) allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (s6LeafGroup state first second) allowCoins
          return result.charge 9 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s6LeafClear .x8 32
      (by decide) false 419 (s6PlacesUpTo 4 (s6LeafOwned state first second)) rest allowCoins
      (placedPC first second) (by decide) s6_leaf_clear_decoded s6_leaf_clear_checked
      (fun impossible => by cases impossible)
    rw [s6_leaf_clear_length] at run
    exact run
  have groupPC (first second : BitVec 1600) :
      (s6LeafGroup state first second).pc = BitVec.ofNat 64 (4096 + 4 * 428) := by
    rw [s6LeafGroup, s3_run_pc _ .x8 32 false _ s6_leaf_clear_checked, placedPC,
      s6_leaf_clear_length]
    rfl
  have groupInput := s6_leaf_group_input state
  have groupOutput (first second : BitVec 1600) :
      (s6LeafGroup state first second).getReg .x12 = 0 :=
    (s6_leaf_group_register state first second .x12 (by decide)).trans ready.2.2.2.1
  -- word 428
  have call3 (first second : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (1 + rest) (s6LeafGroup state first second)
        allowCoins =
      (do let third ← s3PermutationQuery (readBuffer (s6LeafGroup state first second) 56 200)
          let result ← execute ((capExperimental 24).image .check) rest
            (s6LeafReply state first second third) allowCoins
          return result.charge 8 1) := by
    have raw := s3_permutation_execute ((capExperimental 24).image .check)
      (s6LeafGroup state first second)
      (s3_leaf_call_fetched _ (Or.inr (Or.inr (groupPC first second))))
      ⟨(s6_leaf_group_register state first second .x5 (by decide)).trans ready.1,
        (s6_leaf_group_register state first second .x11 (by decide)).trans ready.2.2.1,
        (s6_leaf_group_register state first second .x13 (by decide)).trans ready.2.2.2.2⟩
      (by rw [groupInput]; decide) (by rw [groupOutput]; decide)
      (by rw [groupInput]; decide) (by rw [groupOutput]; decide) rest allowCoins
    rw [show ((s6LeafGroup state first second).getReg .x10).toNat = 56 by
      rw [groupInput]; rfl] at raw
    exact raw
  have replyPC (first second third : BitVec 1600) :
      (s6LeafReply state first second third).pc = BitVec.ofNat 64 (4096 + 4 * 429) := by
    rw [s6LeafReply, s3_permutation_pc, groupPC]
    rfl
  -- words 429..438
  have finish (first second third : BitVec 1600) (rest : Nat) :
      execute ((capExperimental 24).image .check) (10 + rest)
        (s6LeafReply state first second third) allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) rest
            (s3LeafDone state first second third) allowCoins
          return result.charge 10 0) := by
    have run := s3_run_execute ((capExperimental 24).image .check) s3LeafFinish .x8 32
      (by decide) false 429 (s6LeafReply state first second third) rest allowCoins
      (replyPC first second third) (by decide) s3_leaf_finish_decoded s3_leaf_finish_checked
      (fun impossible => by cases impossible)
    rw [s3_leaf_finish_length] at run
    exact run
  have donePC (first second third : BitVec 1600) :
      (s3LeafDone state first second third).pc = BitVec.ofNat 64 (4096 + 4 * 439) := by
    rw [s3LeafDone, s3_run_pc _ .x8 32 false _ s3_leaf_finish_checked, replyPC,
      s3_leaf_finish_length]
    rfl
  have doneLink (first second third : BitVec 1600) :
      (s3LeafDone state first second third).getReg .x1 = 4256 :=
    (s3_leaf_done_register state first second third .x1 (by decide)).trans link
  rw [show 174 + fuel = 55 + (1 + (51 + (1 + (2 + (8 + (35 + (9 + (1 + (10 + (1 + fuel))))))))))
      by omega, build, call]
  simp only [capCheckLeaf, bind_assoc, pure_bind]
  congr 1
  funext first
  rw [chain first, call2 first]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext second
  rw [slot first second, own first second, places first second, clear first second,
    call3 first second]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext third
  rw [finish first second third,
    s3_leaf_return_execute _ (donePC first second third) (doneLink first second third)]
  simp only [bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The count is structural and holds on every reply continuation. -/
theorem cap_check_leaf_query_bound (state : MachineState) :
    IsTotalQueryBound (capCheckLeaf state) 3 := by
  unfold capCheckLeaf s3PermutationQuery
  erw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun first => ?_⟩
  erw [isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun second => ?_⟩
  erw [isTotalQueryBound_query_bind_iff]
  exact ⟨by omega, fun third => by trivial⟩

theorem cap_check_leaf_support (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) :
    ∃ first second third, finished = s3LeafDone state first second third := by
  simp only [capCheckLeaf, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reachable
  obtain ⟨first, _, second, _, third, _, rfl⟩ := reachable
  exact ⟨first, second, third, rfl⟩

theorem cap_check_leaf_register_frame (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) (reg : Reg)
    (outside : reg ∉ [Reg.x5, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x20, .x25]) :
    finished.getReg reg = state.getReg reg := by
  obtain ⟨first, second, third, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_register state first second third reg outside

theorem cap_check_leaf_source (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) :
    finished.getReg .x8 = state.getReg .x8 + 256 := by
  obtain ⟨first, second, third, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_source state first second third

theorem cap_check_leaf_cursor (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) :
    finished.getReg .x25 = state.getReg .x25 + 96 := by
  obtain ⟨first, second, third, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_cursor state first second third

theorem cap_check_leaf_index (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLeaf state)) :
    finished.getReg .x20 = state.getReg .x20 >>> 2 := by
  obtain ⟨first, second, third, rfl⟩ := cap_check_leaf_support state finished reachable
  exact s3_leaf_done_index state first second third

end CommitGolfCandidate
