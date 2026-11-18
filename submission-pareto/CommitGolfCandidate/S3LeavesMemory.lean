import CommitGolfCandidate.S3LeafMemory
import CommitGolfCandidate.S3ReadyMemory
import CommitGolfCandidate.S4GenMemory
import CommitGolfCandidate.S6Model

/-! Commitment: fixed-oracle memory refinement of the generator and the leaf phase.

The generator (`S4GenMemory`) fills the nonce region from the seed; five stores clear the seed
block, so the cell region is zero again. Each block of 64 leaves writes leaf `i`'s first reply into
`[source + 256 i - 80, source + 256 i + 120)` (the dead tail of entry `i - 1` and its own head) and its
digest into its slot of cell `i / 4`; a slot reply spills at most to the end of its cell, so no cell's
72-byte zero prefix is ever written. The 16 group calls of the block then read their cells and write
the group digests into the heap's group slots; a group reply spills over the next slots, which are
written later, and the last one into the 256-byte gap below the cells. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-! ### Fixed-oracle evaluation of sequenced reference steps -/

theorem s3_evaluation_state (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).1 =
      (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).1 := by
  rw [check_evaluation_bind] <;> rfl

theorem s3_evaluation_calls (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).2 =
      (checkEvaluation oracle computation).2 +
        (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).2 := by
  rw [check_evaluation_bind] <;> rfl

theorem s3_evaluation_pure_state (oracle : Oracle) {α : Type} (value : α) :
    (checkEvaluation oracle (pure value : OracleComp World α)).1 = value := by
  rw [check_evaluation_pure]

theorem s3_evaluation_pure_calls (oracle : Oracle) {α : Type} (value : α) :
    (checkEvaluation oracle (pure value : OracleComp World α)).2 = 0 := by
  rw [check_evaluation_pure]

/-! ### Straight-line pieces -/

theorem s6_word_eq {left right : Nat} (same : left = right) :
    BitVec.ofNat 64 left = BitVec.ofNat 64 right := by
  rw [same]

/-- Leaf index `i` reduced into `Index`. -/
def s6Wrap (i : Nat) : Index := ⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩

theorem s6_wrap_eq (i : Nat) (inside : i < LENGTH) : s6Wrap i = ⟨i, inside⟩ :=
  Fin.ext (Nat.mod_eq_of_lt inside)

private theorem addi_value (state : MachineState) (target source : Reg) (immediate : BitVec 12)
    (notZero : target ≠ .x0) :
    (execInstrBr state (.ADDI target source immediate)).getReg target =
      state.getReg source + signExtend12 immediate := by
  show ((state.setReg target (state.getReg source + signExtend12 immediate)).setPC (state.pc + 4)).getReg
    target = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq notZero]

private theorem bltu_register (state : MachineState) (left right : Reg) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BLTU left right offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.getReg_setPC]

private theorem bltu_memory (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BLTU left right offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem s6_block_memory (state : MachineState) : (s6BlockBase state).mem = state.mem := rfl

theorem s6_block_kept (state : MachineState) (reg : Reg) (h25 : reg ≠ .x25) (h27 : reg ≠ .x27) :
    (s6BlockBase state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h25 | exact absurd rfl h27 | rfl

private theorem latch_split (state : MachineState) :
    s3LatchState state =
      execInstrBr (([.ADDI .x10 .x21 0, .ADDI .x18 .x18 1024, .ADDI .x24 .x24 512, .ADD .x23 .x23 .x7] :
        List Instr).foldl execInstrBr state) (.BLTU .x24 .x22 (BitVec.ofNat 13 5160)) := rfl

theorem s3_latch_memory (state : MachineState) : (s3LatchState state).mem = state.mem := by
  rw [latch_split, bltu_memory]
  rfl

theorem s3_latch_kept (state : MachineState) (reg : Reg) (h10 : reg ≠ .x10) (h18 : reg ≠ .x18)
    (h23 : reg ≠ .x23) (h24 : reg ≠ .x24) :
    (s3LatchState state).getReg reg = state.getReg reg := by
  rw [latch_split, bltu_register]
  cases reg <;> first | exact absurd rfl h10 | exact absurd rfl h18 | exact absurd rfl h23 |
    exact absurd rfl h24 | rfl

theorem s3_latch_values (state : MachineState) :
    (s3LatchState state).getReg .x10 = state.getReg .x21 + signExtend12 0 ∧
    (s3LatchState state).getReg .x18 = state.getReg .x18 + signExtend12 1024 ∧
    (s3LatchState state).getReg .x24 = state.getReg .x24 + signExtend12 512 ∧
    (s3LatchState state).getReg .x23 = state.getReg .x23 + state.getReg .x7 := by
  rw [latch_split, bltu_register, bltu_register, bltu_register, bltu_register]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem s6_leaf_setup_memory (state : MachineState) : (s6LeafSetup state).mem = state.mem := rfl

theorem s6_leaf_setup_kept (state : MachineState) (reg : Reg) (h7 : reg ≠ .x7) (h10 : reg ≠ .x10)
    (h18 : reg ≠ .x18) (h22 : reg ≠ .x22) (h23 : reg ≠ .x23) (h24 : reg ≠ .x24) :
    (s6LeafSetup state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h7 | exact absurd rfl h10 | exact absurd rfl h18 |
    exact absurd rfl h22 | exact absurd rfl h23 | exact absurd rfl h24 | rfl

/-- Pointers after the leaf setup: nonce base, group-slot end, first cell, slot of group 0, cell
stride, and the first window. -/
theorem s6_leaf_setup_values_mem (state : MachineState) (heap limit message : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (bound : state.getReg .x6 = BitVec.ofNat 64 limit)
    (entries : state.getReg .x8 = BitVec.ofNat 64 message) (low : 24 ≤ message) :
    (s6LeafSetup state).getReg .x18 = BitVec.ofNat 64 (limit + 24) ∧
    (s6LeafSetup state).getReg .x22 = BitVec.ofNat 64 (heap + 2^28) ∧
    (s6LeafSetup state).getReg .x23 = BitVec.ofNat 64 (heap + 2^28 + 256) ∧
    (s6LeafSetup state).getReg .x24 = BitVec.ofNat 64 (heap + 2^27) ∧
    (s6LeafSetup state).getReg .x7 = BitVec.ofNat 64 5888 ∧
    (s6LeafSetup state).getReg .x10 = BitVec.ofNat 64 (message - 24) := by
  have lui1 : ((65536 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (2^28) := by
    decide
  have lui2 : ((32768 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (2^27) := by
    decide
  have lui3 : ((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 4096 := by
    decide
  have r18 : (s6LeafSetup state).getReg .x18 = state.getReg .x6 + signExtend12 (BitVec.ofNat 12 24) := rfl
  have r22 : (s6LeafSetup state).getReg .x22 =
      state.getReg .x9 + ((65536 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 := rfl
  have r23 : (s6LeafSetup state).getReg .x23 =
      state.getReg .x9 + ((65536 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 +
        signExtend12 (BitVec.ofNat 12 256) := rfl
  have r24 : (s6LeafSetup state).getReg .x24 =
      state.getReg .x9 + ((32768 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 := rfl
  have r7 : (s6LeafSetup state).getReg .x7 =
      ((1 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 + signExtend12 1792 := rfl
  have r10 : (s6LeafSetup state).getReg .x10 = state.getReg .x8 + signExtend12 (BitVec.ofNat 12 4072) :=
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r18, bound, s3_address _ limit 24 _ rfl (s3_offset_extend 24 (by decide))]
  · rw [r22, lui1, base, ← BitVec.ofNat_add]
  · rw [r23, lui1, base, ← BitVec.ofNat_add, s3_address _ _ 256 _ rfl (s3_offset_extend 256 (by decide))]
  · rw [r24, lui2, base, ← BitVec.ofNat_add]
  · rw [r7, lui3, show signExtend12 (1792 : BitVec 12) = BitVec.ofNat 64 1792 from rfl,
      ← BitVec.ofNat_add]
  · rw [r10, entries, show signExtend12 (BitVec.ofNat 12 4072) = BitVec.ofNat 64 (2^64 - 24) from rfl,
      ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

/-- The group-slot end after the leaf setup. -/
theorem s6_leaf_setup_limit (state : MachineState) (heap : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap) :
    (s6LeafSetup state).getReg .x22 = BitVec.ofNat 64 (heap + 2^28) := by
  have lui : ((65536 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (2^28) := by
    decide
  have r22 : (s6LeafSetup state).getReg .x22 =
      state.getReg .x9 + ((65536 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64 := rfl
  rw [r22, lui, base, ← BitVec.ofNat_add]

/-! ### Registers and query counts, for every state -/

theorem s3_group_leaves_register (oracle : Oracle) (count : Nat) :
    ∀ (l : Nat) (state : MachineState) (reg : Reg), reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 →
    reg ≠ .x21 →
    (checkEvaluation oracle (s3GroupLeaves state l count)).1.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro l state reg _ _ _ _
    rw [s3GroupLeaves, s3_evaluation_pure_state]
  | succ count ih =>
    intro l state reg h6 h10 h12 h21
    rw [s3GroupLeaves, s3_evaluation_state, ih (l + 1) _ reg h6 h10 h12 h21,
      s3_leaf_register oracle l state reg h6 h10 h12 h21]

theorem s3_group_leaves_queries (oracle : Oracle) (count : Nat) :
    ∀ (l : Nat) (state : MachineState),
    (checkEvaluation oracle (s3GroupLeaves state l count)).2 = 2 * count := by
  induction count with
  | zero =>
    intro l state
    rw [s3GroupLeaves, s3_evaluation_pure_calls]
  | succ count ih =>
    intro l state
    rw [s3GroupLeaves, s3_evaluation_calls, s3_leaf_queries, ih]
    omega

theorem s6_group_calls_register (oracle : Oracle) (count : Nat) :
    ∀ (c : Nat) (state : MachineState) (reg : Reg), reg ≠ .x10 → reg ≠ .x12 →
    (checkEvaluation oracle (s6GroupCalls state c count)).1.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro c state reg _ _
    rw [s6GroupCalls, s3_evaluation_pure_state]
  | succ count ih =>
    intro c state reg h10 h12
    rw [s6GroupCalls, s3_evaluation_state, ih (c + 1) _ reg h10 h12,
      s6_group_call_register oracle c state reg h10 h12]

theorem s6_group_calls_queries (oracle : Oracle) (count : Nat) :
    ∀ (c : Nat) (state : MachineState), (checkEvaluation oracle (s6GroupCalls state c count)).2 = count := by
  induction count with
  | zero =>
    intro c state
    rw [s6GroupCalls, s3_evaluation_pure_calls]
  | succ count ih =>
    intro c state
    rw [s6GroupCalls, s3_evaluation_calls, s6_group_call_queries, ih]
    omega

theorem s3_group_state (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s3Group state)).1 =
      s3LatchState (checkEvaluation oracle
        (s6GroupCalls (checkEvaluation oracle (s3GroupLeaves (s6BlockBase state) 0 64)).1 0 16)).1 := by
  rw [s3Group, s3_evaluation_state, s3_evaluation_state, s3_evaluation_pure_state]

theorem s3_group_queries (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s3Group state)).2 = 144 := by
  rw [s3Group, s3_evaluation_calls, s3_evaluation_calls, s3_evaluation_pure_calls,
    s3_group_leaves_queries, s6_group_calls_queries]

/-- A block keeps every register except x6, x10, x12, x18, x21, x23, x24, x25, x27. -/
theorem s3_group_register (oracle : Oracle) (state : MachineState) (reg : Reg)
    (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) (h18 : reg ≠ .x18) (h21 : reg ≠ .x21)
    (h23 : reg ≠ .x23) (h24 : reg ≠ .x24) (h25 : reg ≠ .x25) (h27 : reg ≠ .x27) :
    (checkEvaluation oracle (s3Group state)).1.getReg reg = state.getReg reg := by
  rw [s3_group_state, s3_latch_kept _ reg h10 h18 h23 h24,
    s6_group_calls_register oracle 16 0 _ reg h10 h12,
    s3_group_leaves_register oracle 64 0 _ reg h6 h10 h12 h21, s6_block_kept state reg h25 h27]

theorem s3_groups_register (oracle : Oracle) (count : Nat) :
    ∀ (state : MachineState) (reg : Reg), reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 →
    reg ≠ .x21 → reg ≠ .x23 → reg ≠ .x24 → reg ≠ .x25 → reg ≠ .x27 →
    (checkEvaluation oracle (s3Groups state count)).1.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro state reg _ _ _ _ _ _ _ _ _
    rw [s3Groups, s3_evaluation_pure_state]
  | succ count ih =>
    intro state reg h6 h10 h12 h18 h21 h23 h24 h25 h27
    rw [s3Groups, s3_evaluation_state, ih _ reg h6 h10 h12 h18 h21 h23 h24 h25 h27,
      s3_group_register oracle state reg h6 h10 h12 h18 h21 h23 h24 h25 h27]

theorem s3_groups_queries (oracle : Oracle) (count : Nat) :
    ∀ state : MachineState, (checkEvaluation oracle (s3Groups state count)).2 = 144 * count := by
  induction count with
  | zero =>
    intro state
    rw [s3Groups, s3_evaluation_pure_calls]
  | succ count ih =>
    intro state
    rw [s3Groups, s3_evaluation_calls, s3_group_queries, ih]
    omega

theorem s3_leaves_state (oracle : Oracle) (state : MachineState) (groups : Nat) :
    (checkEvaluation oracle (s3Leaves state groups)).1 =
      (checkEvaluation oracle
        (s3Groups (s6LeafSetup (s6GenClear (checkEvaluation oracle (s4Generator state 23832)).1))
          groups)).1 := by
  rw [s3Leaves, s3_evaluation_state]

/-- One permutation query per generator call, two per leaf and one per group. -/
theorem s3_leaves_queries (oracle : Oracle) (state : MachineState) (groups : Nat) :
    (checkEvaluation oracle (s3Leaves state groups)).2 = 1525248 + 144 * groups := by
  rw [s3Leaves, s3_evaluation_calls, s3_groups_queries, s4_generator_queries]

/-! ### Loop invariant -/

/-- Message entries, group slots, cells and nonces, in increasing address order. -/
structure S6Layout (source slots cells nonces blocks : Nat) : Prop where
  low : 80 ≤ source
  sourceAligned : source % 8 = 0
  slotsAligned : slots % 8 = 0
  cellsAligned : cells % 8 = 0
  noncesAligned : nonces % 8 = 0
  sourceEnd : source + 256 * (64 * blocks) ≤ slots
  slotsEnd : slots + 32 * (16 * blocks) + 168 ≤ cells
  cellsEnd : cells + 368 * (16 * blocks) ≤ nonces
  noncesEnd : nonces + 16 * (64 * blocks) ≤ 2 ^ 64

/-- Digest of leaf `i` under nonce `nonce i`, its tag being its window address `source - 24 + 256 i`. -/
def s6Digest (permutation : Perm) (source : Nat) (message : Nat → Entry) (nonce : Nat → BitVec 128)
    (i : Nat) : Digest :=
  s3LeafDigest permutation (BitVec.ofNat 256 ((nonce i).toNat + (source - 24 + 256 * i) * 2^128))
    (message i)

/-- Address of leaf `i`'s digest in its cell. -/
def s6Slot (cells i : Nat) : Nat := cells + 368 * (i / 4) + 72 + 32 * (i % 4)

/-- Memory after `leaves` leaves and `groups` group calls. -/
structure S6Progress (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128) (state : MachineState) (leaves groups : Nat) :
    Prop where
  pending : ∀ i, leaves ≤ i → i < 64 * blocks → readBuffer state (source + 256 * i) 256 = message i
  hashed : ∀ i, i < leaves → readBuffer state (s6Slot cells i) 32 =
    s6Digest oracle.permutation source message nonce i
  zero : ∀ g, g < 16 * blocks → (readBuffer state (cells + 368 * g) 72).toNat = 0
  fresh : ∀ i, i < 64 * blocks → readBuffer state (nonces + 16 * i) 16 = nonce i
  grouped : ∀ g, g < groups → readBuffer state (slots + 32 * g) 32 =
    s6GroupDigest oracle.permutation (s6Digest oracle.permutation source message nonce (4 * g))
      (s6Digest oracle.permutation source message nonce (4 * g + 1))
      (s6Digest oracle.permutation source message nonce (4 * g + 2))
      (s6Digest oracle.permutation source message nonce (4 * g + 3))

theorem s6_progress_memory (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128) (left right : MachineState) (leaves groups : Nat)
    (same : right.mem = left.mem)
    (progress : S6Progress oracle source slots cells nonces blocks message nonce left leaves groups) :
    S6Progress oracle source slots cells nonces blocks message nonce right leaves groups :=
  ⟨fun i after below => (s3_read_memory right left same _ _).trans (progress.pending i after below),
    fun i before => (s3_read_memory right left same _ _).trans (progress.hashed i before),
    fun g below => by rw [s3_read_memory right left same]; exact progress.zero g below,
    fun i below => (s3_read_memory right left same _ _).trans (progress.fresh i below),
    fun g before => (s3_read_memory right left same _ _).trans (progress.grouped g before)⟩

/-- The three cell base registers of block `b`. -/
structure S6CellRegisters (state : MachineState) (cellsBlock : Nat) : Prop where
  first : state.getReg .x23 = BitVec.ofNat 64 cellsBlock
  middle : state.getReg .x25 = BitVec.ofNat 64 (cellsBlock + 1840)
  last : state.getReg .x27 = BitVec.ofNat 64 (cellsBlock + 3680)

theorem s6_cell_register (state : MachineState) (cellsBlock c : Nat)
    (registers : S6CellRegisters state cellsBlock) :
    state.getReg (s6CellRegister c) = BitVec.ofNat 64 (cellsBlock + s6CellShift c) := by
  unfold s6CellRegister s6CellShift
  split_ifs
  · rw [Nat.add_zero]; exact registers.first
  · exact registers.middle
  · exact registers.last

theorem s6_cell_registers_kept (left right : MachineState) (cellsBlock : Nat)
    (h23 : right.getReg .x23 = left.getReg .x23) (h25 : right.getReg .x25 = left.getReg .x25)
    (h27 : right.getReg .x27 = left.getReg .x27) (registers : S6CellRegisters left cellsBlock) :
    S6CellRegisters right cellsBlock :=
  ⟨h23.trans registers.first, h25.trans registers.middle, h27.trans registers.last⟩

theorem s6_block_registers (state : MachineState) (cellsBlock : Nat)
    (pointer : state.getReg .x23 = BitVec.ofNat 64 cellsBlock) :
    S6CellRegisters (s6BlockBase state) cellsBlock := by
  have r23 : (s6BlockBase state).getReg .x23 = state.getReg .x23 := rfl
  have r25 : (s6BlockBase state).getReg .x25 = state.getReg .x23 + signExtend12 1840 := rfl
  have r27 : (s6BlockBase state).getReg .x27 =
      state.getReg .x23 + signExtend12 1840 + signExtend12 1840 := rfl
  refine ⟨r23.trans pointer, ?_, ?_⟩
  · rw [r25, pointer, show signExtend12 (1840 : BitVec 12) = BitVec.ofNat 64 1840 from rfl,
      ← BitVec.ofNat_add]
  · rw [r27, pointer, show signExtend12 (1840 : BitVec 12) = BitVec.ofNat 64 1840 from rfl,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]

set_option maxHeartbeats 16000000 in
/-- One leaf extends the invariant. -/
theorem s6_progress_leaf (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128)
    (layout : S6Layout source slots cells nonces blocks) (state : MachineState) (b l : Nat)
    (unit : l < 64) (inside : b < blocks)
    (input : state.getReg .x10 = BitVec.ofNat 64 (source - 24 + 256 * (64 * b + l)))
    (noncePointer : state.getReg .x18 = BitVec.ofNat 64 (nonces + 1024 * b))
    (registers : S6CellRegisters state (cells + 5888 * b))
    (progress : S6Progress oracle source slots cells nonces blocks message nonce state
      (64 * b + l) (16 * b)) :
    S6Progress oracle source slots cells nonces blocks message nonce
      (checkEvaluation oracle (s3Leaf l state)).1 (64 * b + l + 1) (16 * b) := by
  obtain ⟨low, sourceAligned, slotsAligned, cellsAligned, noncesAligned, sourceEnd, slotsEnd,
    cellsEnd, noncesEnd⟩ := layout
  have slotOffset := s6_slot_offset l unit
  have slotAddress := s6_slot_address l unit
  have quarter : (64 * b + l) / 4 = 16 * b + l / 4 := by omega
  have remainder : (64 * b + l) % 4 = l % 4 := by omega
  have cellBelow : l / 4 < 16 := by omega
  have unitBelow : l % 4 < 4 := Nat.mod_lt _ (by decide)
  have shift : s6CellShift (l / 4) ≤ 3680 := by unfold s6CellShift; split_ifs <;> omega
  have frame : S3LeafFrame state l (source - 24 + 256 * (64 * b + l)) (nonces + 1024 * b)
      (cells + 5888 * b + s6CellShift (l / 4)) :=
    ⟨input, noncePointer, s6_cell_register state _ _ registers, unit, by omega, by omega,
      by unfold s6CellShift; split_ifs <;> omega, by omega, by omega, by omega, by omega,
      Or.inr (by omega)⟩
  have slotIs : cells + 5888 * b + s6CellShift (l / 4) + s6SlotOffset l = s6Slot cells (64 * b + l) := by
    unfold s6Slot
    omega
  have preserved (address count : Nat) (fits : address + count ≤ 2^64)
      (inputSide : address + count ≤ source - 24 + 256 * (64 * b + l) - 56 ∨
        source - 24 + 256 * (64 * b + l) + 144 ≤ address)
      (outputSide : address + count ≤ s6Slot cells (64 * b + l) ∨
        s6Slot cells (64 * b + l) + 200 ≤ address) :=
    s3_leaf_preserves oracle l state _ _ _ address count frame fits inputSide (by rw [slotIs]; exact outputSide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i after below
    rw [preserved (source + 256 * i) 256 (by omega) (Or.inr (by omega)) (Or.inl (by unfold s6Slot; omega))]
    exact progress.pending i (by omega) below
  · intro i before
    by_cases last : i = 64 * b + l
    · subst last
      have digest := s3_leaf_digest oracle l state _ _ _ (nonce (64 * b + l))
        (message (64 * b + l)) frame
        (by
          rw [s3_read_address state (nonces + 1024 * b + 16 * l) (nonces + 16 * (64 * b + l)) 16
            (by omega)]
          exact progress.fresh _ (by omega))
        (by
          rw [s3_read_address state (source - 24 + 256 * (64 * b + l) + 24) (source + 256 * (64 * b + l))
            256 (by omega)]
          exact progress.pending _ (Nat.le_refl _) (by omega))
      rw [slotIs] at digest
      exact digest
    · have earlier : i < 64 * b + l := by omega
      rw [preserved (s6Slot cells i) 32 (by unfold s6Slot; omega) (Or.inr (by unfold s6Slot; omega))
        (Or.inl (by unfold s6Slot; omega))]
      exact progress.hashed i earlier
  · intro g below
    rw [preserved (cells + 368 * g) 72 (by omega) (Or.inr (by omega)) (by
      unfold s6Slot
      rw [quarter, remainder]
      rcases Nat.lt_or_ge (16 * b + l / 4) g with after | before
      · exact Or.inr (by omega)
      · exact Or.inl (by omega))]
    exact progress.zero g below
  · intro i below
    rw [preserved (nonces + 16 * i) 16 (by omega) (Or.inr (by omega))
      (Or.inr (by unfold s6Slot; rw [quarter, remainder]; omega))]
    exact progress.fresh i below
  · intro g before
    rw [preserved (slots + 32 * g) 32 (by omega) (Or.inr (by omega)) (Or.inl (by unfold s6Slot; omega))]
    exact progress.grouped g before

/-- The leaves of one block, from leaf `l` on. -/
theorem s6_progress_leaves (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128)
    (layout : S6Layout source slots cells nonces blocks) (b : Nat) (inside : b < blocks)
    (count : Nat) :
    ∀ (l : Nat) (state : MachineState), l < 64 → l + count ≤ 64 →
    state.getReg .x10 = BitVec.ofNat 64 (source - 24 + 256 * (64 * b + l)) →
    state.getReg .x18 = BitVec.ofNat 64 (nonces + 1024 * b) →
    S6CellRegisters state (cells + 5888 * b) →
    S6Progress oracle source slots cells nonces blocks message nonce state (64 * b + l) (16 * b) →
    S6Progress oracle source slots cells nonces blocks message nonce
      (checkEvaluation oracle (s3GroupLeaves state l count)).1 (64 * b + l + count) (16 * b) ∧
    (l + count < 64 → (checkEvaluation oracle (s3GroupLeaves state l count)).1.getReg .x10 =
      BitVec.ofNat 64 (source - 24 + 256 * (64 * b + l + count))) ∧
    (l + count = 64 → 0 < count → (checkEvaluation oracle (s3GroupLeaves state l count)).1.getReg .x21 =
      BitVec.ofNat 64 (source - 24 + 256 * (64 * b + 64))) := by
  induction count with
  | zero =>
    intro l state _ _ input _ _ progress
    rw [s3GroupLeaves, s3_evaluation_pure_state]
    exact ⟨progress, fun _ => input, fun _ positive => absurd positive (Nat.lt_irrefl 0)⟩
  | succ count ih =>
    intro l state unit fits input noncePointer registers progress
    have step := s6_progress_leaf oracle source slots cells nonces blocks message nonce layout state
      b l unit inside input noncePointer registers progress
    have link := s3_leaf_link oracle l state _ input
    have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
        (h12 : reg ≠ .x12 := by decide) (h21 : reg ≠ .x21 := by decide) :=
      s3_leaf_register oracle l state reg h6 h10 h12 h21
    rw [s3GroupLeaves, s3_evaluation_state]
    by_cases final : l = 63
    · subst final
      have zeroCount : count = 0 := by omega
      subst zeroCount
      rw [s3GroupLeaves, s3_evaluation_pure_state]
      refine ⟨step, fun below => absurd below (by omega), fun _ _ => ?_⟩
      have linkReg : s3LeafNextRegister 63 = .x21 := rfl
      rw [linkReg] at link
      rw [link]
      all_goals (congr 1 <;> omega)
    · have linkReg : s3LeafNextRegister l = .x10 := by unfold s3LeafNextRegister; exact if_neg final
      rw [linkReg] at link
      have next := ih (l + 1) (checkEvaluation oracle (s3Leaf l state)).1 (by omega) (by omega)
        (link.trans (s6_word_eq (by omega))) ((kept .x18).trans noncePointer)
        (s6_cell_registers_kept _ _ _ (kept .x23) (kept .x25) (kept .x27) registers)
        (by rw [show 64 * b + (l + 1) = 64 * b + l + 1 by omega]; exact step)
      rw [show 64 * b + l + (count + 1) = 64 * b + (l + 1) + count by omega,
        show l + (count + 1) = l + 1 + count by omega]
      exact ⟨next.1, next.2.1, fun full _ => by
        by_cases more : 0 < count
        · exact next.2.2 full more
        · omega⟩

set_option maxHeartbeats 16000000 in
/-- One group call extends the invariant. -/
theorem s6_progress_group (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128)
    (layout : S6Layout source slots cells nonces blocks) (state : MachineState) (b c : Nat)
    (small : c < 16) (inside : b < blocks)
    (slotPointer : state.getReg .x24 = BitVec.ofNat 64 (slots + 512 * b))
    (registers : S6CellRegisters state (cells + 5888 * b))
    (progress : S6Progress oracle source slots cells nonces blocks message nonce state
      (64 * (b + 1)) (16 * b + c)) :
    S6Progress oracle source slots cells nonces blocks message nonce
      (checkEvaluation oracle (s6GroupCall c state)).1 (64 * (b + 1)) (16 * b + c + 1) := by
  obtain ⟨low, sourceAligned, slotsAligned, cellsAligned, noncesAligned, sourceEnd, slotsEnd,
    cellsEnd, noncesEnd⟩ := layout
  have cellAddress := s6_cell_address_sum c small
  have cellOffset := s6_cell_offset c small
  have preserved (address count : Nat) (fits : address + count ≤ 2^64)
      (outside : address + count ≤ slots + 512 * b + 32 * c ∨ slots + 512 * b + 32 * c + 200 ≤ address) :=
    s6_group_call_preserves oracle c state (slots + 512 * b) address count slotPointer small (by omega) fits
      outside
  have cellIs : cells + 5888 * b + s6CellShift c + s6CellOffset c = cells + 368 * (16 * b + c) := by
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i after below
    rw [preserved (source + 256 * i) 256 (by omega) (Or.inl (by omega))]
    exact progress.pending i after below
  · intro i before
    rw [preserved (s6Slot cells i) 32 (by unfold s6Slot; omega) (Or.inr (by unfold s6Slot; omega))]
    exact progress.hashed i before
  · intro g below
    rw [preserved (cells + 368 * g) 72 (by omega) (Or.inr (by omega))]
    exact progress.zero g below
  · intro i below
    rw [preserved (nonces + 16 * i) 16 (by omega) (Or.inr (by omega))]
    exact progress.fresh i below
  · intro g before
    by_cases last : g = 16 * b + c
    · subst last
      have digest (u : Nat) (hu : u < 4) :
          readBuffer state (cells + 5888 * b + s6CellShift c + s6CellOffset c + 72 + 32 * u) 32 =
            s6Digest oracle.permutation source message nonce (4 * (16 * b + c) + u) := by
        rw [s3_read_address state _ (s6Slot cells (4 * (16 * b + c) + u)) 32 (by unfold s6Slot; omega)]
        exact progress.hashed _ (by omega)
      have group := s6_cell_group oracle c state (cells + 5888 * b + s6CellShift c) (slots + 512 * b)
        (s6Digest oracle.permutation source message nonce (4 * (16 * b + c)))
        (s6Digest oracle.permutation source message nonce (4 * (16 * b + c) + 1))
        (s6Digest oracle.permutation source message nonce (4 * (16 * b + c) + 2))
        (s6Digest oracle.permutation source message nonce (4 * (16 * b + c) + 3))
        (s6_cell_register state _ c registers) slotPointer small (by omega) (by omega)
        (by rw [cellIs]; exact progress.zero _ (by omega))
        (by have := digest 0 (by decide); simpa using this)
        (by have := digest 1 (by decide); rw [show cells + 5888 * b + s6CellShift c + s6CellOffset c + 104 =
              cells + 5888 * b + s6CellShift c + s6CellOffset c + 72 + 32 * 1 by omega]; exact this)
        (by have := digest 2 (by decide); rw [show cells + 5888 * b + s6CellShift c + s6CellOffset c + 136 =
              cells + 5888 * b + s6CellShift c + s6CellOffset c + 72 + 32 * 2 by omega]; exact this)
        (by have := digest 3 (by decide); rw [show cells + 5888 * b + s6CellShift c + s6CellOffset c + 168 =
              cells + 5888 * b + s6CellShift c + s6CellOffset c + 72 + 32 * 3 by omega]; exact this)
      rw [s3_read_address _ (slots + 32 * (16 * b + c)) (slots + 512 * b + 32 * c) 32 (by omega), group]
    · rw [preserved (slots + 32 * g) 32 (by omega) (Or.inl (by omega))]
      exact progress.grouped g (by omega)

/-- The group calls of one block, from cell `c` on. -/
theorem s6_progress_groups_calls (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128)
    (layout : S6Layout source slots cells nonces blocks) (b : Nat) (inside : b < blocks)
    (count : Nat) :
    ∀ (c : Nat) (state : MachineState), c + count ≤ 16 →
    state.getReg .x24 = BitVec.ofNat 64 (slots + 512 * b) →
    S6CellRegisters state (cells + 5888 * b) →
    S6Progress oracle source slots cells nonces blocks message nonce state (64 * (b + 1)) (16 * b + c) →
    S6Progress oracle source slots cells nonces blocks message nonce
      (checkEvaluation oracle (s6GroupCalls state c count)).1 (64 * (b + 1)) (16 * b + c + count) := by
  induction count with
  | zero =>
    intro c state _ _ _ progress
    rw [s6GroupCalls, s3_evaluation_pure_state]
    exact progress
  | succ count ih =>
    intro c state fits slotPointer registers progress
    have step := s6_progress_group oracle source slots cells nonces blocks message nonce layout state
      b c (by omega) inside slotPointer registers progress
    have kept (reg : Reg) (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide) :=
      s6_group_call_register oracle c state reg h10 h12
    have next := ih (c + 1) (checkEvaluation oracle (s6GroupCall c state)).1 (by omega)
      ((kept .x24).trans slotPointer)
      (s6_cell_registers_kept _ _ _ (kept .x23) (kept .x25) (kept .x27) registers)
      (by rw [show 16 * b + (c + 1) = 16 * b + c + 1 by omega]; exact step)
    rw [s6GroupCalls, s3_evaluation_state, show 16 * b + c + (count + 1) = 16 * b + (c + 1) + count by omega]
    exact next

/-- Pointers at the start of block `b`. -/
structure S6BlockPointers (state : MachineState) (source slots cells nonces b : Nat) : Prop where
  input : state.getReg .x10 = BitVec.ofNat 64 (source - 24 + 256 * (64 * b))
  nonce : state.getReg .x18 = BitVec.ofNat 64 (nonces + 1024 * b)
  cell : state.getReg .x23 = BitVec.ofNat 64 (cells + 5888 * b)
  slot : state.getReg .x24 = BitVec.ofNat 64 (slots + 512 * b)
  stride : state.getReg .x7 = BitVec.ofNat 64 5888

/-- One block: two base registers, 64 leaves, 16 group calls, the latch. -/
theorem s6_progress_block (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128)
    (layout : S6Layout source slots cells nonces blocks) (b : Nat) (inside : b < blocks)
    (state : MachineState) (pointers : S6BlockPointers state source slots cells nonces b)
    (progress : S6Progress oracle source slots cells nonces blocks message nonce state (64 * b) (16 * b)) :
    S6Progress oracle source slots cells nonces blocks message nonce
      (checkEvaluation oracle (s3Group state)).1 (64 * (b + 1)) (16 * (b + 1)) ∧
    S6BlockPointers (checkEvaluation oracle (s3Group state)).1 source slots cells nonces (b + 1) := by
  let entered := s6BlockBase state
  have registers : S6CellRegisters entered (cells + 5888 * b) := s6_block_registers state _ pointers.cell
  have enteredKept (reg : Reg) (h25 : reg ≠ .x25 := by decide) (h27 : reg ≠ .x27 := by decide) :
      entered.getReg reg = state.getReg reg := s6_block_kept state reg h25 h27
  have leaves := s6_progress_leaves oracle source slots cells nonces blocks message nonce layout b inside
    64 0 entered (by decide) (by decide)
    ((enteredKept .x10).trans (pointers.input.trans (s6_word_eq (by omega))))
    ((enteredKept .x18).trans pointers.nonce) registers
    (s6_progress_memory oracle source slots cells nonces blocks message nonce _ _ _ _
      (s6_block_memory state) (by simpa using progress))
  let hashed := (checkEvaluation oracle (s3GroupLeaves entered 0 64)).1
  have leafKept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h12 : reg ≠ .x12 := by decide) (h21 : reg ≠ .x21 := by decide) :
      hashed.getReg reg = entered.getReg reg :=
    s3_group_leaves_register oracle 64 0 entered reg h6 h10 h12 h21
  have afterLeaves : S6Progress oracle source slots cells nonces blocks message nonce hashed
      (64 * (b + 1)) (16 * b + 0) := by
    have p := leaves.1
    rw [show 64 * b + 0 + 64 = 64 * (b + 1) by omega] at p
    simpa using p
  have hashedRegisters : S6CellRegisters hashed (cells + 5888 * b) :=
    s6_cell_registers_kept _ _ _ (leafKept .x23) (leafKept .x25) (leafKept .x27) registers
  have groups := s6_progress_groups_calls oracle source slots cells nonces blocks message nonce layout b
    inside 16 0 hashed (by decide)
    ((leafKept .x24).trans ((enteredKept .x24).trans pointers.slot)) hashedRegisters afterLeaves
  let grouped := (checkEvaluation oracle (s6GroupCalls hashed 0 16)).1
  have groupKept (reg : Reg) (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide) :
      grouped.getReg reg = hashed.getReg reg :=
    s6_group_calls_register oracle 16 0 hashed reg h10 h12
  have values := s3_latch_values grouped
  have link : hashed.getReg .x21 = BitVec.ofNat 64 (source - 24 + 256 * (64 * b + 64)) :=
    leaves.2.2 (by decide) (by decide)
  rw [s3_group_state]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply s6_progress_memory oracle source slots cells nonces blocks message nonce _ _ _ _
      (s3_latch_memory grouped)
    rw [show 16 * (b + 1) = 16 * b + 0 + 16 by omega]
    exact groups
  · rw [values.1, groupKept .x21, link, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 from rfl,
      ← BitVec.ofNat_add]
    all_goals (congr 1 <;> omega)
  · rw [values.2.1, groupKept .x18, leafKept .x18, enteredKept .x18, pointers.nonce,
      show signExtend12 (1024 : BitVec 12) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add]
    all_goals (congr 1 <;> omega)
  · rw [values.2.2.2, groupKept .x23, groupKept .x7, leafKept .x23, leafKept .x7, enteredKept .x23,
      enteredKept .x7, pointers.cell, pointers.stride, ← BitVec.ofNat_add]
    all_goals (congr 1 <;> omega)
  · rw [values.2.2.1, groupKept .x24, leafKept .x24, enteredKept .x24, pointers.slot,
      show signExtend12 (512 : BitVec 12) = BitVec.ofNat 64 512 from rfl, ← BitVec.ofNat_add]
    all_goals (congr 1 <;> omega)
  · rw [s3_latch_kept _ .x7 (by decide) (by decide) (by decide) (by decide), groupKept .x7, leafKept .x7,
      enteredKept .x7]
    exact pointers.stride

/-- All remaining blocks. -/
theorem s6_progress_blocks (oracle : Oracle) (source slots cells nonces blocks : Nat)
    (message : Nat → Entry) (nonce : Nat → BitVec 128)
    (layout : S6Layout source slots cells nonces blocks) (count : Nat) :
    ∀ (b : Nat) (state : MachineState), b + count ≤ blocks →
    S6BlockPointers state source slots cells nonces b →
    S6Progress oracle source slots cells nonces blocks message nonce state (64 * b) (16 * b) →
    S6Progress oracle source slots cells nonces blocks message nonce
      (checkEvaluation oracle (s3Groups state count)).1 (64 * (b + count)) (16 * (b + count)) := by
  induction count with
  | zero =>
    intro b state _ _ progress
    rw [s3Groups, s3_evaluation_pure_state]
    simpa using progress
  | succ count ih =>
    intro b state fits pointers progress
    have step := s6_progress_block oracle source slots cells nonces blocks message nonce layout b
      (by omega) state pointers progress
    have next := ih (b + 1) (checkEvaluation oracle (s3Group state)).1 (by omega) step.2 step.1
    rw [s3Groups, s3_evaluation_state, show b + (count + 1) = b + 1 + count by omega]
    exact next

/-! ### The whole leaf phase on the actual layout -/

theorem s6_ready_layout : S6Layout 4096 4429189152 4563407136 6106911008 (2 ^ 18) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The digest of leaf `i` on the actual layout is the tree's leaf value. -/
theorem s6_digest_values (permutation : Perm) (message : Message) (nonce : Index → Nonce128) (i : Nat)
    (inside : i < LENGTH) :
    s6Digest permutation 4096 (fun j => message (s6Wrap j)) (fun j => nonce (s6Wrap j)) i =
      s6LeafValues permutation message (expandTaggedVector nonce) i := by
  unfold s6Digest s6LeafValues expandTaggedVector expandTagged s6Tag
  rw [dif_pos inside]
  beta_reduce
  rw [s6_wrap_eq i inside]

/-- The whole appended leaf code from any state with the commitment's pointers, message entries,
seed and zero memory above the message: cells hold the leaf digests, group slots the group
digests, and the nonce region the generated nonces. Stated over a variable state. -/
theorem s3_leaves_generated (oracle : Oracle) (state : MachineState) (message : Message)
    (seed : BitVec 256)
    (messagePointer : state.getReg .x8 = BitVec.ofNat 64 4096)
    (seedPointer : state.getReg .x18 = BitVec.ofNat 64 5368713248)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 4294971424)
    (entries : ∀ index : Index, readBuffer state (4096+256*index.val) 256 = message index)
    (seeded : readBuffer state 5368713248 32 = seed)
    (zero : ∀ q, 4294971392 ≤ q → q < 2^36 → (q < 5368713248 ∨ 5368713280 ≤ q) →
      state.getByte (BitVec.ofNat 64 q) = 0) :
    S6Progress oracle 4096 4429189152 4563407136 6106911008 (2 ^ 18)
      (fun i => message (s6Wrap i)) (fun i => s4GenNonce oracle.permutation seed (s6Wrap i))
      (checkEvaluation oracle (s3Leaves state (2^18))).1 (2^24) (2^22) := by
  let generated := (checkEvaluation oracle (s4Generator state 23832)).1
  let cleared := s6GenClear generated
  let ready := s6LeafSetup cleared
  have genKept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h11 : reg ≠ .x11 := by decide) (h12 : reg ≠ .x12 := by decide)
      (h13 : reg ≠ .x13 := by decide) : generated.getReg reg = state.getReg reg :=
    s4_generator_register oracle state 23832 reg h6 h10 h11 h12 h13
  have genPointers := s4_generator_pointers oracle state 23832 5368713248 4294971424 seedPointer heapPointer
    (by decide)
  have progress := s4_generator_progress oracle state 5368713248 4294971424 seedPointer heapPointer
    (by decide) (by decide) (by decide) (by decide)
  have clearByte (q : Nat) (hq : q < 2^64) :=
    s6_gen_clear_byte generated (5368713248 - 168) q genPointers.2 (by decide) (by decide) hq
  have values := s6_leaf_setup_values_mem cleared 4294971424 6106910984 4096
    ((s6_gen_clear_register_mem _ _).trans ((genKept .x9).trans heapPointer))
    ((s6_gen_clear_register_mem _ _).trans genPointers.1)
    ((s6_gen_clear_register_mem _ _).trans ((genKept .x8).trans messagePointer)) (by decide)
  have readyByte (q : Nat) : ready.getByte (BitVec.ofNat 64 q) = cleared.getByte (BitVec.ofNat 64 q) :=
    s3_byte_memory _ _ (s6_leaf_setup_memory cleared) _
  have start : S6Progress oracle 4096 4429189152 4563407136 6106911008 (2 ^ 18)
      (fun i => message (s6Wrap i)) (fun i => s4GenNonce oracle.permutation seed (s6Wrap i)) ready 0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i _ below
      rw [s3_read_congr ready state (4096 + 256 * i) (4096 + 256 * i) 256 (fun j hj => by
        rw [readyByte, clearByte _ (by omega), if_neg (by omega),
          progress.outside _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))])]
      have loaded := entries ⟨i, below⟩
      rw [s6_wrap_eq i below]
      exact loaded
    · intro i before
      exact absurd before (Nat.not_lt_zero i)
    · intro g below
      apply gen_read_zero_nat
      intro j hj
      rw [readyByte, clearByte _ (by omega)]
      by_cases block : (5368713248 - 168 ≤ 4563407136 + 368 * g + j ∧
          4563407136 + 368 * g + j < 5368713248 - 168 + 8) ∨
        (5368713248 - 168 + 168 ≤ 4563407136 + 368 * g + j ∧
          4563407136 + 368 * g + j < 5368713248 - 168 + 200)
      · rw [if_pos block]
      · rw [if_neg block, progress.outside _ (by omega) (by omega) (Or.inl (by omega))]
        exact zero _ (by omega) (by omega) (by omega)
    · intro i below
      have generatedNonce := s4_generator_nonce oracle state seed seedPointer heapPointer seeded
        (fun i hi => zero _ (by omega) (by omega) (by omega)) ⟨i, below⟩
      rw [s6_wrap_eq i below]
      rw [s3_read_congr ready generated (6106911008 + 16 * i) (6106911008 + 16 * i) 16 (fun j hj => by
        rw [readyByte, clearByte _ (by omega), if_neg (by omega)])]
      exact generatedNonce
    · intro g before
      exact absurd before (Nat.not_lt_zero g)
  have pointers : S6BlockPointers ready 4096 4429189152 4563407136 6106911008 0 :=
    ⟨values.2.2.2.2.2.trans (s6_word_eq (by norm_num)), values.1.trans (s6_word_eq (by norm_num)),
      values.2.2.1.trans (s6_word_eq (by norm_num)), values.2.2.2.1.trans (s6_word_eq (by norm_num)),
      values.2.2.2.2.1⟩
  have result := s6_progress_blocks oracle 4096 4429189152 4563407136 6106911008 (2 ^ 18)
    (fun i => message (s6Wrap i)) (fun i => s4GenNonce oracle.permutation seed (s6Wrap i)) s6_ready_layout
    (2 ^ 18) 0 ready (by decide) pointers start
  rw [s3_leaves_state]
  rw [show 64 * (0 + 2 ^ 18) = 2 ^ 24 by norm_num, show 16 * (0 + 2 ^ 18) = 2 ^ 22 by norm_num] at result
  exact result
where
  gen_read_zero_nat (state : MachineState) (address count : Nat)
      (zero : ∀ i < count, state.getByte (BitVec.ofNat 64 (address+i)) = 0) :
      (readBuffer state address count).toNat = 0 := by
    unfold readBuffer
    rw [Finset.sum_eq_zero (fun i hi => by simp [zero i (Finset.mem_range.mp hi)])]
    simp

/-- Registers kept by the whole leaf phase. -/
theorem s3_leaves_kept (oracle : Oracle) (state : MachineState) (groups : Nat) (reg : Reg)
    (h6 : reg ≠ .x6) (h7 : reg ≠ .x7) (h10 : reg ≠ .x10) (h11 : reg ≠ .x11) (h12 : reg ≠ .x12)
    (h13 : reg ≠ .x13) (h18 : reg ≠ .x18) (h21 : reg ≠ .x21) (h22 : reg ≠ .x22) (h23 : reg ≠ .x23)
    (h24 : reg ≠ .x24) (h25 : reg ≠ .x25) (h27 : reg ≠ .x27) :
    (checkEvaluation oracle (s3Leaves state groups)).1.getReg reg = state.getReg reg := by
  rw [s3_leaves_state, s3_groups_register oracle groups _ reg h6 h10 h12 h18 h21 h23 h24 h25 h27,
    s6_leaf_setup_kept _ reg h7 h10 h18 h22 h23 h24, s6_gen_clear_register_mem,
    s4_generator_register oracle state 23832 reg h6 h10 h11 h12 h13]

/-- Registers after the leaf phase that the parent loop and the root copy read. -/
theorem s3_leaves_register (oracle : Oracle) (state : MachineState) (groups : Nat) (reg : Reg)
    (member : reg ∈ [Reg.x8, .x9, .x26]) :
    (checkEvaluation oracle (s3Leaves state groups)).1.getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    exact s3_leaves_kept oracle state groups _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)

/-- The group-slot end register after the leaf phase. -/
theorem s3_leaves_limit (oracle : Oracle) (state : MachineState) (groups heap : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 heap) :
    (checkEvaluation oracle (s3Leaves state groups)).1.getReg .x22 = BitVec.ofNat 64 (heap + 2^28) := by
  rw [s3_leaves_state, s3_groups_register oracle groups _ .x22 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [s6_leaf_setup_limit _ heap (by rw [s6_gen_clear_register_mem, s4_generator_register oracle state 23832 .x9
    (by decide) (by decide) (by decide) (by decide) (by decide), heapPointer])]

/-! ### The actual commitment state -/

/-- After the generator and all 2^24 leaves, each leaf's cell slot holds its digest under its
tagged generated nonce. -/
theorem s3_leaves_digest (oracle : Oracle) (message : Message) (answer : BitVec 256) (index : Index) :
    readBuffer (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
        (4563407136 + 368 * (index.val / 4) + 72 + 32 * (index.val % 4)) 32 =
      s3LeafDigest oracle.permutation (expandTagged index (s4GenNonce oracle.permutation answer index))
        (message index) := by
  have regs := s3_ready_registers message answer
  have result := (s3_leaves_generated oracle (s3CommitReady message answer) message answer regs.2.1
    regs.2.2.1 regs.2.2.2.2.2.1 (s3_ready_value message answer) (s3_ready_seed message answer)
    (fun q above below outside => s3_ready_zero message answer q above below outside)).hashed index.val
    (lt_of_lt_of_eq index.isLt (by decide))
  unfold s6Slot at result
  rw [result, s6_digest_values oracle.permutation message (s4GenNonce oracle.permutation answer) index.val
    index.isLt]
  unfold s6LeafValues expandTaggedVector
  rw [dif_pos index.isLt]

/-- After the leaf phase, group slot `g` (heap node `2^22 + g`) holds the tree's group value. -/
theorem s3_leaves_group (oracle : Oracle) (message : Message) (answer : BitVec 256) (group : Nat)
    (inside : group < 2^22) :
    readBuffer (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
        (4429189152 + 32 * group) 32 =
      s6GroupValues oracle.permutation (s6LeafValues oracle.permutation message
        (expandTaggedVector (s4GenNonce oracle.permutation answer))) group := by
  have regs := s3_ready_registers message answer
  have result := (s3_leaves_generated oracle (s3CommitReady message answer) message answer regs.2.1
    regs.2.2.1 regs.2.2.2.2.2.1 (s3_ready_value message answer) (s3_ready_seed message answer)
    (fun q above below outside => s3_ready_zero message answer q above below outside)).grouped group inside
  rw [result]
  unfold s6GroupValues
  rw [s6_digest_values _ _ _ _ (by change 4 * group < 16777216; omega),
    s6_digest_values _ _ _ _ (by change 4 * group + 1 < 16777216; omega),
    s6_digest_values _ _ _ _ (by change 4 * group + 2 < 16777216; omega),
    s6_digest_values _ _ _ _ (by change 4 * group + 3 < 16777216; omega)]

/-- The nonce region after the leaf phase holds the generated nonces. -/
theorem s3_leaves_nonce (oracle : Oracle) (message : Message) (answer : BitVec 256) (index : Index) :
    readBuffer (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
        (6106911008 + 16 * index.val) 16 = s4GenNonce oracle.permutation answer index := by
  have regs := s3_ready_registers message answer
  have result := (s3_leaves_generated oracle (s3CommitReady message answer) message answer regs.2.1
    regs.2.2.1 regs.2.2.2.2.2.1 (s3_ready_value message answer) (s3_ready_seed message answer)
    (fun q above below outside => s3_ready_zero message answer q above below outside)).fresh index.val
    (lt_of_lt_of_eq index.isLt (by decide))
  rw [result, s6_wrap_eq index.val index.isLt]

end CommitGolfCandidate
