import CommitGolfCandidate.S3LeafMemory
import CommitGolfCandidate.S3ReadyMemory
import CommitGolfCandidate.S3LoopExec

/-! Stage-3 commitment: fixed-oracle memory refinement of the whole appended leaf phase.
Every leaf slot receives the stage-3 digest of its message entry under its nonce. The
last leaf's 200-byte reply covers nonces 0..6; the repair copies them back from the
consumed message windows, so the nonce region is the sampled one again. -/
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

/-! ### Registers and query counts, for every state -/

theorem s3_group_leaves_register (oracle : Oracle) (count : Nat) :
    ∀ (unit : Nat) (state : MachineState) (reg : Reg), reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 →
    (checkEvaluation oracle (s3GroupLeaves state unit count)).1.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro unit state reg _ _ _
    rw [s3GroupLeaves, s3_evaluation_pure_state]
  | succ count ih =>
    intro unit state reg h6 h10 h12
    rw [s3GroupLeaves, s3_evaluation_state, ih (unit + 1) _ reg h6 h10 h12,
      s3_leaf_register oracle unit state reg h6 h10 h12]

theorem s3_group_leaves_queries (oracle : Oracle) (count : Nat) :
    ∀ (unit : Nat) (state : MachineState),
    (checkEvaluation oracle (s3GroupLeaves state unit count)).2 = 2 * count := by
  induction count with
  | zero =>
    intro unit state
    rw [s3GroupLeaves, s3_evaluation_pure_calls]
  | succ count ih =>
    intro unit state
    rw [s3GroupLeaves, s3_evaluation_calls, s3_leaf_queries, ih]
    omega

theorem s3_group_state (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s3Group state)).1 =
      s3LatchState (checkEvaluation oracle (s3GroupLeaves state 0 64)).1 := by
  rw [s3Group, s3_evaluation_state, s3_evaluation_pure_state]

theorem s3_group_register (oracle : Oracle) (state : MachineState) (reg : Reg)
    (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) (h18 : reg ≠ .x18)
    (h23 : reg ≠ .x23) :
    (checkEvaluation oracle (s3Group state)).1.getReg reg = state.getReg reg := by
  rw [s3_group_state, s3_latch_register _ reg h18 h23,
    s3_group_leaves_register oracle 64 0 state reg h6 h10 h12]

theorem s3_group_queries (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s3Group state)).2 = 128 := by
  rw [s3Group, s3_evaluation_calls, s3_evaluation_pure_calls, s3_group_leaves_queries]

theorem s3_groups_register (oracle : Oracle) (count : Nat) :
    ∀ (state : MachineState) (reg : Reg), reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 →
    reg ≠ .x23 → (checkEvaluation oracle (s3Groups state count)).1.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro state reg _ _ _ _ _
    rw [s3Groups, s3_evaluation_pure_state]
  | succ count ih =>
    intro state reg h6 h10 h12 h18 h23
    rw [s3Groups, s3_evaluation_state, ih _ reg h6 h10 h12 h18 h23,
      s3_group_register oracle state reg h6 h10 h12 h18 h23]

theorem s3_groups_queries (oracle : Oracle) (count : Nat) :
    ∀ state : MachineState, (checkEvaluation oracle (s3Groups state count)).2 = 128 * count := by
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
      s3FinishState (checkEvaluation oracle (s3Groups (s3EntryState state) groups)).1 := by
  rw [s3Leaves, s3_evaluation_state, s3_evaluation_pure_state]

/-- The leaf phase makes two permutation queries per leaf. -/
theorem s3_leaves_queries (oracle : Oracle) (state : MachineState) (groups : Nat) :
    (checkEvaluation oracle (s3Leaves state groups)).2 = 128 * groups := by
  rw [s3Leaves, s3_evaluation_calls, s3_evaluation_pure_calls, s3_groups_queries]
  omega

/-- Registers the parent phase and the root copy read. -/
theorem s3_leaves_register (oracle : Oracle) (state : MachineState) (groups : Nat) (reg : Reg)
    (member : reg ∈ [Reg.x9, .x19, .x26]) :
    (checkEvaluation oracle (s3Leaves state groups)).1.getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rw [s3_leaves_state]
  rcases member with rfl | rfl | rfl <;>
    rw [s3_finish_register _ _ (by decide) (by decide) (by decide),
      s3_groups_register oracle groups _ _ (by decide) (by decide) (by decide) (by decide)
        (by decide),
      s3_entry_register _ _ (by decide) (by decide) (by decide) (by decide)]

/-! ### Loop invariant -/

/-- Message entries, leaf slots and nonces, in increasing address order. -/
structure S3Layout (source slots nonces total : Nat) : Prop where
  low : 32 ≤ source
  sourceAligned : source % 8 = 0
  slotsAligned : slots % 8 = 0
  sourceEnd : source + 256 * total ≤ slots
  slotsEnd : slots + 32 * total = nonces
  noncesEnd : nonces + 24 * total ≤ 2 ^ 64
  large : 13 ≤ total

/-- Memory after `done` leaves: unread entries, written digests, nonces not yet
reached by a reply, and the nonce copies the repair will read. -/
structure S3Progress (oracle : Oracle) (source slots nonces total : Nat)
    (message : Nat → Entry) (salts : Nat → BitVec 192) (state : MachineState) (done : Nat) :
    Prop where
  pending : ∀ i, done ≤ i → i < total → readBuffer state (source + 256 * i) 256 = message i
  hashed : ∀ i, i < done → readBuffer state (slots + 32 * i) 32 =
    s3LeafDigest oracle.permutation (expandNonce192 (salts i)) (message i)
  fresh : ∀ i, i < total → 7 ≤ i ∨ done ≤ i → readBuffer state (nonces + 24 * i) 24 = salts i
  saved : ∀ i, i < done → i < 7 → readBuffer state (source + 256 * i + 56) 24 = salts i

theorem s3_progress_memory (oracle : Oracle) (source slots nonces total : Nat)
    (message : Nat → Entry) (salts : Nat → BitVec 192) (left right : MachineState) (done : Nat)
    (same : right.mem = left.mem)
    (progress : S3Progress oracle source slots nonces total message salts left done) :
    S3Progress oracle source slots nonces total message salts right done :=
  ⟨fun i after below => (s3_read_memory right left same _ _).trans (progress.pending i after below),
    fun i before => (s3_read_memory right left same _ _).trans (progress.hashed i before),
    fun i below condition => (s3_read_memory right left same _ _).trans
      (progress.fresh i below condition),
    fun i before first => (s3_read_memory right left same _ _).trans (progress.saved i before first)⟩

set_option maxHeartbeats 16000000 in
/-- One leaf extends the invariant. -/
theorem s3_progress_leaf (oracle : Oracle) (source slots nonces total : Nat)
    (message : Nat → Entry) (salts : Nat → BitVec 192)
    (layout : S3Layout source slots nonces total) (state : MachineState) (group unit : Nat)
    (small : unit < 64) (inside : 64 * group + unit < total)
    (input : state.getReg .x10 = BitVec.ofNat 64 (source + 256 * (64 * group + unit)))
    (noncePointer : state.getReg .x18 = BitVec.ofNat 64 (nonces + 1536 * group))
    (slotPointer : state.getReg .x23 = BitVec.ofNat 64 (slots + 2048 * group))
    (progress : S3Progress oracle source slots nonces total message salts state
      (64 * group + unit)) :
    S3Progress oracle source slots nonces total message salts
      (checkEvaluation oracle (s3Leaf unit state)).1 (64 * group + unit + 1) := by
  obtain ⟨low, sourceAligned, slotsAligned, sourceEnd, slotsEnd, noncesEnd, large⟩ := layout
  have frame : S3LeafFrame state unit (source + 256 * (64 * group + unit))
      (nonces + 1536 * group) (slots + 2048 * group) :=
    ⟨input, noncePointer, slotPointer, small, by omega, by omega, by omega, by omega, by omega,
      by omega, Or.inr (by omega)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i after below
    rw [s3_leaf_preserves oracle unit state (source + 256 * (64 * group + unit))
      (nonces + 1536 * group) (slots + 2048 * group) (source + 256 * i) 256 frame (by omega)
      (Or.inr (by omega)) (Or.inl (by omega))]
    exact progress.pending i (by omega) below
  · intro i before
    by_cases last : i = 64 * group + unit
    · subst last
      have digest := s3_leaf_digest oracle unit state (source + 256 * (64 * group + unit))
        (nonces + 1536 * group) (slots + 2048 * group)
        (expandNonce192 (salts (64 * group + unit))) (message (64 * group + unit)) frame
        (by
          rw [read_nonce_buffer, s3_read_address state (nonces + 1536 * group + 24 * unit)
            (nonces + 24 * (64 * group + unit)) 24 (by omega),
            progress.fresh _ inside (Or.inr (Nat.le_refl _))])
        (by
          exact progress.pending _ (Nat.le_refl _) inside)
      rw [s3_read_address _ (slots + 32 * (64 * group + unit))
        (slots + 2048 * group + 32 * unit) 32 (by omega)]
      exact digest
    · rw [s3_leaf_preserves oracle unit state (source + 256 * (64 * group + unit))
        (nonces + 1536 * group) (slots + 2048 * group) (slots + 32 * i) 32 frame (by omega)
        (Or.inr (by omega)) (Or.inl (by omega))]
      exact progress.hashed i (by omega)
  · intro i below condition
    rw [s3_leaf_preserves oracle unit state (source + 256 * (64 * group + unit))
      (nonces + 1536 * group) (slots + 2048 * group) (nonces + 24 * i) 24 frame (by omega)
      (Or.inr (by omega)) (Or.inr (by rcases condition with seven | later <;> omega))]
    exact progress.fresh i below (by rcases condition with seven | later <;> omega)
  · intro i before first
    by_cases last : i = 64 * group + unit
    · subst last
      have copy := s3_leaf_nonce_copy oracle unit state (source + 256 * (64 * group + unit))
        (nonces + 1536 * group) (slots + 2048 * group) frame (Or.inl (by omega))
      rw [copy,
        s3_read_address state (nonces + 1536 * group + 24 * unit)
          (nonces + 24 * (64 * group + unit)) 24 (by omega)]
      exact progress.fresh _ inside (Or.inr (Nat.le_refl _))
    · rw [s3_leaf_preserves oracle unit state (source + 256 * (64 * group + unit))
        (nonces + 1536 * group) (slots + 2048 * group) (source + 256 * i + 56) 24 frame
        (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
      exact progress.saved i (by omega) first

/-- The leaves of one group, from leaf `unit` on. -/
theorem s3_progress_group_leaves (oracle : Oracle) (source slots nonces total : Nat)
    (message : Nat → Entry) (salts : Nat → BitVec 192)
    (layout : S3Layout source slots nonces total) (group count : Nat) :
    ∀ (unit : Nat) (state : MachineState), unit + count ≤ 64 →
    64 * group + unit + count ≤ total →
    state.getReg .x10 = BitVec.ofNat 64 (source + 256 * (64 * group + unit)) →
    state.getReg .x18 = BitVec.ofNat 64 (nonces + 1536 * group) →
    state.getReg .x23 = BitVec.ofNat 64 (slots + 2048 * group) →
    S3Progress oracle source slots nonces total message salts state (64 * group + unit) →
    S3Progress oracle source slots nonces total message salts
      (checkEvaluation oracle (s3GroupLeaves state unit count)).1 (64 * group + unit + count) ∧
    (checkEvaluation oracle (s3GroupLeaves state unit count)).1.getReg .x10 =
      BitVec.ofNat 64 (source + 256 * (64 * group + unit + count)) := by
  induction count with
  | zero =>
    intro unit state _ _ input _ _ progress
    rw [s3GroupLeaves, s3_evaluation_pure_state]
    exact ⟨progress, input⟩
  | succ count ih =>
    intro unit state small inside input noncePointer slotPointer progress
    have step := s3_progress_leaf oracle source slots nonces total message salts layout state
      group unit (by omega) (by omega) input noncePointer slotPointer progress
    have advanced : (checkEvaluation oracle (s3Leaf unit state)).1.getReg .x10 =
        BitVec.ofNat 64 (source + 256 * (64 * group + (unit + 1))) := by
      rw [s3_leaf_input oracle unit state _ input]
      congr 1 <;> omega
    have next := ih (unit + 1) (checkEvaluation oracle (s3Leaf unit state)).1 (by omega)
      (by omega) advanced
      ((s3_leaf_register oracle unit state .x18 (by decide) (by decide) (by decide)).trans
        noncePointer)
      ((s3_leaf_register oracle unit state .x23 (by decide) (by decide) (by decide)).trans
        slotPointer)
      step
    rw [s3GroupLeaves, s3_evaluation_state,
      show 64 * group + unit + (count + 1) = 64 * group + (unit + 1) + count by omega]
    exact next

theorem s3_latch_memory (state : MachineState) : (s3LatchState state).mem = state.mem := by
  rw [s3_latch_state]
  simp only [execInstrBr]
  split <;> rfl

theorem s3_latch_nonces (state : MachineState) :
    (s3LatchState state).getReg .x18 = state.getReg .x18 + signExtend12 1536 := by
  rw [s3_latch_state, s3_branch_register]
  rfl

theorem s3_latch_slots (state : MachineState) :
    (s3LatchState state).getReg .x23 = state.getReg .x23 + state.getReg .x7 := by
  rw [s3_latch_state, s3_branch_register]
  rfl

/-- One group: 64 leaves, then the two pointer advances of the latch. -/
theorem s3_progress_group (oracle : Oracle) (source slots nonces total : Nat)
    (message : Nat → Entry) (salts : Nat → BitVec 192)
    (layout : S3Layout source slots nonces total) (group : Nat) (state : MachineState)
    (inside : 64 * (group + 1) ≤ total)
    (input : state.getReg .x10 = BitVec.ofNat 64 (source + 256 * (64 * group)))
    (noncePointer : state.getReg .x18 = BitVec.ofNat 64 (nonces + 1536 * group))
    (slotPointer : state.getReg .x23 = BitVec.ofNat 64 (slots + 2048 * group))
    (stride : state.getReg .x7 = BitVec.ofNat 64 2048)
    (progress : S3Progress oracle source slots nonces total message salts state (64 * group)) :
    S3Progress oracle source slots nonces total message salts
      (checkEvaluation oracle (s3Group state)).1 (64 * (group + 1)) ∧
    (checkEvaluation oracle (s3Group state)).1.getReg .x10 =
      BitVec.ofNat 64 (source + 256 * (64 * (group + 1))) ∧
    (checkEvaluation oracle (s3Group state)).1.getReg .x18 =
      BitVec.ofNat 64 (nonces + 1536 * (group + 1)) ∧
    (checkEvaluation oracle (s3Group state)).1.getReg .x23 =
      BitVec.ofNat 64 (slots + 2048 * (group + 1)) ∧
    (checkEvaluation oracle (s3Group state)).1.getReg .x7 = BitVec.ofNat 64 2048 := by
  have leaves := s3_progress_group_leaves oracle source slots nonces total message salts layout
    group 64 0 state (by omega) (by omega) input noncePointer slotPointer progress
  have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h12 : reg ≠ .x12 := by decide) :
      (checkEvaluation oracle (s3GroupLeaves state 0 64)).1.getReg reg = state.getReg reg :=
    s3_group_leaves_register oracle 64 0 state reg h6 h10 h12
  rw [s3_group_state]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have moved := s3_progress_memory oracle source slots nonces total message salts _
      (s3LatchState (checkEvaluation oracle (s3GroupLeaves state 0 64)).1) _
      (s3_latch_memory _) leaves.1
    rw [show 64 * (group + 1) = 64 * group + 0 + 64 by omega]
    exact moved
  · rw [s3_latch_register _ .x10 (by decide) (by decide), leaves.2]
    congr 1 <;> omega
  · rw [s3_latch_nonces, kept .x18, noncePointer,
      show signExtend12 (1536 : BitVec 12) = BitVec.ofNat 64 1536 from rfl, ← BitVec.ofNat_add]
    congr 1 <;> omega
  · rw [s3_latch_slots, kept .x23, kept .x7, slotPointer, stride, ← BitVec.ofNat_add]
    congr 1 <;> omega
  · rw [s3_latch_register _ .x7 (by decide) (by decide), kept .x7]
    exact stride

/-- All remaining groups. -/
theorem s3_progress_groups (oracle : Oracle) (source slots nonces total : Nat)
    (message : Nat → Entry) (salts : Nat → BitVec 192)
    (layout : S3Layout source slots nonces total) (count : Nat) :
    ∀ (group : Nat) (state : MachineState), 64 * (group + count) ≤ total →
    state.getReg .x10 = BitVec.ofNat 64 (source + 256 * (64 * group)) →
    state.getReg .x18 = BitVec.ofNat 64 (nonces + 1536 * group) →
    state.getReg .x23 = BitVec.ofNat 64 (slots + 2048 * group) →
    state.getReg .x7 = BitVec.ofNat 64 2048 →
    S3Progress oracle source slots nonces total message salts state (64 * group) →
    S3Progress oracle source slots nonces total message salts
      (checkEvaluation oracle (s3Groups state count)).1 (64 * (group + count)) := by
  induction count with
  | zero =>
    intro group state _ _ _ _ _ progress
    rw [s3Groups, s3_evaluation_pure_state]
    exact progress
  | succ count ih =>
    intro group state inside input noncePointer slotPointer stride progress
    have step := s3_progress_group oracle source slots nonces total message salts layout group
      state (by omega) input noncePointer slotPointer stride progress
    have next := ih (group + 1) (checkEvaluation oracle (s3Group state)).1 (by omega)
      step.2.1 step.2.2.1 step.2.2.2.1 step.2.2.2.2 step.1
    rw [s3Groups, s3_evaluation_state,
      show group + (count + 1) = group + 1 + count by omega]
    exact next

/-! ### Nonce repair -/

/-- Memory after the first `pair` load/store pairs of the repair. -/
def s3RepairWords (state : MachineState) (source nonces : Word) : Nat → MachineState
  | 0 => state
  | pair + 1 =>
      s3CopyWord (s3RepairWords state source nonces pair)
        (source + signExtend12 (BitVec.ofNat 12 (256 * (pair / 3) + 56 + 8 * (pair % 3))))
        (nonces + signExtend12 (BitVec.ofNat 12 (8 * pair)))

/-- The first `pair` load/store pairs of the repair. -/
def s3RepairPrefix : Nat → List Instr
  | 0 => []
  | pair + 1 => s3RepairPrefix pair ++
      [.LD .x6 .x8 (BitVec.ofNat 12 (256 * (pair / 3) + 56 + 8 * (pair % 3))),
       .SD .x22 .x6 (BitVec.ofNat 12 (8 * pair))]

theorem s3_repair_instructions : s3RepairInstructions = s3RepairPrefix 21 := rfl

theorem s3_repair_pair (state : MachineState) (load store : BitVec 12) :
    (([.LD .x6 .x8 load, .SD .x22 .x6 store] : List Instr).foldl execInstrBr state).mem =
      (s3CopyWord state (state.getReg .x8 + signExtend12 load)
        (state.getReg .x22 + signExtend12 store)).mem ∧
    (([.LD .x6 .x8 load, .SD .x22 .x6 store] : List Instr).foldl execInstrBr state).getReg .x8 =
      state.getReg .x8 ∧
    (([.LD .x6 .x8 load, .SD .x22 .x6 store] : List Instr).foldl execInstrBr state).getReg .x22 =
      state.getReg .x22 :=
  ⟨rfl, rfl, rfl⟩

theorem s3_copy_memory (left right : MachineState) (source destination : Word)
    (same : left.mem = right.mem) :
    (s3CopyWord left source destination).mem = (s3CopyWord right source destination).mem := by
  unfold s3CopyWord
  simp only [MachineState.setMem, MachineState.getMem, same]

theorem s3_repair_prefix_memory (count : Nat) : ∀ state : MachineState,
    ((s3RepairPrefix count).foldl execInstrBr state).mem =
      (s3RepairWords state (state.getReg .x8) (state.getReg .x22) count).mem ∧
    ((s3RepairPrefix count).foldl execInstrBr state).getReg .x8 = state.getReg .x8 ∧
    ((s3RepairPrefix count).foldl execInstrBr state).getReg .x22 = state.getReg .x22 := by
  induction count with
  | zero =>
    intro state
    exact ⟨rfl, rfl, rfl⟩
  | succ count ih =>
    intro state
    obtain ⟨memory, message, limit⟩ := ih state
    have pair := s3_repair_pair ((s3RepairPrefix count).foldl execInstrBr state)
      (BitVec.ofNat 12 (256 * (count / 3) + 56 + 8 * (count % 3))) (BitVec.ofNat 12 (8 * count))
    rw [s3RepairPrefix, List.foldl_append]
    refine ⟨?_, pair.2.1.trans message, pair.2.2.trans limit⟩
    rw [pair.1, message, limit, s3RepairWords]
    exact s3_copy_memory _ _ _ _ memory

theorem s3_exit_memory (state : MachineState) :
    (s3ExitInstructions.foldl execInstrBr state).mem = state.mem := rfl

theorem s3_finish_memory (state : MachineState) :
    (s3FinishState state).mem =
      (s3RepairWords state (state.getReg .x8) (state.getReg .x22) 21).mem := by
  rw [s3FinishState, List.foldl_append, s3_exit_memory, s3_repair_instructions]
  exact (s3_repair_prefix_memory 21 state).1

theorem s3_repair_offset (pair : Nat) (small : pair < 21) :
    signExtend12 (BitVec.ofNat 12 (256 * (pair / 3) + 56 + 8 * (pair % 3))) =
      BitVec.ofNat 64 (256 * (pair / 3) + 56 + 8 * (pair % 3)) ∧
    signExtend12 (BitVec.ofNat 12 (8 * pair)) = BitVec.ofNat 64 (8 * pair) := by
  interval_cases pair <;> exact ⟨rfl, rfl⟩

/-- After `count` pairs, the first `8 * count` nonce bytes are the saved copies. -/
theorem s3_repair_byte (state : MachineState) (source nonces : Nat)
    (sourceAligned : source % 8 = 0) (noncesAligned : nonces % 8 = 0)
    (separate : source + 1616 ≤ nonces) (bound : nonces + 168 ≤ 2 ^ 64) (count : Nat)
    (bounded : count ≤ 21) :
    ∀ query : Nat, query < 2 ^ 64 →
    (s3RepairWords state (BitVec.ofNat 64 source) (BitVec.ofNat 64 nonces) count).getByte
        (BitVec.ofNat 64 query) =
      if nonces ≤ query ∧ query < nonces + 8 * count then
        state.getByte (BitVec.ofNat 64
          (source + 256 * ((query - nonces) / 24) + 56 + (query - nonces) % 24))
      else state.getByte (BitVec.ofNat 64 query) := by
  induction count with
  | zero =>
    intro query _
    rw [if_neg (by omega)]
    rfl
  | succ count ih =>
    intro query queryBound
    have offsets := s3_repair_offset count (by omega)
    show (s3CopyWord (s3RepairWords state (BitVec.ofNat 64 source) (BitVec.ofNat 64 nonces) count)
      (BitVec.ofNat 64 source +
        signExtend12 (BitVec.ofNat 12 (256 * (count / 3) + 56 + 8 * (count % 3))))
      (BitVec.ofNat 64 nonces + signExtend12 (BitVec.ofNat 12 (8 * count)))).getByte _ = _
    rw [s3_address (BitVec.ofNat 64 source) source (256 * (count / 3) + 56 + 8 * (count % 3)) _ rfl
        offsets.1,
      s3_address (BitVec.ofNat 64 nonces) nonces (8 * count) _ rfl offsets.2,
      s3_copy_byte _ (source + (256 * (count / 3) + 56 + 8 * (count % 3))) (nonces + 8 * count)
        query (by omega) (by omega) (by omega) queryBound]
    by_cases copied : nonces + 8 * count ≤ query ∧ query < nonces + 8 * count + 8
    · rw [if_pos copied, if_pos (show nonces ≤ query ∧ query < nonces + 8 * (count + 1) by omega),
        ih (by omega) (source + (256 * (count / 3) + 56 + 8 * (count % 3)) +
          (query - (nonces + 8 * count))) (by omega),
        if_neg (show ¬ (nonces ≤ source + (256 * (count / 3) + 56 + 8 * (count % 3)) +
            (query - (nonces + 8 * count)) ∧
          source + (256 * (count / 3) + 56 + 8 * (count % 3)) + (query - (nonces + 8 * count)) <
            nonces + 8 * count) by omega)]
      exact s3_byte_address state _ _ (by omega)
    · rw [if_neg copied, ih (by omega) query queryBound]
      by_cases earlier : nonces ≤ query ∧ query < nonces + 8 * count
      · rw [if_pos earlier,
          if_pos (show nonces ≤ query ∧ query < nonces + 8 * (count + 1) by omega)]
      · rw [if_neg earlier,
          if_neg (show ¬ (nonces ≤ query ∧ query < nonces + 8 * (count + 1)) by omega)]

/-- Bytes after the repair and exit: nonce bytes `[0,168)` come from the message windows. -/
theorem s3_finish_byte (state : MachineState) (source nonces query : Nat)
    (message : state.getReg .x8 = BitVec.ofNat 64 source)
    (limit : state.getReg .x22 = BitVec.ofNat 64 nonces)
    (sourceAligned : source % 8 = 0) (noncesAligned : nonces % 8 = 0)
    (separate : source + 1616 ≤ nonces) (bound : nonces + 168 ≤ 2 ^ 64)
    (queryBound : query < 2 ^ 64) :
    (s3FinishState state).getByte (BitVec.ofNat 64 query) =
      if nonces ≤ query ∧ query < nonces + 168 then
        state.getByte (BitVec.ofNat 64
          (source + 256 * ((query - nonces) / 24) + 56 + (query - nonces) % 24))
      else state.getByte (BitVec.ofNat 64 query) := by
  rw [s3_byte_memory _ _ (s3_finish_memory state), message, limit]
  exact s3_repair_byte state source nonces sourceAligned noncesAligned separate bound 21
    (by decide) query queryBound

/-! ### The whole leaf phase -/

set_option maxHeartbeats 16000000 in
/-- Leaf slots hold the digests and the nonce region holds the sampled nonces. -/
theorem s3_leaves_memory (oracle : Oracle) (source slots nonces total groups : Nat)
    (message : Nat → Entry) (salts : Nat → BitVec 192)
    (layout : S3Layout source slots nonces total) (size : 64 * groups = total)
    (state : MachineState)
    (input : state.getReg .x10 = BitVec.ofNat 64 (source - 32))
    (messagePointer : state.getReg .x8 = BitVec.ofNat 64 source)
    (noncePointer : state.getReg .x18 = BitVec.ofNat 64 nonces)
    (limit : state.getReg .x22 = BitVec.ofNat 64 nonces)
    (slotPointer : state.getReg .x23 = BitVec.ofNat 64 slots)
    (entries : ∀ i, i < total → readBuffer state (source + 256 * i) 256 = message i)
    (sampled : ∀ i, i < total → readBuffer state (nonces + 24 * i) 24 = salts i) :
    ∀ i, i < total →
      readBuffer (checkEvaluation oracle (s3Leaves state groups)).1 (slots + 32 * i) 32 =
        s3LeafDigest oracle.permutation (expandNonce192 (salts i)) (message i) ∧
      readBuffer (checkEvaluation oracle (s3Leaves state groups)).1 (nonces + 24 * i) 24 =
        salts i := by
  have ⟨low, sourceAligned, slotsAligned, sourceEnd, slotsEnd, noncesEnd, large⟩ := layout
  have start : S3Progress oracle source slots nonces total message salts (s3EntryState state) 0 :=
    s3_progress_memory oracle source slots nonces total message salts state _ 0 rfl
      ⟨fun i _ below => entries i below, fun i before => absurd before (Nat.not_lt_zero i),
        fun i below _ => sampled i below, fun i before _ => absurd before (Nat.not_lt_zero i)⟩
  have entered : (s3EntryState state).getReg .x10 =
      BitVec.ofNat 64 (source + 256 * (64 * 0)) := by
    show state.getReg .x10 + signExtend12 32 = _
    rw [input, show signExtend12 (32 : BitVec 12) = BitVec.ofNat 64 32 from rfl,
      ← BitVec.ofNat_add]
    congr 1
    omega
  have hashed := s3_progress_groups oracle source slots nonces total message salts layout groups
    0 (s3EntryState state) (by omega) entered
    ((s3_entry_register state .x18 (by decide) (by decide) (by decide) (by decide)).trans
      noncePointer)
    ((s3_entry_register state .x23 (by decide) (by decide) (by decide) (by decide)).trans
      slotPointer)
    rfl start
  rw [show 64 * (0 + groups) = total by omega] at hashed
  have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h7 : reg ≠ .x7 := by decide)
      (h10 : reg ≠ .x10 := by decide) (h11 : reg ≠ .x11 := by decide)
      (h12 : reg ≠ .x12 := by decide) (h13 : reg ≠ .x13 := by decide)
      (h18 : reg ≠ .x18 := by decide) (h23 : reg ≠ .x23 := by decide) :
      (checkEvaluation oracle (s3Groups (s3EntryState state) groups)).1.getReg reg =
        state.getReg reg :=
    (s3_groups_register oracle groups _ reg h6 h10 h12 h18 h23).trans
      (s3_entry_register state reg h7 h10 h11 h13)
  have byte (query : Nat) (queryBound : query < 2 ^ 64) :=
    s3_finish_byte (checkEvaluation oracle (s3Groups (s3EntryState state) groups)).1 source
      nonces query ((kept .x8).trans messagePointer) ((kept .x22).trans limit) sourceAligned
      (by omega) (by omega) (by omega) queryBound
  intro i below
  rw [s3_leaves_state]
  constructor
  · rw [s3_read_congr _ (checkEvaluation oracle (s3Groups (s3EntryState state) groups)).1
      (slots + 32 * i) (slots + 32 * i) 32 (fun j hj => by
        rw [byte (slots + 32 * i + j) (by omega),
          if_neg (show ¬ (nonces ≤ slots + 32 * i + j ∧ slots + 32 * i + j < nonces + 168) by
            omega)])]
    exact hashed.hashed i below
  · by_cases first : i < 7
    · rw [s3_read_congr _ (checkEvaluation oracle (s3Groups (s3EntryState state) groups)).1
        (nonces + 24 * i) (source + 256 * i + 56) 24 (fun j hj => by
          rw [byte (nonces + 24 * i + j) (by omega),
            if_pos (show nonces ≤ nonces + 24 * i + j ∧ nonces + 24 * i + j < nonces + 168 by
              omega)]
          exact s3_byte_address _ _ _ (by omega))]
      exact hashed.saved i below first
    · rw [s3_read_congr _ (checkEvaluation oracle (s3Groups (s3EntryState state) groups)).1
        (nonces + 24 * i) (nonces + 24 * i) 24 (fun j hj => by
          rw [byte (nonces + 24 * i + j) (by omega),
            if_neg (show ¬ (nonces ≤ nonces + 24 * i + j ∧ nonces + 24 * i + j < nonces + 168) by
              omega)])]
      exact hashed.fresh i below (Or.inl (by omega))

/-! ### The actual commitment state -/

theorem s3_ready_layout : S3Layout 4096 4831842336 5368713248 (2 ^ 24) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Leaf slots and nonce region after the actual leaf phase, by natural leaf index. -/
theorem s3_leaves_ready (oracle : Oracle) (message : Message) (answer : BitVec (192*LENGTH))
    (index : Index) :
    readBuffer (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
        (4831842336+32*index.val) 32 =
      s3LeafDigest oracle.permutation
        (expandNonce192 (answer.extractLsb' (192*index.val) 192)) (message index) ∧
    readBuffer (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
        (5368713248+24*index.val) 24 = answer.extractLsb' (192*index.val) 192 := by
  let wrap (i : Nat) : Index := ⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩
  have wrapped (i : Nat) (inside : i < LENGTH) : (wrap i).val = i := Nat.mod_eq_of_lt inside
  have regs := s3_ready_registers message answer
  have result := s3_leaves_memory oracle 4096 4831842336 5368713248 (2 ^ 24) (2 ^ 18)
    (fun i => message (wrap i)) (fun i => answer.extractLsb' (192*i) 192) s3_ready_layout
    (by decide) (s3CommitReady message answer) regs.1 regs.2.1 regs.2.2.1 regs.2.2.2.1
    regs.2.2.2.2.1
    (fun i below => by
      have loaded := s3_ready_value message answer (wrap i)
      rw [wrapped i below] at loaded
      exact loaded)
    (fun i below => by
      have loaded := s3_ready_nonce message answer (wrap i)
      rw [wrapped i below] at loaded
      exact loaded)
    index.val index.isLt
  have same : wrap index.val = index := Fin.ext (wrapped index.val index.isLt)
  simpa only [same] using result

/-- After all 2^24 actual leaf iterations and the repair, each heap leaf is the stage-3
digest of that exact input entry under its sampled nonce. -/
theorem s3_leaves_digest (oracle : Oracle) (message : Message) (answer : BitVec (192*LENGTH))
    (index : Index) :
    readBuffer (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
      (4831842336+32*index.val) 32 =
      s3LeafDigest oracle.permutation
        (expandNonce192 (answer.extractLsb' (192*index.val) 192)) (message index) :=
  (s3_leaves_ready oracle message answer index).1

/-- The nonce region after the leaf phase is the sampled one, including nonces 0..6. -/
theorem s3_leaves_salt (oracle : Oracle) (message : Message) (answer : BitVec (192*LENGTH))
    (index : Index) :
    readNonce (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
      (5368713248+24*index.val) = expandNonce192 (answer.extractLsb' (192*index.val) 192) := by
  rw [read_nonce_buffer, (s3_leaves_ready oracle message answer index).2]

end CommitGolfCandidate
