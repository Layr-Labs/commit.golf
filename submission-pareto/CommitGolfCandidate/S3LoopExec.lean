import CommitGolfCandidate.S3LeafExec
import CommitGolfCandidate.S4GenExec

/-! The leaf phase on the actual interpreter: per block of 64 leaves two cell-base instructions,
64 unrolled leaves, 16 group calls and five restore and latch instructions (759 instructions,
1,767 cycles, 144 queries); all 2^18 blocks; and the whole appended code before the parent sweep
(generator, seed-block clearing, leaf-phase setup, blocks). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### Leaves of a block -/

theorem s6_leaf_state_next (l : Nat) (state : MachineState) (window nonce cell : Nat)
    (first second : BitVec PERMUTATION_WIDTH) (invariant : S6LeafState state l window nonce cell)
    (pc : (s3LeafResult l state first second).pc = BitVec.ofNat 64 (1012276 + 44 * (l + 1)))
    (input : (s3LeafResult l state first second).getReg .x10 = BitVec.ofNat 64 (window + 256)) :
    S6LeafState (s3LeafResult l state first second) (l + 1) (window + 256) nonce cell := by
  have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h12 : reg ≠ .x12 := by decide) (h21 : reg ≠ .x21 := by decide) :=
    s3_leaf_result_register l state first second reg h6 h10 h12 h21
  exact ⟨pc, ⟨(kept .x5).trans invariant.ready.1, (kept .x11).trans invariant.ready.2.1,
    (kept .x13).trans invariant.ready.2.2⟩, input, (kept .x18).trans invariant.nonces,
    (kept .x23).trans invariant.cell23, (kept .x25).trans invariant.cell25,
    (kept .x27).trans invariant.cell27⟩

/-- Leaves `l, ..., l+count-1` of a block, all before the last one. -/
theorem s3_group_leaves_execute (count : Nat) :
    ∀ (l : Nat) (state : MachineState) (window nonce cell : Nat),
    l + count ≤ 63 → S6LeafState state l window nonce cell →
    window % 8 = 0 → nonce % 8 = 0 → cell % 8 = 0 → 56 ≤ window →
    window + 256 * count + 280 ≤ MEMORY_BYTES → nonce + 1024 ≤ MEMORY_BYTES →
    cell + 5888 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (11 * count + fuel) state true =
      (do let finished ← s3GroupLeaves state l count
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (25 * count) (2 * count)) ∧
    ∀ finished ∈ support (s3GroupLeaves state l count),
      S6LeafState finished (l + count) (window + 256 * count) nonce cell ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x21 →
        finished.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro l state window nonce cell _ invariant _ _ _ _ _ _ _ fuel
    refine ⟨by simp [s3GroupLeaves, Execution.charge], ?_⟩
    intro finished reachable
    simp only [s3GroupLeaves, support_pure, Set.mem_singleton_iff] at reachable
    subst reachable
    exact ⟨invariant, fun _ _ _ _ _ => rfl⟩
  | succ count ih =>
    intro l state window nonce cell inside invariant windowAligned nonceAligned cellAligned
      windowLow windowBound nonceBound cellBound fuel
    have leaf := s3_leaf_execute l (by omega) state window nonce cell invariant windowAligned
      nonceAligned cellAligned windowLow (by omega) (by omega) cellBound (11 * count + fuel)
    have next (first second : BitVec PERMUTATION_WIDTH) :
        S6LeafState (s3LeafResult l state first second) (l + 1) (window + 256) nonce cell :=
      s6_leaf_state_next l state window nonce cell first second invariant (leaf.2.1 first second)
        (by rw [leaf.2.2.2 first second, if_neg (by omega)])
    constructor
    · rw [show 11 * (count + 1) + fuel = 11 + (11 * count + fuel) by omega, leaf.1]
      simp only [s3GroupLeaves, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun reached reachable => ?_
      obtain ⟨first, second, rfl⟩ := s3_leaf_support l state reached reachable
      rw [(ih (l + 1) _ (window + 256) nonce cell (by omega) (next first second)
        (by omega) nonceAligned cellAligned (by omega) (by omega) nonceBound cellBound fuel).1]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun finished => ?_
      refine bind_congr fun result => ?_
      simp [Execution.charge]
      omega
    · intro finished reachable
      simp only [s3GroupLeaves, mem_support_bind_iff] at reachable
      obtain ⟨reached, reachedLeaf, rest⟩ := reachable
      obtain ⟨first, second, rfl⟩ := s3_leaf_support l state reached reachedLeaf
      have tail := (ih (l + 1) _ (window + 256) nonce cell (by omega) (next first second)
        (by omega) nonceAligned cellAligned (by omega) (by omega) nonceBound cellBound fuel).2
        finished rest
      refine ⟨?_, fun reg h6 h10 h12 h21 => (tail.2 reg h6 h10 h12 h21).trans
        (s3_leaf_result_register l state first second reg h6 h10 h12 h21)⟩
      rw [show l + (count + 1) = l + 1 + count by omega,
        show window + 256 * (count + 1) = window + 256 + 256 * count by omega]
      exact tail.1

/-- Pointers and fixed syscall arguments at a group call. -/
structure S6CallState (state : MachineState) (c cell group : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (1015092 + 12 * c)
  ready : S3PermReady state
  cell23 : state.getReg .x23 = BitVec.ofNat 64 cell
  cell25 : state.getReg .x25 = BitVec.ofNat 64 (cell + 1840)
  cell27 : state.getReg .x27 = BitVec.ofNat 64 (cell + 3680)
  groups : state.getReg .x24 = BitVec.ofNat 64 group

/-- Group calls `c, ..., c+count-1` of a block. -/
theorem s6_group_calls_execute (count : Nat) :
    ∀ (c : Nat) (state : MachineState) (cell group : Nat),
    c + count ≤ 16 → S6CallState state c cell group →
    cell % 8 = 0 → group % 8 = 0 → cell + 5888 ≤ MEMORY_BYTES → group + 680 ≤ MEMORY_BYTES →
    ∀ fuel : Nat,
    execute (submission.image .commit) (3 * count + fuel) state true =
      (do let finished ← s6GroupCalls state c count
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (10 * count) count) ∧
    ∀ finished ∈ support (s6GroupCalls state c count),
      S6CallState finished (c + count) cell group ∧
      ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → finished.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro c state cell group _ invariant _ _ _ _ fuel
    refine ⟨by simp [s6GroupCalls, Execution.charge], ?_⟩
    intro finished reachable
    simp only [s6GroupCalls, support_pure, Set.mem_singleton_iff] at reachable
    subst reachable
    exact ⟨invariant, fun _ _ _ => rfl⟩
  | succ count ih =>
    intro c state cell group inside invariant cellAligned groupAligned cellBound groupBound fuel
    have call := s6_group_call_execute c (by omega) state cell group invariant.pc invariant.ready
      invariant.cell23 invariant.cell25 invariant.cell27 invariant.groups cellAligned groupAligned
      cellBound groupBound (3 * count + fuel)
    have next (answer : BitVec PERMUTATION_WIDTH) :
        S6CallState (s6GroupCallResult c state answer) (c + 1) cell group := by
      have kept (reg : Reg) (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide) :=
        s6_group_call_result_register c state answer reg h10 h12
      exact ⟨call.2.1 answer, ⟨(kept .x5).trans invariant.ready.1,
        (kept .x11).trans invariant.ready.2.1, (kept .x13).trans invariant.ready.2.2⟩,
        (kept .x23).trans invariant.cell23, (kept .x25).trans invariant.cell25,
        (kept .x27).trans invariant.cell27, (kept .x24).trans invariant.groups⟩
    constructor
    · rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega, call.1]
      simp only [s6GroupCalls, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun reached reachable => ?_
      obtain ⟨answer, rfl⟩ := s6_group_call_support c state reached reachable
      rw [(ih (c + 1) _ cell group (by omega) (next answer) cellAligned groupAligned cellBound
        groupBound fuel).1]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun finished => ?_
      refine bind_congr fun result => ?_
      simp [Execution.charge]
      omega
    · intro finished reachable
      simp only [s6GroupCalls, mem_support_bind_iff] at reachable
      obtain ⟨reached, reachedCall, rest⟩ := reachable
      obtain ⟨answer, rfl⟩ := s6_group_call_support c state reached reachedCall
      have tail := (ih (c + 1) _ cell group (by omega) (next answer) cellAligned groupAligned
        cellBound groupBound fuel).2 finished rest
      refine ⟨by rw [show c + (count + 1) = c + 1 + count by omega]; exact tail.1,
        fun reg h10 h12 => (tail.2 reg h10 h12).trans
          (s6_group_call_result_register c state answer reg h10 h12)⟩

/-! ### One block -/

/-- Pointers at the start of a block (PC 1012268). -/
structure S6BlockState (state : MachineState) (window nonce cell group : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 1012268
  ready : S3PermReady state
  input : state.getReg .x10 = BitVec.ofNat 64 window
  nonces : state.getReg .x18 = BitVec.ofNat 64 nonce
  cell23 : state.getReg .x23 = BitVec.ofNat 64 cell
  groups : state.getReg .x24 = BitVec.ofNat 64 group

theorem s6_block_base_register (state : MachineState) (reg : Reg) (h25 : reg ≠ .x25) (h27 : reg ≠ .x27) :
    (s6BlockBase state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h25 | exact absurd rfl h27 | rfl

theorem s3_latch_register (state : MachineState) (reg : Reg) (h10 : reg ≠ .x10) (h18 : reg ≠ .x18)
    (h23 : reg ≠ .x23) (h24 : reg ≠ .x24) :
    (s3LatchState state).getReg reg = state.getReg reg := by
  have branch (current : MachineState) :
      (execInstrBr current (.BLTU .x24 .x22 (BitVec.ofNat 13 5160))).getReg reg = current.getReg reg := by
    simp only [execInstrBr]
    split <;> simp only [MachineState.getReg_setPC]
  show (execInstrBr (([.ADDI .x10 .x21 0, .ADDI .x18 .x18 1024, .ADDI .x24 .x24 512, .ADD .x23 .x23 .x7] :
    List Instr).foldl execInstrBr state) (.BLTU .x24 .x22 (BitVec.ofNat 13 5160))).getReg reg = _
  rw [branch]
  cases reg <;> first | exact absurd rfl h10 | exact absurd rfl h18 | exact absurd rfl h23 |
    exact absurd rfl h24 | rfl

/-- The four pointer updates of the latch, before its branch. -/
def s3LatchAdvance (state : MachineState) : MachineState :=
  ([.ADDI .x10 .x21 0, .ADDI .x18 .x18 1024, .ADDI .x24 .x24 512, .ADD .x23 .x23 .x7] : List Instr).foldl
    execInstrBr state

theorem s3_latch_advance_kept (state : MachineState) :
    (s3LatchAdvance state).getReg .x22 = state.getReg .x22 := rfl

theorem s3_latch_state (state : MachineState) :
    s3LatchState state = execInstrBr (s3LatchAdvance state) (.BLTU .x24 .x22 (BitVec.ofNat 13 5160)) := rfl

theorem s3_latch_branch_register (state : MachineState) (reg : Reg) :
    (execInstrBr state (.BLTU .x24 .x22 (BitVec.ofNat 13 5160))).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.getReg_setPC]

/-- The group-node branch returns to the block start exactly while group nodes remain. -/
theorem s3_branch_pc (state : MachineState) (group finish : Nat)
    (pc : state.pc = BitVec.ofNat 64 1015300)
    (groups : state.getReg .x24 = BitVec.ofNat 64 group)
    (limit : state.getReg .x22 = BitVec.ofNat 64 finish)
    (groupBound : group < 2 ^ 64) (finishBound : finish < 2 ^ 64) :
    (execInstrBr state (.BLTU .x24 .x22 (BitVec.ofNat 13 5160))).pc =
      BitVec.ofNat 64 (if group < finish then 1012268 else 1015304) := by
  have compared : BitVec.ult (state.getReg .x24) (state.getReg .x22) = decide (group < finish) := by
    rw [groups, limit]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt groupBound,
      Nat.mod_eq_of_lt finishBound]
  simp only [execInstrBr, compared, pc]
  by_cases taken : group < finish
  · simp only [taken, decide_true, ↓reduceIte]
    rfl
  · simp only [taken, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

set_option maxHeartbeats 16000000 in
/-- One block: cell bases, 64 leaves, 16 group calls, restore and latch: 759 instructions,
1767 cycles, 144 queries. -/
theorem s3_group_execute (state : MachineState) (window nonce cell group finish : Nat)
    (invariant : S6BlockState state window nonce cell group)
    (stride : state.getReg .x7 = BitVec.ofNat 64 5888)
    (limit : state.getReg .x22 = BitVec.ofNat 64 finish)
    (windowAligned : window % 8 = 0) (nonceAligned : nonce % 8 = 0) (cellAligned : cell % 8 = 0)
    (groupAligned : group % 8 = 0) (windowLow : 56 ≤ window)
    (windowBound : window + 16384 + 280 ≤ MEMORY_BYTES) (nonceBound : nonce + 1024 ≤ MEMORY_BYTES)
    (cellBound : cell + 5888 ≤ MEMORY_BYTES) (groupBound : group + 680 ≤ MEMORY_BYTES)
    (finishBound : finish ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (759 + fuel) state true =
      (do let next ← s3Group state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge 1767 144) ∧
    ∀ next ∈ support (s3Group state),
      next.pc = BitVec.ofNat 64 (if group + 512 < finish then 1012268 else 1015304) ∧
      S3PermReady next ∧
      next.getReg .x10 = BitVec.ofNat 64 (window + 16384) ∧
      next.getReg .x18 = BitVec.ofNat 64 (nonce + 1024) ∧
      next.getReg .x23 = BitVec.ofNat 64 (cell + 5888) ∧
      next.getReg .x24 = BitVec.ofNat 64 (group + 512) ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 → reg ≠ .x21 → reg ≠ .x23 →
        reg ≠ .x24 → reg ≠ .x25 → reg ≠ .x27 → next.getReg reg = state.getReg reg := by
  -- cell bases
  have bases := s3_straight_execute (submission.image .commit) s6BlockBaseInstructions 2 1012268 state
    (11 * 63 + (11 + (3 * 16 + (4 + (1 + fuel))))) true rfl invariant.pc (by decide)
    (fun k bound current currentPC => s6_image_block_base k bound current currentPC)
    (fun k bound => by interval_cases k <;> rfl)
  have basesRun : execute (submission.image .commit) (2 + (11 * 63 + (11 + (3 * 16 + (4 + (1 + fuel))))))
      state true =
      (do let result ← execute (submission.image .commit) (11 * 63 + (11 + (3 * 16 + (4 + (1 + fuel)))))
            (s6BlockBase state) true
          return result.charge 2 0) := bases.1
  have basesKept (reg : Reg) (h25 : reg ≠ .x25 := by decide) (h27 : reg ≠ .x27 := by decide) :
      (s6BlockBase state).getReg reg = state.getReg reg :=
    s6_block_base_register state reg h25 h27
  have base25 : (s6BlockBase state).getReg .x25 = BitVec.ofNat 64 (cell + 1840) := by
    show state.getReg .x23 + signExtend12 1840 = _
    rw [invariant.cell23, show signExtend12 (1840 : BitVec 12) = BitVec.ofNat 64 1840 from rfl,
      ← BitVec.ofNat_add]
  have base27 : (s6BlockBase state).getReg .x27 = BitVec.ofNat 64 (cell + 3680) := by
    show state.getReg .x23 + signExtend12 1840 + signExtend12 1840 = _
    rw [invariant.cell23, show signExtend12 (1840 : BitVec 12) = BitVec.ofNat 64 1840 from rfl,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    all_goals first | rfl | (congr 1; omega)
  have entered : S6LeafState (s6BlockBase state) 0 window nonce cell :=
    ⟨bases.2, ⟨(basesKept .x5).trans invariant.ready.1, (basesKept .x11).trans invariant.ready.2.1,
      (basesKept .x13).trans invariant.ready.2.2⟩, (basesKept .x10).trans invariant.input,
      (basesKept .x18).trans invariant.nonces, (basesKept .x23).trans invariant.cell23, base25, base27⟩
  -- leaves 0..62
  have leaves := s3_group_leaves_execute 63 0 (s6BlockBase state) window nonce cell (by decide) entered
    windowAligned nonceAligned cellAligned windowLow (by norm_num <;> omega) nonceBound cellBound
    (11 + (3 * 16 + (4 + (1 + fuel))))
  -- leaf 63
  have last (early : MachineState) (reached : early ∈ support (s3GroupLeaves (s6BlockBase state) 0 63)) :=
    s3_leaf_execute 63 (by decide) early (window + 256 * 63) nonce cell
      (by simpa using (leaves.2 early reached).1) (by norm_num <;> omega) nonceAligned cellAligned
      (by norm_num <;> omega) (by norm_num <;> omega) (by norm_num <;> omega) cellBound
      (3 * 16 + (4 + (1 + fuel)))
  -- the whole computation of leaves
  have allLeaves : s3GroupLeaves (s6BlockBase state) 0 64 =
      (do let early ← s3GroupLeaves (s6BlockBase state) 0 63; s3Leaf 63 early) := by
    have split (count : Nat) : ∀ (current : MachineState) (l : Nat),
        s3GroupLeaves current l (count + 1) =
          (do let early ← s3GroupLeaves current l count; s3Leaf (l + count) early) := by
      induction count with
      | zero =>
        intro current l
        simp [s3GroupLeaves]
      | succ count ih =>
        intro current l
        rw [s3GroupLeaves]
        conv_rhs => rw [s3GroupLeaves]
        rw [bind_assoc]
        refine bind_congr fun next => ?_
        rw [ih next (l + 1), show l + 1 + count = l + (count + 1) by omega]
    simpa using split 63 (s6BlockBase state) 0
  -- group calls
  have callState (early : MachineState) (reached : early ∈ support (s3GroupLeaves (s6BlockBase state) 0 63))
      (first second : BitVec PERMUTATION_WIDTH) :
      S6CallState (s3LeafResult 63 early first second) 0 cell group := by
    have known := (leaves.2 early reached)
    have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
        (h12 : reg ≠ .x12 := by decide) (h21 : reg ≠ .x21 := by decide) :
        (s3LeafResult 63 early first second).getReg reg = (s6BlockBase state).getReg reg :=
      (s3_leaf_result_register 63 early first second reg h6 h10 h12 h21).trans (known.2 reg h6 h10 h12 h21)
    exact ⟨((last early reached).2.1 first second).trans (by norm_num), ⟨(kept .x5).trans entered.ready.1,
      (kept .x11).trans entered.ready.2.1, (kept .x13).trans entered.ready.2.2⟩,
      (kept .x23).trans entered.cell23, (kept .x25).trans entered.cell25, (kept .x27).trans entered.cell27,
      (kept .x24).trans ((basesKept .x24).trans invariant.groups)⟩
  have calls (early : MachineState) (reached : early ∈ support (s3GroupLeaves (s6BlockBase state) 0 63))
      (first second : BitVec PERMUTATION_WIDTH) :=
    s6_group_calls_execute 16 0 (s3LeafResult 63 early first second) cell group (by decide)
      (callState early reached first second) cellAligned groupAligned cellBound groupBound (4 + (1 + fuel))
  -- latch
  have latch (grouped : MachineState) (pc : grouped.pc = BitVec.ofNat 64 (1015092 + 12 * (0 + 16))) :=
    s3_straight_execute (submission.image .commit)
      ([.ADDI .x10 .x21 0, .ADDI .x18 .x18 1024, .ADDI .x24 .x24 512, .ADD .x23 .x23 .x7] : List Instr) 4
      1015284 grouped (1 + fuel) true rfl (pc.trans (by norm_num)) (by decide)
      (fun k bound current currentPC => by
        have fetched := s3_image_latch k (by omega) current currentPC
        interval_cases k <;> exact fetched)
      (fun k bound => by interval_cases k <;> rfl)
  constructor
  · rw [show 759 + fuel = 2 + (11 * 63 + (11 + (3 * 16 + (4 + (1 + fuel))))) by ring, basesRun,
      leaves.1]
    simp only [s3Group, allLeaves, bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun early reached => ?_
    rw [(last early reached).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun leaf leafReached => ?_
    obtain ⟨first, second, rfl⟩ := s3_leaf_support 63 early leaf leafReached
    rw [(calls early reached first second).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun grouped groupedReached => ?_
    have groupedPC := ((calls early reached first second).2 grouped groupedReached).1.pc
    have latchRun : execute (submission.image .commit) (4 + (1 + fuel)) grouped true =
        (do let result ← execute (submission.image .commit) (1 + fuel) (s3LatchAdvance grouped) true
            return result.charge 4 0) := (latch grouped groupedPC).1
    have branchRun : execute (submission.image .commit) (fuel + 1) (s3LatchAdvance grouped) true =
        (do let result ← execute (submission.image .commit) fuel (s3LatchState grouped) true
            return result.charge 1 0) :=
      execute_ordinary_step (submission.image .commit) (.base (.BLTU .x24 .x22 (BitVec.ofNat 13 5160)))
        (s3LatchAdvance grouped) (s3LatchState grouped) fuel true
        (s3_image_latch 4 (by decide) _ ((latch grouped groupedPC).2)) rfl
    rw [latchRun, Nat.add_comm 1 fuel, branchRun]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · intro next reachable
    simp only [s3Group, allLeaves, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨leaf, ⟨early, reached, leafReached⟩, grouped, groupedReached, rfl⟩ := reachable
    obtain ⟨first, second, rfl⟩ := s3_leaf_support 63 early leaf leafReached
    have knownLeaves := leaves.2 early reached
    have knownCalls := (calls early reached first second).2 grouped groupedReached
    have callsKept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
        (h12 : reg ≠ .x12 := by decide) (h21 : reg ≠ .x21 := by decide) (h25 : reg ≠ .x25 := by decide)
        (h27 : reg ≠ .x27 := by decide) : grouped.getReg reg = state.getReg reg :=
      (knownCalls.2 reg h10 h12).trans ((s3_leaf_result_register 63 early first second reg h6 h10 h12 h21).trans
        ((knownLeaves.2 reg h6 h10 h12 h21).trans (basesKept reg h25 h27)))
    have advancePC : (s3LatchAdvance grouped).pc = BitVec.ofNat 64 1015300 :=
      (latch grouped knownCalls.1.pc).2
    have parked : grouped.getReg .x21 = BitVec.ofNat 64 (window + 16384) := by
      have next := (last early reached).2.2.1 first second
      have register : s3LeafNextRegister 63 = .x21 := rfl
      rw [register] at next
      exact (knownCalls.2 .x21 (by decide) (by decide)).trans
        (next.trans (congrArg (BitVec.ofNat 64) (by ring)))
    have advance10 : (s3LatchAdvance grouped).getReg .x10 = BitVec.ofNat 64 (window + 16384) := by
      show grouped.getReg .x21 + signExtend12 0 = _
      rw [parked, show signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 from rfl, ← BitVec.ofNat_add]
    have advance18 : (s3LatchAdvance grouped).getReg .x18 = BitVec.ofNat 64 (nonce + 1024) := by
      show grouped.getReg .x18 + signExtend12 1024 = _
      rw [callsKept .x18, invariant.nonces, show signExtend12 (1024 : BitVec 12) = BitVec.ofNat 64 1024 from rfl,
        ← BitVec.ofNat_add]
    have advance24 : (s3LatchAdvance grouped).getReg .x24 = BitVec.ofNat 64 (group + 512) := by
      show grouped.getReg .x24 + signExtend12 512 = _
      rw [knownCalls.1.groups, show signExtend12 (512 : BitVec 12) = BitVec.ofNat 64 512 from rfl,
        ← BitVec.ofNat_add]
    have advance23 : (s3LatchAdvance grouped).getReg .x23 = BitVec.ofNat 64 (cell + 5888) := by
      show grouped.getReg .x23 + grouped.getReg .x7 = _
      rw [knownCalls.1.cell23, callsKept .x7, stride, ← BitVec.ofNat_add]
    have finalKept (reg : Reg) (h10 : reg ≠ .x10) (h18 : reg ≠ .x18) (h23 : reg ≠ .x23) (h24 : reg ≠ .x24) :
        (s3LatchState grouped).getReg reg = grouped.getReg reg :=
      s3_latch_register grouped reg h10 h18 h23 h24
    refine ⟨?_, ⟨(finalKept .x5 (by decide) (by decide) (by decide) (by decide)).trans
        ((callsKept .x5).trans invariant.ready.1),
      (finalKept .x11 (by decide) (by decide) (by decide) (by decide)).trans
        ((callsKept .x11).trans invariant.ready.2.1),
      (finalKept .x13 (by decide) (by decide) (by decide) (by decide)).trans
        ((callsKept .x13).trans invariant.ready.2.2)⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [s3_latch_state]
      exact s3_branch_pc _ (group + 512) finish advancePC advance24
        ((s3_latch_advance_kept grouped).trans ((callsKept .x22).trans limit))
        (by dsimp [MEMORY_BYTES] at groupBound; omega) (by dsimp [MEMORY_BYTES] at finishBound; omega)
    · rw [s3_latch_state, s3_latch_branch_register]
      exact advance10
    · rw [s3_latch_state, s3_latch_branch_register]
      exact advance18
    · rw [s3_latch_state, s3_latch_branch_register]
      exact advance23
    · rw [s3_latch_state, s3_latch_branch_register]
      exact advance24
    · intro reg h6 h10 h12 h18 h21 h23 h24 h25 h27
      rw [finalKept reg h10 h18 h23 h24]
      exact callsKept reg h6 h10 h12 h21 h25 h27


/-! ### All blocks -/

/-- All blocks: the latch falls through to the parent setup (PC 1015304) after the last group node. -/
theorem s3_groups_execute (groups : Nat) :
    ∀ (state : MachineState) (window nonce cell group finish : Nat),
    S6BlockState state window nonce cell group →
    state.getReg .x7 = BitVec.ofNat 64 5888 → state.getReg .x22 = BitVec.ofNat 64 finish →
    group + 512 * (groups + 1) = finish →
    window % 8 = 0 → nonce % 8 = 0 → cell % 8 = 0 → group % 8 = 0 → 56 ≤ window →
    window + 16384 * (groups + 1) + 280 ≤ MEMORY_BYTES → nonce + 1024 * (groups + 1) ≤ MEMORY_BYTES →
    cell + 5888 * (groups + 1) ≤ MEMORY_BYTES → finish + 168 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (759 * (groups + 1) + fuel) state true =
      (do let finished ← s3Groups state (groups + 1)
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (1767 * (groups + 1)) (144 * (groups + 1))) ∧
    ∀ finished ∈ support (s3Groups state (groups + 1)),
      finished.pc = BitVec.ofNat 64 1015304 ∧ S3PermReady finished ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 → reg ≠ .x21 → reg ≠ .x23 →
        reg ≠ .x24 → reg ≠ .x25 → reg ≠ .x27 → finished.getReg reg = state.getReg reg := by
  induction groups with
  | zero =>
    intro state window nonce cell group finish invariant stride limit full windowAligned nonceAligned
      cellAligned groupAligned windowLow windowBound nonceBound cellBound finishBound fuel
    have block := s3_group_execute state window nonce cell group finish invariant stride limit
      windowAligned nonceAligned cellAligned groupAligned windowLow (by omega) (by omega) (by omega)
      (by omega) (by omega) fuel
    constructor
    · rw [show 759 * (0 + 1) + fuel = 759 + fuel by omega, block.1]
      simp only [s3Groups, bind_assoc, pure_bind]
    · intro finished reachable
      simp only [s3Groups, bind_pure] at reachable
      have known := block.2 finished reachable
      refine ⟨?_, known.2.1, known.2.2.2.2.2.2⟩
      rw [known.1, if_neg (by omega)]
  | succ groups ih =>
    intro state window nonce cell group finish invariant stride limit full windowAligned nonceAligned
      cellAligned groupAligned windowLow windowBound nonceBound cellBound finishBound fuel
    have block := s3_group_execute state window nonce cell group finish invariant stride limit
      windowAligned nonceAligned cellAligned groupAligned windowLow (by omega) (by omega) (by omega)
      (by omega) (by omega) (759 * (groups + 1) + fuel)
    have continued (next : MachineState) (reached : next ∈ support (s3Group state)) :=
      ih next (window + 16384) (nonce + 1024) (cell + 5888) (group + 512) finish
        ⟨by rw [(block.2 next reached).1, if_pos (by omega)], (block.2 next reached).2.1,
          (block.2 next reached).2.2.1, (block.2 next reached).2.2.2.1,
          (block.2 next reached).2.2.2.2.1, (block.2 next reached).2.2.2.2.2.1⟩
        (((block.2 next reached).2.2.2.2.2.2 .x7 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans stride)
        (((block.2 next reached).2.2.2.2.2.2 .x22 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) finishBound fuel
    constructor
    · rw [show 759 * (groups + 1 + 1) + fuel = 759 + (759 * (groups + 1) + fuel) by omega, block.1]
      simp only [s3Groups, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun next reached => ?_
      rw [(continued next reached).1]
      simp only [s3Groups, bind_assoc, pure_bind]
      refine bind_congr fun following => ?_
      refine bind_congr fun finished => ?_
      refine bind_congr fun result => ?_
      simp [Execution.charge]
      omega
    · intro finished reachable
      rw [s3Groups] at reachable
      simp only [mem_support_bind_iff] at reachable
      obtain ⟨next, reached, rest⟩ := reachable
      have tail := (continued next reached).2 finished rest
      exact ⟨tail.1, tail.2.1, fun reg h6 h10 h12 h18 h21 h23 h24 h25 h27 =>
        (tail.2.2 reg h6 h10 h12 h18 h21 h23 h24 h25 h27).trans
          ((block.2 next reached).2.2.2.2.2.2 reg h6 h10 h12 h18 h21 h23 h24 h25 h27)⟩

/-! ### The appended code before the parent sweep -/

theorem s6_gen_clear_register (state : MachineState) (reg : Reg) :
    (s6GenClear state).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem s6_gen_clear_pc (state : MachineState) : (s6GenClear state).pc = state.pc + 4 + 4 + 4 + 4 + 4 :=
  rfl

theorem s6_leaf_setup_register (state : MachineState) (reg : Reg) (h7 : reg ≠ .x7) (h10 : reg ≠ .x10)
    (h18 : reg ≠ .x18) (h22 : reg ≠ .x22) (h23 : reg ≠ .x23) (h24 : reg ≠ .x24) :
    (s6LeafSetup state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h7 | exact absurd rfl h10 | exact absurd rfl h18 |
    exact absurd rfl h22 | exact absurd rfl h23 | exact absurd rfl h24 | rfl

theorem s6_lui_28 : (((65536 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 =
    BitVec.ofNat 64 268435456 := by
  decide

theorem s6_lui_27 : (((32768 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 =
    BitVec.ofNat 64 134217728 := by
  decide

theorem s6_lui_1 : (((1 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 =
    BitVec.ofNat 64 4096 := by
  decide

/-- Registers after the leaf-phase setup, for the trapdoor base `heap` (x9), the loop bound
`heap + 1811939560` (x6) and the message `source` (x8). -/
theorem s6_leaf_setup_values (state : MachineState) (heap source : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (bound : state.getReg .x6 = BitVec.ofNat 64 (heap + 1811939560))
    (message : state.getReg .x8 = BitVec.ofNat 64 source) (low : 24 ≤ source) :
    (s6LeafSetup state).getReg .x18 = BitVec.ofNat 64 (heap + 1811939584) ∧
    (s6LeafSetup state).getReg .x22 = BitVec.ofNat 64 (heap + 268435456) ∧
    (s6LeafSetup state).getReg .x23 = BitVec.ofNat 64 (heap + 268435712) ∧
    (s6LeafSetup state).getReg .x24 = BitVec.ofNat 64 (heap + 134217728) ∧
    (s6LeafSetup state).getReg .x7 = BitVec.ofNat 64 5888 ∧
    (s6LeafSetup state).getReg .x10 = BitVec.ofNat 64 (source - 24) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show state.getReg .x6 + signExtend12 24 = _
    rw [bound, show signExtend12 (24 : BitVec 12) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add]
    all_goals first | rfl | (congr 1; omega)
  · show state.getReg .x9 + (((65536 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 = _
    rw [base, s6_lui_28, ← BitVec.ofNat_add]
  · show state.getReg .x9 + (((65536 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 +
      signExtend12 256 = _
    rw [base, s6_lui_28, show signExtend12 (256 : BitVec 12) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    all_goals first | rfl | (congr 1; omega)
  · show state.getReg .x9 + (((32768 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 = _
    rw [base, s6_lui_27, ← BitVec.ofNat_add]
  · show (((1 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 + signExtend12 1792 = _
    rw [s6_lui_1, show signExtend12 (1792 : BitVec 12) = BitVec.ofNat 64 1792 from rfl, ← BitVec.ofNat_add]
    all_goals first | rfl | (congr 1; omega)
  · show state.getReg .x8 + signExtend12 (BitVec.ofNat 12 4072) = _
    rw [message, show signExtend12 (BitVec.ofNat 12 4072) = BitVec.ofNat 64 (2 ^ 64 - 24) by decide]
    exact s4_ofNat_sub source 24 low (by decide)

set_option maxHeartbeats 16000000 in
/-- **The appended code before the parent sweep**, from PC 1011404 to PC 1015304: the generator
(`9 + 193 * 23832` instructions), the seed-block clearing (5), the leaf-phase setup (9) and the
2^18 blocks (759 each). -/
theorem s3_leaves_execute (state : MachineState) (source seed heap : Nat)
    (pc : state.pc = BitVec.ofNat 64 1011404) (selector : state.getReg .x5 = 0)
    (message : state.getReg .x8 = BitVec.ofNat 64 source)
    (seedReg : state.getReg .x18 = BitVec.ofNat 64 seed)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (sourceAligned : source % 8 = 0) (seedAligned : seed % 8 = 0) (heapAligned : heap % 8 = 0)
    (sourceLow : 80 ≤ source) (seedLow : 168 ≤ seed)
    (sourceBound : source + 2 ^ 33 ≤ MEMORY_BYTES) (seedBound : seed + 32 ≤ MEMORY_BYTES)
    (heapBound : heap + 2 ^ 31 ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (9 + 193 * 23832 + 14 + 759 * 2 ^ 18 + fuel) state true =
      (do let leaves ← s3Leaves state (2 ^ 18)
          let result ← execute (submission.image .commit) fuel leaves true
          return result.charge (9 + 641 * 23832 + 14 + 1767 * 2 ^ 18) (1525248 + 144 * 2 ^ 18)) ∧
    ∀ leaves ∈ support (s3Leaves state (2 ^ 18)),
      leaves.pc = BitVec.ofNat 64 1015304 ∧ leaves.getReg .x5 = 0 ∧
      leaves.getReg .x22 = BitVec.ofNat 64 (heap + 2 ^ 28) ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x12 → reg ≠ .x13 →
        reg ≠ .x18 → reg ≠ .x21 → reg ≠ .x22 → reg ≠ .x23 → reg ≠ .x24 → reg ≠ .x25 → reg ≠ .x27 →
        leaves.getReg reg = state.getReg reg := by
  have heapBound' : heap + 2147483648 ≤ MEMORY_BYTES := Eq.trans_le (by norm_num) heapBound
  have sourceBound' : source + 8589934592 ≤ MEMORY_BYTES := Eq.trans_le (by norm_num) sourceBound
  have generator := s4_generator_execute state seed heap (14 + 759 * 2 ^ 18 + fuel) pc selector
    seedReg base seedAligned heapAligned seedLow seedBound
    (le_trans (Nat.add_le_add_left (show 2080383232 ≤ 2147483648 by norm_num) heap) heapBound')
  have filledKept (filled : MachineState) (reached : filled ∈ support (s4Generator state 23832))
      (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h11 : reg ≠ .x11 := by decide) (h12 : reg ≠ .x12 := by decide)
      (h13 : reg ≠ .x13 := by decide) : filled.getReg reg = state.getReg reg :=
    (generator.2 filled reached).2.2.2.2 reg h6 h10 h11 h12 h13
  have clear (filled : MachineState) (reached : filled ∈ support (s4Generator state 23832)) :=
    s3_straight_execute (submission.image .commit) s6GenClearInstructions 5 1012212 filled
      (9 + (759 * 2 ^ 18 + fuel)) true rfl (generator.2 filled reached).1 (by decide)
      (fun k bound current currentPC => s6_image_clear k bound current currentPC)
      (fun k bound => by
        have input := (generator.2 filled reached).2.2.1
        interval_cases k
        · exact s3_access_valid _ _ (seed - 168) 0 input rfl (by omega) (by decide) (by omega)
        · exact s3_access_valid _ _ (seed - 168) 168 input rfl (by omega) (by decide) (by omega)
        · exact s3_access_valid _ _ (seed - 168) 176 input rfl (by omega) (by decide) (by omega)
        · exact s3_access_valid _ _ (seed - 168) 184 input rfl (by omega) (by decide) (by omega)
        · exact s3_access_valid _ _ (seed - 168) 192 input rfl (by omega) (by decide) (by omega))
  have setup (filled : MachineState) (reached : filled ∈ support (s4Generator state 23832)) :=
    s3_straight_execute (submission.image .commit) s6LeafSetupInstructions 9 1012232 (s6GenClear filled)
      (759 * 2 ^ 18 + fuel) true rfl ((clear filled reached).2) (by decide)
      (fun k bound current currentPC => s6_image_leaf_setup k bound current currentPC)
      (fun k bound => by interval_cases k <;> rfl)
  have values (filled : MachineState) (reached : filled ∈ support (s4Generator state 23832)) :=
    s6_leaf_setup_values (s6GenClear filled) heap source
      ((s6_gen_clear_register filled .x9).trans ((filledKept filled reached .x9).trans base))
      ((s6_gen_clear_register filled .x6).trans (generator.2 filled reached).2.2.2.1)
      ((s6_gen_clear_register filled .x8).trans ((filledKept filled reached .x8).trans message))
      (by omega)
  have setupKept (filled : MachineState) (reached : filled ∈ support (s4Generator state 23832))
      (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h7 : reg ≠ .x7 := by decide)
      (h10 : reg ≠ .x10 := by decide) (h11 : reg ≠ .x11 := by decide) (h12 : reg ≠ .x12 := by decide)
      (h13 : reg ≠ .x13 := by decide) (h18 : reg ≠ .x18 := by decide) (h22 : reg ≠ .x22 := by decide)
      (h23 : reg ≠ .x23 := by decide) (h24 : reg ≠ .x24 := by decide) :
      (s6LeafSetup (s6GenClear filled)).getReg reg = state.getReg reg :=
    (s6_leaf_setup_register _ reg h7 h10 h18 h22 h23 h24).trans
      ((s6_gen_clear_register filled reg).trans (filledKept filled reached reg h6 h10 h11 h12 h13))
  have ready (filled : MachineState) (reached : filled ∈ support (s4Generator state 23832)) :
      S3PermReady (s6LeafSetup (s6GenClear filled)) :=
    ⟨(setupKept filled reached .x5).trans selector,
      ((s6_leaf_setup_register _ .x11 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans (s6_gen_clear_register filled .x11)).trans (generator.2 filled reached).2.1.2.1,
      ((s6_leaf_setup_register _ .x13 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans (s6_gen_clear_register filled .x13)).trans (generator.2 filled reached).2.1.2.2⟩
  have full : heap + 134217728 + 512 * (262143 + 1) = heap + 268435456 := by ring
  have windowEnd : source - 24 + 16384 * (262143 + 1) + 280 ≤ MEMORY_BYTES :=
    le_trans (by rw [show (16384 * (262143 + 1) : Nat) = 4294967296 from rfl]; omega :
      source - 24 + 16384 * (262143 + 1) + 280 ≤ source + 8589934592) sourceBound'
  have within (n : Nat) (small : n ≤ 2147483648) : heap + n ≤ MEMORY_BYTES :=
    le_trans (Nat.add_le_add_left small heap) heapBound'
  have nonceEnd : heap + 1811939584 + 1024 * (262143 + 1) ≤ MEMORY_BYTES :=
    Eq.trans_le (by ring : heap + 1811939584 + 1024 * (262143 + 1) = heap + 2080375040)
      (within _ (by norm_num))
  have cellEnd : heap + 268435712 + 5888 * (262143 + 1) ≤ MEMORY_BYTES :=
    Eq.trans_le (by ring : heap + 268435712 + 5888 * (262143 + 1) = heap + 1811939584)
      (within _ (by norm_num))
  have finishEnd : heap + 268435456 + 168 ≤ MEMORY_BYTES :=
    Eq.trans_le (by ring : heap + 268435456 + 168 = heap + 268435624) (within _ (by norm_num))
  have blocks (filled : MachineState) (reached : filled ∈ support (s4Generator state 23832)) :=
    s3_groups_execute 262143 (s6LeafSetup (s6GenClear filled)) (source - 24) (heap + 1811939584)
      (heap + 268435712) (heap + 134217728) (heap + 268435456)
      ⟨(setup filled reached).2, ready filled reached, (values filled reached).2.2.2.2.2,
        (values filled reached).1, (values filled reached).2.2.1, (values filled reached).2.2.2.1⟩
      (values filled reached).2.2.2.2.1 (values filled reached).2.1
      full (by omega) (by omega) (by omega) (by omega) (by omega)
      windowEnd nonceEnd cellEnd finishEnd fuel
  have groupCount : (262143 + 1 : Nat) = 2 ^ 18 := by norm_num
  rw [groupCount] at blocks
  constructor
  · rw [show 9 + 193 * 23832 + 14 + 759 * 2 ^ 18 + fuel = 9 + 193 * 23832 + (14 + 759 * 2 ^ 18 + fuel) by ring,
      generator.1]
    simp only [s3Leaves, bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun filled reached => ?_
    have clearRun : execute (submission.image .commit) (5 + (9 + (759 * 2 ^ 18 + fuel))) filled true =
        (do let result ← execute (submission.image .commit) (9 + (759 * 2 ^ 18 + fuel)) (s6GenClear filled) true
            return result.charge 5 0) := (clear filled reached).1
    have setupRun : execute (submission.image .commit) (9 + (759 * 2 ^ 18 + fuel)) (s6GenClear filled) true =
        (do let result ← execute (submission.image .commit) (759 * 2 ^ 18 + fuel)
              (s6LeafSetup (s6GenClear filled)) true
            return result.charge 9 0) := (setup filled reached).1
    rw [show 14 + 759 * 2 ^ 18 + fuel = 5 + (9 + (759 * 2 ^ 18 + fuel)) by ring, clearRun]
    simp only [bind_assoc, pure_bind]
    rw [setupRun]
    simp only [bind_assoc, pure_bind]
    rw [(blocks filled reached).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun leaves => ?_
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · intro leaves reachable
    simp only [s3Leaves, mem_support_bind_iff] at reachable
    obtain ⟨filled, reached, hashed⟩ := reachable
    have known := (blocks filled reached).2 leaves hashed
    have kept (reg : Reg) (h6 : reg ≠ .x6) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) (h18 : reg ≠ .x18)
        (h21 : reg ≠ .x21) (h23 : reg ≠ .x23) (h24 : reg ≠ .x24) (h25 : reg ≠ .x25) (h27 : reg ≠ .x27) :
        leaves.getReg reg = (s6LeafSetup (s6GenClear filled)).getReg reg :=
      known.2.2 reg h6 h10 h12 h18 h21 h23 h24 h25 h27
    refine ⟨known.1, (kept .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans (ready filled reached).1,
      ((kept .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)).trans (values filled reached).2.1).trans
        (congrArg (BitVec.ofNat 64) (by norm_num)),
      fun reg h6 h7 h10 h11 h12 h13 h18 h21 h22 h23 h24 h25 h27 =>
        (kept reg h6 h10 h12 h18 h21 h23 h24 h25 h27).trans
          (setupKept filled reached reg h6 h7 h10 h11 h12 h13 h18 h22 h23 h24)⟩

end CommitGolfCandidate
