import CommitGolfCandidate.S3LeafExec

/-! The stage-3 leaf phase on the actual interpreter: 64 unrolled leaves and a latch per
group, all groups, then the nonce repair and the exit jump to parent setup. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Pointers and fixed syscall arguments at leaf `u` of a group. -/
structure S3GroupState (state : MachineState) (segment u cursor nonce heap : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (s3SegmentPC segment + 56 * u)
  ready : S3PermReady state
  input : state.getReg .x10 = BitVec.ofNat 64 cursor
  nonces : state.getReg .x18 = BitVec.ofNat 64 nonce
  slots : state.getReg .x23 = BitVec.ofNat 64 heap

theorem s3_group_leaves_execute (segment : Nat) (hs : segment < 8) (count : Nat) :
    ∀ (u : Nat) (state : MachineState) (cursor nonce heap : Nat),
    u + count ≤ 64 → S3GroupState state segment u cursor nonce heap →
    cursor % 8 = 0 → nonce % 8 = 0 → heap % 8 = 0 →
    cursor + 256 * count + 16 ≤ MEMORY_BYTES → nonce + 1536 ≤ MEMORY_BYTES →
    heap + 2216 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (14 * count + fuel) state true =
      (do let finished ← s3GroupLeaves state u count
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (28 * count) (2 * count)) ∧
    ∀ finished ∈ support (s3GroupLeaves state u count),
      S3GroupState finished segment (u + count) (cursor + 256 * count) nonce heap ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 →
        finished.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro u state cursor nonce heap _ invariant _ _ _ _ _ _ fuel
    refine ⟨by simp [s3GroupLeaves, Execution.charge], ?_⟩
    intro finished reachable
    simp only [s3GroupLeaves, support_pure, Set.mem_singleton_iff] at reachable
    subst reachable
    exact ⟨invariant, fun _ _ _ _ => rfl⟩
  | succ count ih =>
    intro u state cursor nonce heap inside invariant cursorAligned nonceAligned heapAligned
      cursorBound nonceBound heapBound fuel
    have leaf := s3_leaf_execute segment hs u (by omega) state cursor nonce heap invariant.pc
      invariant.ready invariant.input invariant.nonces invariant.slots cursorAligned
      nonceAligned heapAligned (by omega) (by omega) (by omega) (14 * count + fuel)
    have preserved (first second : BitVec PERMUTATION_WIDTH) (reg : Reg)
        (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
        (h12 : reg ≠ .x12 := by decide) :
        (s3LeafResult u state first second).getReg reg = state.getReg reg :=
      s3_leaf_result_register u state first second reg h6 h10 h12
    have next (first second : BitVec PERMUTATION_WIDTH) :
        S3GroupState (s3LeafResult u state first second) segment (u + 1) (cursor + 256) nonce heap :=
      ⟨leaf.2.1 first second,
        ⟨(preserved first second .x5).trans invariant.ready.1,
          (preserved first second .x11).trans invariant.ready.2.1,
          (preserved first second .x13).trans invariant.ready.2.2⟩,
        leaf.2.2 first second, (preserved first second .x18).trans invariant.nonces,
        (preserved first second .x23).trans invariant.slots⟩
    constructor
    · rw [show 14 * (count + 1) + fuel = 14 + (14 * count + fuel) by omega, leaf.1]
      simp only [s3GroupLeaves, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun reached reachable => ?_
      obtain ⟨first, second, rfl⟩ := s3_leaf_support u state reached reachable
      rw [(ih (u + 1) _ (cursor + 256) nonce heap (by omega) (next first second)
        (by omega) nonceAligned heapAligned (by omega) nonceBound heapBound fuel).1]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun finished => ?_
      refine bind_congr fun result => ?_
      simp [Execution.charge]
      omega
    · intro finished reachable
      simp only [s3GroupLeaves, mem_support_bind_iff] at reachable
      obtain ⟨reached, reachedLeaf, rest⟩ := reachable
      obtain ⟨first, second, rfl⟩ := s3_leaf_support u state reached reachedLeaf
      have tail := (ih (u + 1) _ (cursor + 256) nonce heap (by omega) (next first second)
        (by omega) nonceAligned heapAligned (by omega) nonceBound heapBound fuel).2 finished rest
      refine ⟨?_, fun reg h6 h10 h12 => (tail.2 reg h6 h10 h12).trans
        (preserved first second reg h6 h10 h12)⟩
      rw [show u + (count + 1) = u + 1 + count by omega,
        show cursor + 256 * (count + 1) = cursor + 256 + 256 * count by omega]
      exact tail.1

/-- The two pointer advances of every segment. -/
def s3LatchAdvance (state : MachineState) : MachineState :=
  ([.ADDI .x18 .x18 1536, .ADD .x23 .x23 .x7] : List Instr).foldl execInstrBr state

theorem s3_latch_state (state : MachineState) :
    s3LatchState state =
      if (s3LatchAdvance state).pc = 1040160 then
        (s3LatchAdvance state).setPC
          (if BitVec.ult ((s3LatchAdvance state).getReg .x23)
            ((s3LatchAdvance state).getReg .x22) then 1011424 else 1040172)
      else s3LatchAdvance state := rfl

theorem s3_latch_post_register (state : MachineState) (reg : Reg) :
    (s3LatchState state).getReg reg = (s3LatchAdvance state).getReg reg := by
  rw [s3_latch_state]
  split <;> simp only [MachineState.getReg_setPC]

theorem s3_latch_advance_register (state : MachineState) (reg : Reg)
    (h18 : reg ≠ .x18) (h23 : reg ≠ .x23) :
    (s3LatchAdvance state).getReg reg = state.getReg reg := by
  cases reg <;> first | rfl | exact absurd rfl h18 | exact absurd rfl h23

theorem s3_latch_register (state : MachineState) (reg : Reg)
    (h18 : reg ≠ .x18) (h23 : reg ≠ .x23) :
    (s3LatchState state).getReg reg = state.getReg reg := by
  rw [s3_latch_post_register, s3_latch_advance_register _ _ h18 h23]

/-- Two executed instructions at the last segment: the conditional branch and
one of two unconditional jumps. Both paths preserve every register and memory byte. -/
theorem s3_long_latch_execute (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 1040160) (fuel : Nat) :
    execute (submission.image .commit) (2 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel
            (state.setPC (if BitVec.ult (state.getReg .x23) (state.getReg .x22)
              then 1011424 else 1040172)) true
          return result.charge 2 0) := by
  have branch := execute_ordinary_step (submission.image .commit) (.base (.BLTU .x23 .x22 8))
    state (execInstrBr state (.BLTU .x23 .x22 8)) (fuel + 1) true
    (s3_image_long_latch 0 (by decide) state pc) rfl
  rw [show 2 + fuel = (fuel + 1) + 1 by omega, branch]
  by_cases taken : BitVec.ult (state.getReg .x23) (state.getReg .x22) = true
  · have branchState : execInstrBr state (.BLTU .x23 .x22 8) = state.setPC 1040168 := by
      simp only [execInstrBr, taken, ↓reduceIte, pc]
      rfl
    rw [branchState]
    have jump := execute_ordinary_step (submission.image .commit) (.base (.JAL .x0 2068408))
      (state.setPC 1040168) (state.setPC 1011424) fuel true
      (s3_image_long_latch 2 (by decide) _ rfl) (by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
          MachineState.setReg, MachineState.setPC, signExtend21])
    rw [jump]
    simp only [taken, ↓reduceIte, bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge, instructionCycles] <;> omega
  · have branchState : execInstrBr state (.BLTU .x23 .x22 8) = state.setPC 1040164 := by
      simp only [execInstrBr, taken, ↓reduceIte, pc]
      rfl
    rw [branchState]
    have jump := execute_ordinary_step (submission.image .commit) (.base (.JAL .x0 8))
      (state.setPC 1040164) (state.setPC 1040172) fuel true
      (s3_image_long_latch 1 (by decide) _ rfl) (by
        simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
          MachineState.setReg, MachineState.setPC, signExtend21])
    rw [jump]
    simp only [taken, ↓reduceIte, bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge, instructionCycles] <;> omega

def s3SegmentExtra (segment : Nat) : Nat := if segment = 7 then 2 else 0

def s3GroupNextPC (segment heap finish : Nat) : Nat :=
  if segment = 7 then (if heap < finish then 1011424 else 1040172)
  else s3SegmentPC (segment + 1)

set_option maxHeartbeats 8000000 in
/-- One 64-leaf segment: 898 instructions plus two only at each eighth boundary. -/
theorem s3_group_execute (segment : Nat) (hs : segment < 8)
    (state : MachineState) (cursor nonce heap finish : Nat)
    (invariant : S3GroupState state segment 0 cursor nonce heap)
    (stride : state.getReg .x7 = BitVec.ofNat 64 2048)
    (limit : state.getReg .x22 = BitVec.ofNat 64 finish)
    (cursorAligned : cursor % 8 = 0) (nonceAligned : nonce % 8 = 0) (heapAligned : heap % 8 = 0)
    (cursorBound : cursor + 16400 ≤ MEMORY_BYTES) (nonceBound : nonce + 1536 ≤ MEMORY_BYTES)
    (heapBound : heap + 2216 ≤ MEMORY_BYTES) (finishBound : finish ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (898 + s3SegmentExtra segment + fuel) state true =
      (do let next ← s3Group state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge (1794 + s3SegmentExtra segment) 128) ∧
    ∀ next ∈ support (s3Group state),
      next.pc = BitVec.ofNat 64 (s3GroupNextPC segment (heap + 2048) finish) ∧
      S3PermReady next ∧
      next.getReg .x10 = BitVec.ofNat 64 (cursor + 16384) ∧
      next.getReg .x18 = BitVec.ofNat 64 (nonce + 1536) ∧
      next.getReg .x23 = BitVec.ofNat 64 (heap + 2048) ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 → reg ≠ .x23 →
        next.getReg reg = state.getReg reg := by
  have leaves := s3_group_leaves_execute segment hs 64 0 state cursor nonce heap (by decide) invariant
    cursorAligned nonceAligned heapAligned (by omega) nonceBound heapBound (2 + (s3SegmentExtra segment + fuel))
  have facts (finished : MachineState) (reachable : finished ∈ support (s3GroupLeaves state 0 64)) :=
    leaves.2 finished reachable
  have advance (finished : MachineState)
      (reachable : finished ∈ support (s3GroupLeaves state 0 64)) :=
    s3_straight_execute (submission.image .commit) [.ADDI .x18 .x18 1536, .ADD .x23 .x23 .x7] 2
      (s3SegmentPC segment + 3584) finished (s3SegmentExtra segment + fuel) true rfl
      (facts finished reachable).1.pc (by decide)
      (fun k bound current currentPC => by
        have fetched := s3_image_advance segment k hs bound current currentPC
        interval_cases k <;> exact fetched)
      (fun k bound => by interval_cases k <;> rfl)
  have advancePC (finished : MachineState)
      (reachable : finished ∈ support (s3GroupLeaves state 0 64)) :
      (s3LatchAdvance finished).pc = BitVec.ofNat 64 (s3SegmentPC segment + 3592) :=
    (advance finished reachable).2
  have atEnd (finished : MachineState)
      (reachable : finished ∈ support (s3GroupLeaves state 0 64)) :
      (s3LatchAdvance finished).pc = 1040160 ↔ segment = 7 := by
    rw [advancePC finished reachable]
    rw [← BitVec.toNat_inj]
    change ((s3SegmentPC segment + 3592) % 2 ^ 64 = 1040160) ↔ segment = 7
    have bounded : s3SegmentPC segment + 3592 < 2 ^ 64 := by
      dsimp [s3SegmentPC]
      omega
    rw [Nat.mod_eq_of_lt bounded]
    dsimp [s3SegmentPC]
    omega
  have advanceSlots (finished : MachineState)
      (reachable : finished ∈ support (s3GroupLeaves state 0 64)) :
      (s3LatchAdvance finished).getReg .x23 = BitVec.ofNat 64 (heap + 2048) := by
    show finished.getReg .x23 + finished.getReg .x7 = _
    rw [(facts finished reachable).1.slots,
      (facts finished reachable).2 .x7 (by decide) (by decide) (by decide), stride,
      ← BitVec.ofNat_add]
  have advanceNonces (finished : MachineState)
      (reachable : finished ∈ support (s3GroupLeaves state 0 64)) :
      (s3LatchAdvance finished).getReg .x18 = BitVec.ofNat 64 (nonce + 1536) := by
    show finished.getReg .x18 + signExtend12 1536 = _
    rw [(facts finished reachable).1.nonces,
      show signExtend12 (1536 : BitVec 12) = BitVec.ofNat 64 1536 from rfl, ← BitVec.ofNat_add]
  have branch (finished : MachineState)
      (reachable : finished ∈ support (s3GroupLeaves state 0 64)) :
      execute (submission.image .commit) (s3SegmentExtra segment + fuel) (s3LatchAdvance finished) true =
        (do let result ← execute (submission.image .commit) fuel (s3LatchState finished) true
            return result.charge (s3SegmentExtra segment) 0) := by
    by_cases last : segment = 7
    · rw [s3SegmentExtra, if_pos last, s3_latch_state, if_pos ((atEnd finished reachable).2 last)]
      exact s3_long_latch_execute _ ((atEnd finished reachable).2 last) fuel
    · rw [s3SegmentExtra, if_neg last, s3_latch_state,
        if_neg (fun h => last ((atEnd finished reachable).1 h))]
      simp [Execution.charge]
  constructor
  · rw [show 898 + s3SegmentExtra segment + fuel =
      14 * 64 + (2 + (s3SegmentExtra segment + fuel)) by omega, leaves.1]
    simp only [s3Group, bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun finished reachable => ?_
    have advanceRun : execute (submission.image .commit) (2 + (s3SegmentExtra segment + fuel)) finished true =
        (do let result ← execute (submission.image .commit) (s3SegmentExtra segment + fuel)
              (s3LatchAdvance finished) true
            return result.charge 2 0) := (advance finished reachable).1
    rw [advanceRun, branch finished reachable]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · intro next reachable
    simp only [s3Group, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨finished, reached, rfl⟩ := reachable
    have known := facts finished reached
    have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide)
        (h12 : reg ≠ .x12 := by decide) (h18 : reg ≠ .x18 := by decide)
        (h23 : reg ≠ .x23 := by decide) :
        (s3LatchState finished).getReg reg = state.getReg reg :=
      (s3_latch_register finished reg h18 h23).trans (known.2 reg h6 h10 h12)
    refine ⟨?_, ⟨(kept .x5).trans invariant.ready.1, (kept .x11).trans invariant.ready.2.1,
      (kept .x13).trans invariant.ready.2.2⟩, ?_, ?_, ?_,
      fun reg h6 h10 h12 h18 h23 => kept reg h6 h10 h12 h18 h23⟩
    · have compared : BitVec.ult ((s3LatchAdvance finished).getReg .x23)
          ((s3LatchAdvance finished).getReg .x22) = decide (heap + 2048 < finish) := by
        rw [advanceSlots finished reached,
          s3_latch_advance_register finished .x22 (by decide) (by decide),
          known.2 .x22 (by decide) (by decide) (by decide), limit]
        simp only [BitVec.ult, BitVec.toNat_ofNat]
        have hb : heap + 2048 < 2 ^ 64 := by dsimp [MEMORY_BYTES] at heapBound; omega
        have fb : finish < 2 ^ 64 := by dsimp [MEMORY_BYTES] at finishBound; omega
        rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt fb]
      rw [s3_latch_state]
      by_cases last : segment = 7
      · rw [if_pos ((atEnd finished reached).2 last), s3GroupNextPC, if_pos last, compared]
        by_cases more : heap + 2048 < finish <;> simp [more, MachineState.setPC]
      · rw [if_neg (fun h => last ((atEnd finished reached).1 h)), advancePC finished reached,
          s3GroupNextPC, if_neg last]
        congr 1 <;> simp only [s3SegmentPC] <;> omega
    · rw [s3_latch_register _ _ (by decide) (by decide)]
      exact known.1.input
    · rw [s3_latch_post_register]
      exact advanceNonces finished reached
    · rw [s3_latch_post_register]
      exact advanceSlots finished reached

/-- All segments, including complete final groups of eight. The quotient counts
exactly the two-instruction long transfers actually executed. -/
theorem s3_groups_execute (groups : Nat) :
    ∀ (segment : Nat), segment < 8 → (segment + groups + 1) % 8 = 0 →
    ∀ (state : MachineState) (cursor nonce heap finish : Nat),
    S3GroupState state segment 0 cursor nonce heap →
    state.getReg .x7 = BitVec.ofNat 64 2048 → state.getReg .x22 = BitVec.ofNat 64 finish →
    heap + 2048 * (groups + 1) = finish →
    cursor % 8 = 0 → nonce % 8 = 0 → heap % 8 = 0 →
    cursor + 16384 * (groups + 1) + 16 ≤ MEMORY_BYTES →
    nonce + 1536 * (groups + 1) ≤ MEMORY_BYTES → finish + 168 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit)
        (898 * (groups + 1) + 2 * ((segment + groups + 1) / 8) + fuel) state true =
      (do let finished ← s3Groups state (groups + 1)
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (1794 * (groups + 1) + 2 * ((segment + groups + 1) / 8))
            (128 * (groups + 1))) ∧
    ∀ finished ∈ support (s3Groups state (groups + 1)),
      finished.pc = BitVec.ofNat 64 1040172 ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 → reg ≠ .x23 →
        finished.getReg reg = state.getReg reg := by
  induction groups with
  | zero =>
    intro segment hs aligned state cursor nonce heap finish invariant stride limit window cursorAligned
      nonceAligned heapAligned cursorBound nonceBound finishBound fuel
    have last : segment = 7 := by omega
    subst segment
    have group := s3_group_execute 7 (by decide) state cursor nonce heap finish invariant stride limit
      cursorAligned nonceAligned heapAligned (by omega) (by omega) (by omega) (by omega) fuel
    constructor
    · simpa only [s3SegmentExtra, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
        s3Groups, bind_assoc, pure_bind] using group.1
    · intro finished reachable
      simp only [s3Groups, bind_pure] at reachable
      have known := group.2 finished reachable
      refine ⟨?_, known.2.2.2.2.2⟩
      rw [known.1, s3GroupNextPC, if_pos rfl, if_neg (by omega)]
  | succ groups ih =>
    intro segment hs aligned state cursor nonce heap finish invariant stride limit window cursorAligned
      nonceAligned heapAligned cursorBound nonceBound finishBound fuel
    let nextSegment := (segment + 1) % 8
    have countStep : (segment + (groups + 1) + 1) / 8 =
        (if segment = 7 then 1 else 0) + (nextSegment + groups + 1) / 8 := by
      dsimp [nextSegment]
      split <;> omega
    have group := s3_group_execute segment hs state cursor nonce heap finish invariant stride limit
      cursorAligned nonceAligned heapAligned (by omega) (by omega) (by omega) (by omega)
      (898 * (groups + 1) + 2 * ((nextSegment + groups + 1) / 8) + fuel)
    have continued (next : MachineState) (reached : next ∈ support (s3Group state)) :=
      ih nextSegment (by dsimp [nextSegment]; omega) (by dsimp [nextSegment]; omega)
        next (cursor + 16384) (nonce + 1536) (heap + 2048) finish
        ⟨by
          rw [(group.2 next reached).1]
          congr 1
          dsimp [s3GroupNextPC, nextSegment, s3SegmentPC]
          split <;> (try split) <;> omega,
          (group.2 next reached).2.1,
          (group.2 next reached).2.2.1, (group.2 next reached).2.2.2.1,
          (group.2 next reached).2.2.2.2.1⟩
        (((group.2 next reached).2.2.2.2.2 .x7 (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans stride)
        (((group.2 next reached).2.2.2.2.2 .x22 (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans limit)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) finishBound fuel
    constructor
    · have total : 898 * (groups + 1 + 1) + 2 * ((segment + (groups + 1) + 1) / 8) + fuel =
          898 + s3SegmentExtra segment +
            (898 * (groups + 1) + 2 * ((nextSegment + groups + 1) / 8) + fuel) := by
        rw [countStep]
        unfold s3SegmentExtra
        split <;> omega
      rw [total, group.1]
      simp only [s3Groups, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun next reached => ?_
      rw [(continued next reached).1]
      simp only [s3Groups, bind_assoc, pure_bind]
      refine bind_congr fun following => ?_
      refine bind_congr fun finished => ?_
      refine bind_congr fun result => ?_
      by_cases last : segment = 7 <;>
        simp [Execution.charge, s3SegmentExtra, last, countStep] <;> omega
    · intro finished reachable
      rw [s3Groups] at reachable
      simp only [mem_support_bind_iff] at reachable
      obtain ⟨next, reached, rest⟩ := reachable
      have tail := (continued next reached).2 finished rest
      exact ⟨tail.1, fun reg h6 h10 h12 h18 h23 => (tail.2 reg h6 h10 h12 h18 h23).trans
        ((group.2 next reached).2.2.2.2.2 reg h6 h10 h12 h18 h23)⟩

/-- The 44 fall-through instructions before the exit jump. -/
def s3FinishStraight : List Instr :=
  s3RepairInstructions ++ [.ADDI .x11 .x0 64, .ADDI .x13 .x0 0]

theorem s3_finish_state (state : MachineState) :
    s3FinishState state =
      execInstrBr (s3FinishStraight.foldl execInstrBr state) (.JAL .x0 1061168) := rfl

theorem s3_finish_register (state : MachineState) (reg : Reg)
    (h6 : reg ≠ .x6) (h11 : reg ≠ .x11) (h13 : reg ≠ .x13) :
    (s3FinishState state).getReg reg = state.getReg reg := by
  cases reg <;> first | rfl | exact absurd rfl h6 | exact absurd rfl h11 | exact absurd rfl h13

theorem s3_finish_constants (state : MachineState) :
    (s3FinishState state).getReg .x11 = 64 ∧ (s3FinishState state).getReg .x13 = 0 :=
  ⟨rfl, rfl⟩

set_option maxHeartbeats 16000000 in
/-- Nonce repair and exit: 45 instructions ending at the testers' parent setup. -/
theorem s3_finish_execute (state : MachineState) (source nonce : Nat)
    (pc : state.pc = BitVec.ofNat 64 1040172)
    (message : state.getReg .x8 = BitVec.ofNat 64 source)
    (nonces : state.getReg .x22 = BitVec.ofNat 64 nonce)
    (sourceAligned : source % 8 = 0) (nonceAligned : nonce % 8 = 0)
    (sourceBound : source + 1616 ≤ MEMORY_BYTES) (nonceBound : nonce + 168 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (45 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (s3FinishState state) true
          return result.charge 45 0) ∧
    (s3FinishState state).pc = 4364 := by
  have straight := s3_straight_execute (submission.image .commit) s3FinishStraight 44 1040172
    state (1 + fuel) true rfl pc (by decide)
    (fun k bound current currentPC => by
      have fetched := s3_image_finish k (by omega) current currentPC
      interval_cases k <;> exact fetched)
    (fun k bound => by
      interval_cases k
      · exact s3_access_valid _ _ source 56 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 0 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 64 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 8 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 72 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 16 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 312 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 24 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 320 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 32 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 328 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 40 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 568 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 48 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 576 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 56 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 584 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 64 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 824 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 72 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 832 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 80 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 840 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 88 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1080 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 96 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1088 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 104 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1096 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 112 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1336 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 120 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1344 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 128 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1352 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 136 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1592 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 144 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1600 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 152 nonces rfl nonceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ source 1608 message rfl sourceAligned (by decide) (by omega)
      · exact s3_access_valid _ _ nonce 160 nonces rfl nonceAligned (by decide) (by omega)
      · rfl
      · rfl)
  have jumpPC : (s3FinishStraight.foldl execInstrBr state).pc = BitVec.ofNat 64 1040348 :=
    straight.2
  have jump : execute (submission.image .commit) (fuel + 1)
      (s3FinishStraight.foldl execInstrBr state) true =
      (do let result ← execute (submission.image .commit) fuel (s3FinishState state) true
          return result.charge 1 0) :=
    execute_ordinary_step (submission.image .commit) (.base (.JAL .x0 1061168))
      (s3FinishStraight.foldl execInstrBr state) (s3FinishState state) fuel true
      (s3_image_finish 44 (by decide) _ jumpPC) rfl
  constructor
  · rw [show 45 + fuel = 44 + (1 + fuel) by omega, straight.1, Nat.add_comm 1 fuel, jump]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · rw [s3_finish_state]
    show (s3FinishStraight.foldl execInstrBr state).pc + signExtend21 1061168 = 4364
    rw [jumpPC]
    rfl

theorem s3_entry_register (state : MachineState) (reg : Reg)
    (h7 : reg ≠ .x7) (h10 : reg ≠ .x10) (h11 : reg ≠ .x11) (h13 : reg ≠ .x13) :
    (s3EntryState state).getReg reg = state.getReg reg := by
  cases reg <;> first | rfl | exact absurd rfl h7 | exact absurd rfl h10 | exact absurd rfl h11 |
    exact absurd rfl h13

set_option maxHeartbeats 8000000 in
/-- The whole appended leaf phase, from the state after the ready block and entry jump
(PC 1011404) to the testers' parent setup (PC 4364). -/
theorem s3_leaves_execute (state : MachineState) (groups cursor source nonce heap : Nat)
    (alignedGroups : (groups + 1) % 8 = 0)
    (pc : state.pc = BitVec.ofNat 64 1011404)
    (selector : state.getReg .x5 = 0)
    (input : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (message : state.getReg .x8 = BitVec.ofNat 64 source)
    (nonces : state.getReg .x18 = BitVec.ofNat 64 nonce)
    (slots : state.getReg .x23 = BitVec.ofNat 64 heap)
    (limit : state.getReg .x22 = BitVec.ofNat 64 nonce)
    (window : heap + 2048 * (groups + 1) = nonce)
    (cursorAligned : cursor % 8 = 0) (sourceAligned : source % 8 = 0) (heapAligned : heap % 8 = 0)
    (cursorBound : cursor + 16384 * (groups + 1) + 32 ≤ MEMORY_BYTES)
    (sourceBound : source + 1616 ≤ MEMORY_BYTES)
    (nonceBound : nonce + 1536 * (groups + 1) ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) ((898 * (groups + 1) + 2 * ((groups + 1) / 8)) + 50 + fuel) state true =
      (do let leaves ← s3Leaves state (groups + 1)
          let result ← execute (submission.image .commit) fuel leaves true
          return result.charge ((1794 * (groups + 1) + 2 * ((groups + 1) / 8)) + 50) (128 * (groups + 1))) ∧
    ∀ leaves ∈ support (s3Leaves state (groups + 1)),
      leaves.pc = 4364 ∧
      leaves.getReg .x5 = 0 ∧ leaves.getReg .x11 = 64 ∧ leaves.getReg .x13 = 0 ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x12 → reg ≠ .x13 →
        reg ≠ .x18 → reg ≠ .x23 → leaves.getReg reg = state.getReg reg := by
  have entry := s3_straight_execute (submission.image .commit) s3EntryInstructions 5 1011404
    state ((898 * (groups + 1) + 2 * ((groups + 1) / 8)) + (45 + fuel)) true rfl pc (by decide)
    (fun k bound current currentPC => s3_image_entry k bound current currentPC)
    (fun k bound => by interval_cases k <;> rfl)
  have entryRun : execute (submission.image .commit) (5 + ((898 * (groups + 1) + 2 * ((groups + 1) / 8)) + (45 + fuel)))
      state true =
      (do let result ← execute (submission.image .commit) ((898 * (groups + 1) + 2 * ((groups + 1) / 8)) + (45 + fuel))
            (s3EntryState state) true
          return result.charge 5 0) := entry.1
  have entered : S3GroupState (s3EntryState state) 0 0 (cursor + 16) nonce heap :=
    ⟨entry.2, ⟨selector, rfl, rfl⟩, by
      show state.getReg .x10 + signExtend12 16 = _
      rw [input, show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from rfl,
        ← BitVec.ofNat_add], nonces, slots⟩
  have nonceAligned : nonce % 8 = 0 := by omega
  have groupsRun := s3_groups_execute groups 0 (by decide) (by simpa using alignedGroups) (s3EntryState state) (cursor + 16) nonce heap nonce
    entered rfl limit window (by omega) nonceAligned heapAligned (by omega) nonceBound (by omega)
    (45 + fuel)
  simp only [Nat.zero_add] at groupsRun
  have kept (hashed : MachineState)
      (reached : hashed ∈ support (s3Groups (s3EntryState state) (groups + 1))) (reg : Reg)
      (h6 : reg ≠ .x6 := by decide) (h7 : reg ≠ .x7 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h11 : reg ≠ .x11 := by decide) (h12 : reg ≠ .x12 := by decide)
      (h13 : reg ≠ .x13 := by decide) (h18 : reg ≠ .x18 := by decide)
      (h23 : reg ≠ .x23 := by decide) : hashed.getReg reg = state.getReg reg :=
    ((groupsRun.2 hashed reached).2 reg h6 h10 h12 h18 h23).trans
      (s3_entry_register state reg h7 h10 h11 h13)
  have finish (hashed : MachineState)
      (reached : hashed ∈ support (s3Groups (s3EntryState state) (groups + 1))) :=
    s3_finish_execute hashed source nonce (groupsRun.2 hashed reached).1
      ((kept hashed reached .x8).trans message) ((kept hashed reached .x22).trans limit)
      sourceAligned nonceAligned sourceBound (by omega) fuel
  constructor
  · rw [show (898 * (groups + 1) + 2 * ((groups + 1) / 8)) + 50 + fuel = 5 + ((898 * (groups + 1) + 2 * ((groups + 1) / 8)) + (45 + fuel)) by omega,
      entryRun, groupsRun.1]
    simp only [s3Leaves, bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun hashed reached => ?_
    rw [(finish hashed reached).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · intro leaves reachable
    simp only [s3Leaves, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨hashed, reached, rfl⟩ := reachable
    refine ⟨(finish hashed reached).2, ?_, (s3_finish_constants hashed).1,
      (s3_finish_constants hashed).2, fun reg h6 h7 h10 h11 h12 h13 h18 h23 => ?_⟩
    · rw [s3_finish_register hashed .x5 (by decide) (by decide) (by decide),
        kept hashed reached .x5]
      exact selector
    · rw [s3_finish_register hashed reg h6 h11 h13]
      exact kept hashed reached reg h6 h7 h10 h11 h12 h13 h18 h23

end CommitGolfCandidate
