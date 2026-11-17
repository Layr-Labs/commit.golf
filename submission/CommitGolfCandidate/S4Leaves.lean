import CommitGolfCandidate.S4Block

/-! All 512-leaf blocks and the complete physical leaf phase. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 2000000
set_option maxHeartbeats 8000000

/-- Support facts after `groups + 1` reference groups. -/
theorem s4_groups_support (groups : Nat) : ∀ (state : MachineState) (cursor nonce heap finish : Nat),
    S3GroupState state 0 cursor nonce heap →
    state.getReg .x7 = BitVec.ofNat 64 2048 → state.getReg .x22 = BitVec.ofNat 64 finish →
    heap + 2048 * (groups + 1) ≤ finish →
    cursor % 8 = 0 → nonce % 8 = 0 → heap % 8 = 0 →
    cursor + 16384 * (groups + 1) + 16 ≤ MEMORY_BYTES →
    nonce + 1536 * (groups + 1) ≤ MEMORY_BYTES → finish + 168 ≤ MEMORY_BYTES →
    ∀ next ∈ support (s3Groups state (groups + 1)),
      next.pc = BitVec.ofNat 64 (if heap + 2048 * (groups + 1) < finish then 1011424 else 1015020) ∧
      S3PermReady next ∧
      next.getReg .x10 = BitVec.ofNat 64 (cursor + 16384 * (groups + 1)) ∧
      next.getReg .x18 = BitVec.ofNat 64 (nonce + 1536 * (groups + 1)) ∧
      next.getReg .x23 = BitVec.ofNat 64 (heap + 2048 * (groups + 1)) ∧
      ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 → reg ≠ .x23 →
        next.getReg reg = state.getReg reg := by
  induction groups with
  | zero =>
    intro state cursor nonce heap finish invariant stride limit window cursorAligned nonceAligned
      heapAligned cursorBound nonceBound finishBound next reached
    simp only [s3Groups, bind_pure] at reached
    have facts := (s3_group_execute state cursor nonce heap finish invariant stride limit
      cursorAligned nonceAligned heapAligned (by omega) (by omega) (by omega) (by omega) 0).2 next reached
    simpa using facts
  | succ groups ih =>
    intro state cursor nonce heap finish invariant stride limit window cursorAligned nonceAligned
      heapAligned cursorBound nonceBound finishBound next reached
    rw [show groups + 1 + 1 = 1 + (groups + 1) by omega, s3_groups_add] at reached
    simp only [mem_support_bind_iff] at reached
    obtain ⟨middle, middleReached, rest⟩ := reached
    have first := (s3_group_execute state cursor nonce heap finish invariant stride limit
      cursorAligned nonceAligned heapAligned (by omega) (by omega) (by omega) (by omega) 0).2
      middle (by simpa [s3Groups] using middleReached)
    have later := ih middle (cursor + 16384) (nonce + 1536) (heap + 2048) finish
      ⟨by rw [first.1, if_pos (by omega)], first.2.1, first.2.2.1, first.2.2.2.1, first.2.2.2.2.1⟩
      ((first.2.2.2.2.2 .x7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans stride)
      ((first.2.2.2.2.2 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) finishBound next rest
    refine ⟨?_, later.2.1, ?_, ?_, ?_, fun reg h6 h10 h12 h18 h23 =>
      (later.2.2.2.2.2 reg h6 h10 h12 h18 h23).trans (first.2.2.2.2.2 reg h6 h10 h12 h18 h23)⟩
    · rw [later.1]; congr 2; ring_nf
    · rw [later.2.2.1]; congr 1; ring
    · rw [later.2.2.2.1]; congr 1; ring
    · rw [later.2.2.2.2.1]; congr 1; ring

/-- All blocks: 7186 instructions and 14354 cycles per block, two more for the final exit. -/
theorem s4_blocks (blocks : Nat) : ∀ (state : MachineState) (cursor nonce heap finish : Nat),
    S3GroupState state 0 cursor nonce heap →
    state.getReg .x7 = BitVec.ofNat 64 2048 → state.getReg .x22 = BitVec.ofNat 64 finish →
    heap + 16384 * (blocks + 1) = finish →
    cursor % 8 = 0 → nonce % 8 = 0 → heap % 8 = 0 →
    cursor + 131072 * (blocks + 1) + 16 ≤ MEMORY_BYTES →
    nonce + 12288 * (blocks + 1) ≤ MEMORY_BYTES → finish + 168 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (7186 * (blocks + 1) + 2 + fuel)
        (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 (s4HalfPC 0 0)) state) true =
      (do let next ← s3Groups state (8 * (blocks + 1))
          let result ← execute (submission.image .commit) fuel next true
          return result.charge (14354 * (blocks + 1) + 2) (1024 * (blocks + 1))) := by
  induction blocks with
  | zero =>
    intro state cursor nonce heap finish invariant stride limit window cursorAligned nonceAligned
      heapAligned cursorBound nonceBound finishBound fuel
    have run := s4_windows 3 0 state cursor nonce heap finish (by decide) invariant stride limit
      (by omega) cursorAligned nonceAligned heapAligned (by omega) (by omega) finishBound (4 + fuel)
    rw [show 7186 * (0 + 1) + 2 + fuel = 1796 * (3 + 1) + (4 + fuel) by omega, run]
    try simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    have facts := s4_groups_support 7 state cursor nonce heap finish invariant stride limit
      (by omega) cursorAligned nonceAligned heapAligned (by omega) (by omega) finishBound next
      (by simpa using reached)
    rw [show s4HalfPC (0 + (3 + 1)) 0 = 1043964 by rfl,
      s4_end_exit next finish (by rw [facts.1, if_neg (by omega)])
        (by rw [facts.2.2.2.2.1]; congr 1; try omega)
        ((facts.2.2.2.2.2 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit)
        (by dsimp [MEMORY_BYTES] at finishBound; omega) fuel]
    simp only [bind_assoc, pure_bind, Execution.charge]
    refine bind_congr fun result => ?_
    simp only [pure_inj]
    congr 1 <;> omega
  | succ blocks ih =>
    intro state cursor nonce heap finish invariant stride limit window cursorAligned nonceAligned
      heapAligned cursorBound nonceBound finishBound fuel
    have run := s4_windows 3 0 state cursor nonce heap finish (by decide) invariant stride limit
      (by omega) cursorAligned nonceAligned heapAligned (by omega) (by omega) finishBound
      (2 + (7186 * (blocks + 1) + 2 + fuel))
    rw [show 7186 * (blocks + 1 + 1) + 2 + fuel = 1796 * (3 + 1) + (2 + (7186 * (blocks + 1) + 2 + fuel))
      by ring, run, show 8 * (blocks + 1 + 1) = 2 * (3 + 1) + 8 * (blocks + 1) by ring, s3_groups_add]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    have facts := s4_groups_support 7 state cursor nonce heap finish invariant stride limit
      (by omega) cursorAligned nonceAligned heapAligned (by omega) (by omega) finishBound next
      (by simpa using reached)
    have nextState : S3GroupState next 0 (cursor + 131072) (nonce + 12288) (heap + 16384) :=
      ⟨by rw [facts.1, if_pos (by omega)], facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2.1⟩
    rw [show s4HalfPC (0 + (3 + 1)) 0 = 1043964 by rfl,
      s4_end_loop next (heap + 16384) finish facts.2.2.2.2.1
        ((facts.2.2.2.2.2 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit)
        (by omega) (by omega) (by dsimp [MEMORY_BYTES] at finishBound; omega),
      show (1015228 : Nat) = s4HalfPC 0 0 by rfl,
      ih next (cursor + 131072) (nonce + 12288) (heap + 16384) finish nextState
        ((facts.2.2.2.2.2 .x7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans stride)
        ((facts.2.2.2.2.2 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) finishBound fuel]
    simp only [bind_assoc, pure_bind, Execution.charge]
    refine bind_congr fun last => ?_
    refine bind_congr fun result => ?_
    simp only [pure_inj]
    congr 1 <;> ring

theorem s4_entry_frame (state : MachineState) :
    (s3EntryInstructions ++ s4BiasInstructions).foldl execInstrBr (state.setPC 1015200) =
      s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 (s4HalfPC 0 0)) (s3EntryState state) := by
  have entry : s3EntryInstructions.foldl execInstrBr (state.setPC 1015200) =
      (s3EntryState state).setPC 1015220 := by
    cases state; rfl
  rw [List.foldl_append, entry, ← s4_frame_zero_pc]
  simp only [s4BiasInstructions, List.foldl]
  rw [s4_frame_addi18, s4_frame_add23 _ _ _ _ rfl]
  congr 1 <;> decide

/-- The physical leaf phase from the retargeted entry (PC 1015200) to parent setup. -/
theorem s4_leaves_execute (state : MachineState) (blocks cursor source nonce heap : Nat)
    (pc : state.pc = BitVec.ofNat 64 1011404)
    (selector : state.getReg .x5 = 0)
    (input : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (message : state.getReg .x8 = BitVec.ofNat 64 source)
    (nonces : state.getReg .x18 = BitVec.ofNat 64 nonce)
    (slots : state.getReg .x23 = BitVec.ofNat 64 heap)
    (limit : state.getReg .x22 = BitVec.ofNat 64 nonce)
    (window : heap + 16384 * (blocks + 1) = nonce)
    (cursorAligned : cursor % 8 = 0) (sourceAligned : source % 8 = 0) (heapAligned : heap % 8 = 0)
    (cursorBound : cursor + 131072 * (blocks + 1) + 32 ≤ MEMORY_BYTES)
    (sourceBound : source + 1616 ≤ MEMORY_BYTES)
    (nonceBound : nonce + 12288 * (blocks + 1) ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (7186 * (blocks + 1) + 54 + fuel) (state.setPC 1015200) true =
      (do let leaves ← s3Leaves state (8 * (blocks + 1))
          let result ← execute (submission.image .commit) fuel leaves true
          return result.charge (14354 * (blocks + 1) + 54) (1024 * (blocks + 1))) := by
  have entry := s3_straight_execute (submission.image .commit)
    (s3EntryInstructions ++ s4BiasInstructions) 7 1015200 (state.setPC 1015200)
    (7186 * (blocks + 1) + 2 + (45 + fuel)) true rfl rfl (by decide)
    (fun k bound current currentPC => s4_image_entry k bound current currentPC)
    (fun k bound => by interval_cases k <;> rfl)
  rw [s4_entry_frame] at entry
  have entered : S3GroupState (s3EntryState state) 0 (cursor + 16) nonce heap :=
    ⟨by
      have := (s3_straight_execute (submission.image .commit) s3EntryInstructions 5 1011404 state
        0 true rfl pc (by decide) (fun k bound current currentPC => s3_image_entry k bound current
        currentPC) (fun k bound => by interval_cases k <;> rfl)).2
      exact this, ⟨selector, rfl, rfl⟩, by
      show state.getReg .x10 + signExtend12 16 = _
      rw [input, show signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 from rfl,
        ← BitVec.ofNat_add], nonces, slots⟩
  have nonceAligned : nonce % 8 = 0 := by omega
  have blocksRun := s4_blocks blocks (s3EntryState state) (cursor + 16) nonce heap nonce entered
    rfl limit window (by omega) nonceAligned heapAligned (by omega) nonceBound (by omega) (45 + fuel)
  have finished (hashed : MachineState)
      (reached : hashed ∈ support (s3Groups (s3EntryState state) (8 * (blocks + 1)))) :=
    (s3_groups_execute (8 * blocks + 7) (s3EntryState state) (cursor + 16) nonce heap nonce entered
      rfl limit (by omega) (by omega) nonceAligned heapAligned (by omega) (by omega) (by omega)
      0).2 hashed (by rw [show 8 * blocks + 7 + 1 = 8 * (blocks + 1) by ring]; exact reached)
  have kept (hashed : MachineState)
      (reached : hashed ∈ support (s3Groups (s3EntryState state) (8 * (blocks + 1)))) (reg : Reg)
      (h6 : reg ≠ .x6 := by decide) (h7 : reg ≠ .x7 := by decide) (h10 : reg ≠ .x10 := by decide)
      (h11 : reg ≠ .x11 := by decide) (h12 : reg ≠ .x12 := by decide)
      (h13 : reg ≠ .x13 := by decide) (h18 : reg ≠ .x18 := by decide)
      (h23 : reg ≠ .x23 := by decide) : hashed.getReg reg = state.getReg reg :=
    ((finished hashed reached).2 reg h6 h10 h12 h18 h23).trans
      (s3_entry_register state reg h7 h10 h11 h13)
  rw [show 7186 * (blocks + 1) + 54 + fuel = 7 + (7186 * (blocks + 1) + 2 + (45 + fuel)) by omega,
    entry.1, blocksRun]
  simp only [s3Leaves, bind_assoc, pure_bind]
  refine bind_congr_of_forall_mem_support _ fun hashed reached => ?_
  rw [(s3_finish_execute hashed source nonce (finished hashed reached).1
    ((kept hashed reached .x8).trans message) ((kept hashed reached .x22).trans limit)
    sourceAligned nonceAligned sourceBound (by omega) fuel).1]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun result => ?_
  simp [Execution.charge]
  omega

end CommitGolfCandidate
