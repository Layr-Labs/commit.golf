import CommitGolfCandidate.S4Exec

/-! Windows, blocks and the whole physical leaf phase of the 512-leaf layout. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem s4_frame_zero_pc (pc : Word) (state : MachineState) :
    s4Frame 0 0 pc state = state.setPC pc := by
  cases state
  simp only [s4Frame, unrollShift, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    BitVec.sub_zero, BitVec.add_zero, MachineState.mk.injEq, and_true]
  funext reg
  cases reg <;> simp

theorem s4_frame_addi18 (a b p : Word) (state : MachineState) (c : BitVec 12) :
    execInstrBr (s4Frame a b p state) (.ADDI .x18 .x18 c) =
      s4Frame (a - signExtend12 c) b (p + 4) state := by
  have x18 : state.getReg .x18 - a + signExtend12 c = state.getReg .x18 - (a - signExtend12 c) := by
    bv_omega
  cases state
  simp only [execInstrBr, s4Frame, unrollShift, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, MachineState.mk.injEq] at x18 ⊢
  constructor
  · funext reg
    cases reg <;> simp_all
  · simp_all

theorem s4_frame_addi23 (a b p : Word) (state : MachineState) (c : BitVec 12) :
    execInstrBr (s4Frame a b p state) (.ADDI .x23 .x23 c) =
      s4Frame a (b - signExtend12 c) (p + 4) state := by
  have x23 : state.getReg .x23 - b + signExtend12 c = state.getReg .x23 - (b - signExtend12 c) := by
    bv_omega
  cases state
  simp only [execInstrBr, s4Frame, unrollShift, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, MachineState.mk.injEq] at x23 ⊢
  constructor
  · funext reg
    cases reg <;> simp_all
  · simp_all

theorem s4_frame_add23 (a b p : Word) (state : MachineState)
    (stride : state.getReg .x7 = BitVec.ofNat 64 2048) :
    execInstrBr (s4Frame a b p state) (.ADD .x23 .x23 .x7) =
      s4Frame a (b - 2048) (p + 4) state := by
  have x23 : state.getReg .x23 - b + state.getReg .x7 = state.getReg .x23 - (b - 2048) := by
    rw [stride]; bv_omega
  cases state
  simp only [execInstrBr, s4Frame, unrollShift, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, MachineState.mk.injEq] at x23 stride ⊢
  constructor
  · funext reg
    cases reg <;> simp_all
  · simp_all

/-- The reference latch only changes the displacement of the physical frame. -/
theorem s4_frame_latch (a b p : Word) (state : MachineState)
    (stride : state.getReg .x7 = BitVec.ofNat 64 2048) :
    s4Frame a b p state = s4Frame (a + 1536) (b + 2048) p (s3LatchState state) := by
  have s1536 : signExtend12 (1536 : BitVec 12) = 1536 := by decide
  have x18 : state.getReg .x18 - a = state.getReg .x18 + signExtend12 1536 - (a + 1536) := by
    rw [s1536]; bv_omega
  have x23 : state.getReg .x23 - b = state.getReg .x23 + state.getReg .x7 - (b + 2048) := by
    rw [stride]; bv_omega
  have branch : ∀ current : MachineState, execInstrBr current (.BLTU .x23 .x22 4600) =
      current.setPC (execInstrBr current (.BLTU .x23 .x22 4600)).pc := by
    intro current
    simp only [execInstrBr]
    split <;> cases current <;> rfl
  have framePC : ∀ (current : MachineState) (q : Word),
      s4Frame (a + 1536) (b + 2048) p (current.setPC q) = s4Frame (a + 1536) (b + 2048) p current := by
    intro current q; cases current; rfl
  rw [s3_latch_state, branch, framePC]
  cases state
  simp only [s3LatchAdvance, List.foldl, execInstrBr, s4Frame, unrollShift, MachineState.getReg,
    MachineState.setReg, MachineState.setPC, MachineState.mk.injEq] at x18 x23 stride ⊢
  constructor
  · funext reg
    cases reg <;> simp_all
  · simp_all

theorem s4_rebase_frame (a b p : Word) (state : MachineState)
    (stride : state.getReg .x7 = BitVec.ofNat 64 2048) :
    s4RebaseInstructions.foldl execInstrBr (s4Frame a b p state) =
      s4Frame (a - 3072) (b - 4096) (p + 16) state := by
  have s1536 : signExtend12 (1536 : BitVec 12) = 1536 := by decide
  simp only [s4RebaseInstructions, List.foldl]
  rw [s4_frame_addi18, s4_frame_addi18, s4_frame_add23 _ _ _ _ stride,
    s4_frame_add23 _ _ _ _ stride, s1536]
  congr 1 <;> bv_omega

theorem s3_groups_add (state : MachineState) (first second : Nat) :
    s3Groups state (first + second) =
      (do let middle ← s3Groups state first
          s3Groups middle second) := by
  induction first generalizing state with
  | zero => simp [s3Groups]
  | succ first ih =>
    rw [show first + 1 + second = (first + second) + 1 by omega]
    simp only [s3Groups, bind_assoc, ih]

/-- Facts after two reference groups. -/
structure S4Next (state next : MachineState) (cursor nonce heap finish : Nat) : Prop where
  pc : next.pc = BitVec.ofNat 64 (if heap + 4096 < finish then 1011424 else 1015020)
  ready : S3PermReady next
  input : next.getReg .x10 = BitVec.ofNat 64 (cursor + 32768)
  nonces : next.getReg .x18 = BitVec.ofNat 64 (nonce + 3072)
  slots : next.getReg .x23 = BitVec.ofNat 64 (heap + 4096)
  kept : ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x18 → reg ≠ .x23 →
    next.getReg reg = state.getReg reg

set_option maxHeartbeats 16000000 in
/-- One window: two halves and the rebase, 1796 instructions, 3588 cycles, two reference groups. -/
theorem s4_window_execute (w : Nat) (hw : w < 4) (state : MachineState)
    (cursor nonce heap finish : Nat)
    (invariant : S3GroupState state 0 cursor nonce heap)
    (stride : state.getReg .x7 = BitVec.ofNat 64 2048)
    (limit : state.getReg .x22 = BitVec.ofNat 64 finish)
    (more : heap + 4096 ≤ finish)
    (cursorAligned : cursor % 8 = 0) (nonceAligned : nonce % 8 = 0) (heapAligned : heap % 8 = 0)
    (cursorBound : cursor + 32768 + 16 ≤ MEMORY_BYTES) (nonceBound : nonce + 3072 ≤ MEMORY_BYTES)
    (finishBound : finish + 168 ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (1796 + fuel)
        (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 (s4HalfPC w 0)) state) true =
      (do let next ← s3Groups state 2
          let result ← execute (submission.image .commit) fuel
            (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 (s4HalfPC w 0 + 7184)) next) true
          return result.charge 3588 256) ∧
    ∀ next ∈ support (s3Groups state 2), S4Next state next cursor nonce heap finish := by
  have first := s3_group_execute state cursor nonce heap finish invariant stride limit
    cursorAligned nonceAligned heapAligned (by omega) (by omega) (by omega) (by omega) 0
  have middleState (middle : MachineState) (reached : middle ∈ support (s3Group state)) :
      S3GroupState middle 0 (cursor + 16384) (nonce + 1536) (heap + 2048) :=
    ⟨by rw [(first.2 middle reached).1, if_pos (by omega)], (first.2 middle reached).2.1,
      (first.2 middle reached).2.2.1, (first.2 middle reached).2.2.2.1,
      (first.2 middle reached).2.2.2.2.1⟩
  have middleKept (middle : MachineState) (reached : middle ∈ support (s3Group state)) (reg : Reg)
      (h6 : reg ≠ .x6 := by decide) (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide)
      (h18 : reg ≠ .x18 := by decide) (h23 : reg ≠ .x23 := by decide) :
      middle.getReg reg = state.getReg reg :=
    (first.2 middle reached).2.2.2.2.2 reg h6 h10 h12 h18 h23
  have second (middle : MachineState) (reached : middle ∈ support (s3Group state)) :=
    s3_group_execute middle (cursor + 16384) (nonce + 1536) (heap + 2048) finish
      (middleState middle reached) ((middleKept middle reached .x7).trans stride)
      ((middleKept middle reached .x22).trans limit) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) 0
  constructor
  · rw [show 1796 + fuel = 896 + (896 + (4 + fuel)) by omega,
      s4_half_execute w 0 hw (by decide) state cursor nonce heap invariant cursorAligned
        nonceAligned heapAligned (by omega) (by omega) (by omega)]
    simp only [s3Groups, s3Group, bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro leaves reached
    have leavesFacts := (s3_group_leaves_execute 64 0 state cursor nonce heap (by decide) invariant
      cursorAligned nonceAligned heapAligned (by omega) (by omega) (by omega) 0).2 leaves reached
    have leavesStride : leaves.getReg .x7 = BitVec.ofNat 64 2048 :=
      (leavesFacts.2 .x7 (by decide) (by decide) (by decide)).trans stride
    have inSupport : s3LatchState leaves ∈ support (s3Group state) := by
      simp only [s3Group, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨leaves, reached, rfl⟩
    have lag18 : s4Lag18 0 + 1536 = s4Lag18 1 := by decide
    have lag23 : s4Lag23 0 + 2048 = s4Lag23 1 := by decide
    rw [s4_frame_latch _ _ _ leaves leavesStride, lag18, lag23,
      show s4HalfPC w 0 + 3584 = s4HalfPC w 1 by unfold s4HalfPC; omega,
      s4_half_execute w 1 hw (by decide) _ (cursor + 16384) (nonce + 1536) (heap + 2048)
        (middleState _ inSupport) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro leaves' reached'
    have leavesFacts' := (s3_group_leaves_execute 64 0 _ (cursor + 16384) (nonce + 1536)
      (heap + 2048) (by decide) (middleState _ inSupport) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) 0).2 leaves' reached'
    have stride' : leaves'.getReg .x7 = BitVec.ofNat 64 2048 :=
      (leavesFacts'.2 .x7 (by decide) (by decide) (by decide)).trans
        ((middleKept _ inSupport .x7).trans stride)
    have rebase := s3_straight_execute (submission.image .commit) s4RebaseInstructions 4
      (s4HalfPC w 1 + 3584)
      (s4Frame (s4Lag18 1) (s4Lag23 1) (BitVec.ofNat 64 (s4HalfPC w 1 + 3584)) leaves')
      fuel true rfl (s4_frame_pc _ _ _ _) (by decide)
      (fun k bound current currentPC => by
        apply s4_image_window w (1792 + k) hw (by omega) _ current
          (by rw [currentPC]; unfold s4HalfPC; congr 1; omega)
          (s4_rebase_decoded k bound))
      (fun k bound => by interval_cases k <;> rfl)
    rw [rebase.1, s4_rebase_frame _ _ _ _ stride', s4_frame_latch _ _ _ leaves' stride']
    have lag18' : s4Lag18 1 - 3072 + 1536 = s4Lag18 0 := by decide
    have lag23' : s4Lag23 1 - 4096 + 2048 = s4Lag23 0 := by decide
    have pcEq : BitVec.ofNat 64 (s4HalfPC w 1 + 3584) + 16 =
        BitVec.ofNat 64 (s4HalfPC w 0 + 7184) := by
      rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]
      unfold s4HalfPC; congr 1; try omega
    rw [lag18', lag23', pcEq]
    simp only [bind_assoc, pure_bind, Execution.charge]
    refine bind_congr fun result => ?_
    simp only [pure_inj]
    congr 1 <;> omega
  · intro next reachable
    rw [show (2 : Nat) = 1 + 1 by rfl] at reachable
    simp only [s3Groups, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨middle, reached, last, reachedLast, rest⟩ := reachable
    rw [rest]
    have facts := (second middle reached).2 last reachedLast
    refine ⟨?_, facts.2.1, ?_, ?_, ?_, ?_⟩
    · rw [facts.1]
    · rw [facts.2.2.1]
    · rw [facts.2.2.2.1]
    · rw [facts.2.2.2.2.1]
    · intro reg h6 h10 h12 h18 h23
      exact (facts.2.2.2.2.2 reg h6 h10 h12 h18 h23).trans (middleKept middle reached reg h6 h10 h12 h18 h23)

end CommitGolfCandidate
