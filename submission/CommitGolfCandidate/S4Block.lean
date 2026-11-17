import CommitGolfCandidate.S4Loop

/-! Four windows per block, the block-end dispatch, all blocks, and the physical leaf phase. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- `n + 1` consecutive windows starting at window `w`. -/
theorem s4_windows (n : Nat) : ∀ (w : Nat) (state : MachineState) (cursor nonce heap finish : Nat),
    w + (n + 1) ≤ 4 → S3GroupState state 0 cursor nonce heap →
    state.getReg .x7 = BitVec.ofNat 64 2048 → state.getReg .x22 = BitVec.ofNat 64 finish →
    heap + 4096 * (n + 1) ≤ finish →
    cursor % 8 = 0 → nonce % 8 = 0 → heap % 8 = 0 →
    cursor + 32768 * (n + 1) + 16 ≤ MEMORY_BYTES → nonce + 3072 * (n + 1) ≤ MEMORY_BYTES →
    finish + 168 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (1796 * (n + 1) + fuel)
        (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 (s4HalfPC w 0)) state) true =
      (do let next ← s3Groups state (2 * (n + 1))
          let result ← execute (submission.image .commit) fuel
            (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 (s4HalfPC (w + (n + 1)) 0)) next) true
          return result.charge (3588 * (n + 1)) (256 * (n + 1))) := by
  induction n with
  | zero =>
    intro w state cursor nonce heap finish bound invariant stride limit more cursorAligned
      nonceAligned heapAligned cursorBound nonceBound finishBound fuel
    have run := (s4_window_execute w (by omega) state cursor nonce heap finish invariant stride limit
      (by omega) cursorAligned nonceAligned heapAligned (by omega) (by omega) finishBound fuel).1
    rw [show s4HalfPC (w + (0 + 1)) 0 = s4HalfPC w 0 + 7184 by unfold s4HalfPC; omega]
    simpa using run
  | succ n ih =>
    intro w state cursor nonce heap finish bound invariant stride limit more cursorAligned
      nonceAligned heapAligned cursorBound nonceBound finishBound fuel
    have window := s4_window_execute w (by omega) state cursor nonce heap finish invariant stride
      limit (by omega) cursorAligned nonceAligned heapAligned (by omega) (by omega) finishBound
      (1796 * (n + 1) + fuel)
    rw [show 1796 * (n + 1 + 1) + fuel = 1796 + (1796 * (n + 1) + fuel) by ring, window.1,
      show 2 * (n + 1 + 1) = 2 + 2 * (n + 1) by ring, s3_groups_add]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    have facts := window.2 next reached
    have nextState : S3GroupState next 0 (cursor + 32768) (nonce + 3072) (heap + 4096) :=
      ⟨by rw [facts.pc, if_pos (by omega)], facts.ready, facts.input, facts.nonces, facts.slots⟩
    rw [show s4HalfPC w 0 + 7184 = s4HalfPC (w + 1) 0 by unfold s4HalfPC; omega,
      ih (w + 1) next (cursor + 32768) (nonce + 3072) (heap + 4096) finish (by omega) nextState
        ((facts.kept .x7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans stride)
        ((facts.kept .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans limit)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) finishBound fuel,
      show w + 1 + (n + 1) = w + (n + 1 + 1) by omega]
    simp only [bind_assoc, pure_bind, Execution.charge]
    refine bind_congr fun last => ?_
    refine bind_congr fun result => ?_
    simp only [pure_inj]
    congr 1 <;> ring

theorem s4_frame_setPC (a b p q : Word) (state : MachineState) :
    (s4Frame a b p state).setPC q = s4Frame a b q state := by
  cases state; rfl

theorem s4_frame_jal (a b p : Word) (state : MachineState) (offset : BitVec 21) :
    execInstrBr (s4Frame a b p state) (.JAL .x0 offset) = s4Frame a b (p + signExtend21 offset) state := by
  simp only [execInstrBr, MachineState.setReg, s4_frame_pc, s4_frame_setPC]

/-- Block end: the forward branch either returns to the block start or removes the bias
and jumps to the retained nonce repair. -/
theorem s4_end_loop (state : MachineState) (heap finish : Nat)
    (slots : state.getReg .x23 = BitVec.ofNat 64 heap)
    (limit : state.getReg .x22 = BitVec.ofNat 64 finish)
    (more : heap < finish) (aligned : heap + 2048 < finish) (finishBound : finish < 2 ^ 63)
    (fuel : Nat) :
    execute (submission.image .commit) (2 + fuel)
        (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state) true =
      (do let result ← execute (submission.image .commit) fuel
            (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1015228) state) true
          return result.charge 2 0) := by
  have ult : BitVec.ult ((s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state).getReg .x23)
      ((s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state).getReg .x22) = true := by
    rw [s4_frame_x23, s4_frame_getReg _ _ _ _ _ (by decide) (by decide), slots, limit]
    simp only [BitVec.ult, decide_eq_true_eq]
    rw [show s4Lag23 0 = BitVec.ofNat 64 (2 ^ 64 - 2048) by decide]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have first : ordinaryStep (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state)
      (.base (.BGEU .x23 .x22 8)) =
      some (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043968) state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, execInstrBr, ult,
      not_true_eq_false, ite_false, s4_frame_pc, s4_frame_setPC]
    rfl
  have second : ordinaryStep (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043968) state)
      (.base (.JAL .x0 2068412)) =
      some (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1015228) state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, s4_frame_jal]
    rfl
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ (s4_image_end 0 (by decide) _ (s4_frame_pc _ _ _ _)) first,
    execute_ordinary_step _ _ _ _ _ _ (s4_image_end 1 (by decide) _ (s4_frame_pc _ _ _ _)) second]
  simp only [Execution.charge, s4EndInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, instructionCycles, bind_assoc, pure_bind,
    bind_pure_comp, Functor.map_map]
  ring_nf

theorem s4_end_exit (state : MachineState) (finish : Nat)
    (pc : state.pc = BitVec.ofNat 64 1015020)
    (slots : state.getReg .x23 = BitVec.ofNat 64 finish)
    (limit : state.getReg .x22 = BitVec.ofNat 64 finish) (finishBound : finish < 2 ^ 63)
    (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel)
        (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state) true =
      (do let result ← execute (submission.image .commit) fuel state true
          return result.charge 4 0) := by
  have ult : BitVec.ult ((s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state).getReg .x23)
      ((s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state).getReg .x22) = false := by
    rw [s4_frame_x23, s4_frame_getReg _ _ _ _ _ (by decide) (by decide), slots, limit]
    simp only [BitVec.ult, decide_eq_false_iff_not, not_lt]
    rw [show s4Lag23 0 = BitVec.ofNat 64 (2 ^ 64 - 2048) by decide]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have s8 : signExtend13 (8 : BitVec 13) = 8 := by decide
  have first : ordinaryStep (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043964) state)
      (.base (.BGEU .x23 .x22 8)) =
      some (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043972) state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, execInstrBr, ult,
      Bool.false_eq_true, not_false_eq_true, ite_true, s4_frame_pc, s4_frame_setPC, s8]
    rfl
  have second : ordinaryStep (s4Frame (s4Lag18 0) (s4Lag23 0) (BitVec.ofNat 64 1043972) state)
      (.base (.ADDI .x18 .x18 (-1536))) =
      some (s4Frame 0 (s4Lag23 0) (BitVec.ofNat 64 1043976) state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, s4_frame_addi18]
    congr 2 <;> decide
  have third : ordinaryStep (s4Frame 0 (s4Lag23 0) (BitVec.ofNat 64 1043976) state)
      (.base (.ADDI .x23 .x23 (-2048))) =
      some (s4Frame 0 0 (BitVec.ofNat 64 1043980) state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, s4_frame_addi23]
    congr 2 <;> decide
  have fourth : ordinaryStep (s4Frame 0 0 (BitVec.ofNat 64 1043980) state)
      (.base (.JAL .x0 2068192)) = some state := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ite_true, s4_frame_jal]
    rw [s4_frame_zero _ state (by rw [pc]; decide)]
  rw [show 4 + fuel = (((fuel + 1) + 1) + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ (s4_image_end 0 (by decide) _ (s4_frame_pc _ _ _ _)) first,
    execute_ordinary_step _ _ _ _ _ _ (s4_image_end 2 (by decide) _ (s4_frame_pc _ _ _ _)) second,
    execute_ordinary_step _ _ _ _ _ _ (s4_image_end 3 (by decide) _ (s4_frame_pc _ _ _ _)) third,
    execute_ordinary_step _ _ _ _ _ _ (s4_image_end 4 (by decide) _ (s4_frame_pc _ _ _ _)) fourth]
  simp only [Execution.charge, s4EndInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, instructionCycles, bind_assoc, pure_bind,
    bind_pure_comp, Functor.map_map]
  ring_nf

end CommitGolfCandidate
