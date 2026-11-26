import CommitGolfCandidate.CommitLeaf

import CommitGolfCandidate.TruncFetch

namespace CommitGolfCandidate.Trunc

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

set_option maxHeartbeats 1200000

theorem exec_leaf_prep (state : MachineState) (j : Nat) (hj : j < 32)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j)))
    (salt0Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j)) 8 = true)
    (salt1Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j + 8)) 8 = true)
    (slotValid : ∀ w : Fin 3, accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * w.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (6 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (leafPrepState state j) true
          return result.charge 6 0) := by
  apply execute_unit_steps (states := leafPrepPrefix state j)
  intro i hi
  refine ⟨.base ((leafPrepInstrs j)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply prefixFetch _ (34 + 17 * j + i) _ (by omega)
    · interval_cases i
      · exact pc
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc]
        apply ofNat64_add_eq _ 4 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (8 : Word) = _
        apply ofNat64_add_eq _ 8 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (12 : Word) = _
        apply ofNat64_add_eq _ 12 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (16 : Word) = _
        apply ofNat64_add_eq _ 16 _; omega
      · simp only [leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr, MachineState.setPC, pc, BitVec.add_assoc]
        change BitVec.ofNat 64 _ + (20 : Word) = _
        apply ofNat64_add_eq _ 20 _; omega
    · have hd := commit_leaf_decode j i hj (by omega)
      interval_cases i <;> exact hd
  · have r18 := leaf_prep_prefix_reg state j i (by omega) .x18 (by decide) (by decide)
    have r10 := leaf_prep_prefix_reg state j i (by omega) .x10 (by decide) (by decide)
    have s0 := signExtend12_salt0 ⟨j, hj⟩
    have s1 := signExtend12_salt1 ⟨j, hj⟩
    have w0 := slotValid ⟨0, by decide⟩
    have w1 := slotValid ⟨1, by decide⟩
    have w2 := slotValid ⟨2, by decide⟩
    have valid : memoryArgumentsValid (leafPrepPrefix state j i)
        ((leafPrepInstrs j)[i]?.getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [leafPrepInstrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, r18, r10]
      · rw [s0]; exact salt0Valid
      · simpa [signExtend12] using w0
      · rw [s1]; exact salt1Valid
      · simpa [signExtend12] using w1
      · simpa [signExtend12] using w2
    interval_cases i <;>
      simp only [leafPrepInstrs, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem exec_two_addi_ecall (state : MachineState) (j m : Nat) (hj : j < 32)
    (hm : m = 7 ∨ m = 10 ∨ m = 13)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + m)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (dx : Nat) (hdx : dx = if m = 7 then 56 else 64)
    (outAddr : Word)
    (hout : outAddr = if m = 13 then state.getReg .x23 + BitVec.ofNat 64 (heapOffset j)
                      else state.getReg .x10 + BitVec.ofNat 64 (dx + 64))
    (sv : rangeValid (state.getReg .x10 + BitVec.ofNat 64 dx) 96 = true)
    (sa : (state.getReg .x10 + BitVec.ofNat 64 dx).toNat % 8 = 0)
    (dv : rangeValid outAddr 32 = true)
    (da : outAddr.toNat % 8 = 0)
    (fuel : Nat) :
    let nextX10 := state.getReg .x10 + BitVec.ofNat 64 dx
    let ready := ((state.setReg .x10 nextX10).setReg .x12 outAddr).setPC (state.pc + 8)
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (.inl (readBuffer state nextX10.toNat 96)))
          let result ← execute (submission.image .commit) fuel (writeBits ready outAddr answer) true
          return result.charge 10 1) := by
  dsimp only
  let nextX10 := state.getReg .x10 + BitVec.ofNat 64 dx
  let mid := (state.setReg .x10 nextX10).setPC (state.pc + 4)
  let ready := ((state.setReg .x10 nextX10).setReg .x12 outAddr).setPC (state.pc + 8)
  have hpc1 : mid.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + (m + 1))) := by
    change state.pc + 4 = _
    rw [pc]
    apply ofNat64_add_eq _ 4 _; omega
  have hpc2 : ready.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + (m + 2))) := by
    change state.pc + 8 = _
    rw [pc]
    apply ofNat64_add_eq _ 8 _; omega
  have f0 : fetch (submission.image .commit) state = some (.base (leafLaneInstr j m)) :=
    prefixFetch state (34 + 17 * j + m) _ (by rcases hm with rfl | rfl | rfl <;> omega) pc
      (commit_leaf_decode j m hj (by rcases hm with rfl | rfl | rfl <;> omega))
  have f1 : fetch (submission.image .commit) mid = some (.base (leafLaneInstr j (m + 1))) :=
    prefixFetch mid (34 + 17 * j + (m + 1)) _ (by rcases hm with rfl | rfl | rfl <;> omega) hpc1
      (commit_leaf_decode j (m + 1) hj (by rcases hm with rfl | rfl | rfl <;> omega))
  have f2 : fetch (submission.image .commit) ready = some (.base .ECALL) :=
    prefixFetch ready (34 + 17 * j + (m + 2)) .ECALL (by rcases hm with rfl | rfl | rfl <;> omega) hpc2
      (by rcases hm with rfl | rfl | rfl <;> exact commit_leaf_decode j _ hj (by omega))
  have s0 : ordinaryStep state (.base (leafLaneInstr j m)) = some mid := by
    rcases hm with rfl | rfl | rfl <;> subst hdx <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        signExtend12, mid, nextX10]
  have h44 : (4 : Word) + 4 = 8 := by decide
  have s1 : ordinaryStep mid (.base (leafLaneInstr j (m + 1))) = some ready := by
    rcases hm with rfl | rfl | rfl
    · subst hdx; subst hout
      have h56 : BitVec.ofNat 64 56 + (64 : Word) = BitVec.ofNat 64 (56 + 64) := by decide
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        signExtend12, mid, ready, nextX10, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, BitVec.add_assoc, h44, h56]
    · subst hdx; subst hout
      have h64 : BitVec.ofNat 64 64 + (64 : Word) = BitVec.ofNat 64 (64 + 64) := by decide
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        signExtend12, mid, ready, nextX10, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, BitVec.add_assoc, h44, h64]
    · subst hdx; subst hout
      have sheap := signExtend12_heapOffset ⟨j, hj⟩
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, leafLaneInstr,
        mid, ready, nextX10, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, BitVec.add_assoc, sheap, h44]
  have rr5 : ready.getReg .x5 = 0 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r5]
  have rr11 : ready.getReg .x11 = 96 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r11]
  have rr13 : ready.getReg .x13 = 0 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, r13]
  have rr10 : ready.getReg .x10 = nextX10 := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]
  have rr12 : ready.getReg .x12 = outAddr := by
    simp [ready, MachineState.getReg_setPC, MachineState.getReg_setReg_eq]
  have sameMem : ready.mem = state.mem := rfl
  have rmem : readBuffer ready nextX10.toNat 96 = readBuffer state nextX10.toNat 96 := by
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have hinput : oracleInput ready = some (.inl (readBuffer state nextX10.toNat 96)) := by
    have h := oracleInput_compression ready rr11 rr13
      (by rw [rr10]; exact sv) (by rw [rr10]; exact sa)
      (by rw [rr12]; exact dv) (by rw [rr12]; exact da)
    rwa [rr10, rmem] at h
  rw [show 3 + fuel = ((fuel + 1) + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0,
    execute_ordinary_step _ _ _ _ _ _ f1 s1,
    execute, f2, if_pos rr5, hinput]
  simp only [writeOracleAnswer, rr12, bind_assoc, pure_bind]
  have c0 : instructionCycles (.base (leafLaneInstr j m)) = 1 := by
    rcases hm with rfl | rfl | rfl <;> rfl
  have c1 : instructionCycles (.base (leafLaneInstr j (m + 1))) = 1 := by
    rcases hm with rfl | rfl | rfl <;> rfl
  rw [c0, c1]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer state nextX10.toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, charge_charge]
  rfl

theorem commit_leaf_lane (state : MachineState) (j : Nat) (hj : j < 32)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 280 ≤ MEMORY_BYTES)
    (salt0Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j)) 8 = true)
    (salt1Valid : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * j + 8)) 8 = true)
    (heap : Nat) (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (17 + fuel) state true =
      (do let finished ← leafLaneRun state j
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 45 4) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have hOff : heapOffset j + 32 ≤ 1536 := by
    have := heap_offset_bound j 16 (by omega); omega
  have hOffAl : heapOffset j % 8 = 0 := heap_offset_aligned j
  have slotAccess : ∀ w : Fin 3, accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * w.val)) 8 = true := by
    intro w
    have hw := w.isLt
    simp only [accessValid, rangeValid, slotPtr, pointer_offset_nat slot (8 * w.val) (by omega),
      Bool.and_eq_true, decide_eq_true_eq]
    constructor <;> omega
  -- Helper for aligned offsets from slot
  have slotOffNat (off : Nat) (hb : off ≤ 280) :
      (state.getReg .x10 + BitVec.ofNat 64 off).toNat = slot + off := by
    rw [slotPtr]; exact pointer_offset_nat slot off (by omega)
  have heapOffNat : (state.getReg .x23 + BitVec.ofNat 64 (heapOffset j)).toNat = heap + heapOffset j := by
    rw [heapPtr]; exact pointer_offset_nat heap (heapOffset j) (by omega)
  -- Execute prep (6 instructions)
  rw [show 17 + fuel = 6 + (1 + (3 + (3 + (3 + (1 + fuel))))) by omega,
    exec_leaf_prep state j hj pc salt0Valid salt1Valid slotAccess]
  simp only [leafLaneRun, bind_assoc, pure_bind]
  -- Call 0 ECALL at index 34 + 17*j + 6
  let p0 := leafPrepState state j
  have p0pc : p0.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 6)) := by
    dsimp only [p0]; rw [leaf_prep_pc, pc]
    apply ofNat64_add_eq _ 24 _; omega
  have p0r5 : p0.getReg .x5 = 0 := (leaf_prep_prefix_reg state j 6 (by decide) .x5 (by decide) (by decide)).trans r5
  have p0r11 : p0.getReg .x11 = 96 := (leaf_prep_prefix_reg state j 6 (by decide) .x11 (by decide) (by decide)).trans r11
  have p0r13 : p0.getReg .x13 = 0 := (leaf_prep_prefix_reg state j 6 (by decide) .x13 (by decide) (by decide)).trans r13
  have p0r10 : p0.getReg .x10 = state.getReg .x10 := leaf_prep_prefix_reg state j 6 (by decide) .x10 (by decide) (by decide)
  have p0r12 : (leafPrepState state j).getReg .x12 = state.getReg .x10 + 56 := leaf_prep_x12 state j
  have p0r23 : p0.getReg .x23 = state.getReg .x23 := leaf_prep_prefix_reg state j 6 (by decide) .x23 (by decide) (by decide)
  have f0 : fetch (submission.image .commit) p0 = some (.base .ECALL) :=
    prefixFetch p0 (34 + 17 * j + 6) .ECALL (by omega) p0pc (commit_leaf_decode j 6 hj (by decide))
  have s0nat : (state.getReg .x10).toNat = slot := by rw [slotPtr]; exact word_small_toNat slot (by omega)
  have d0nat : (state.getReg .x10 + 56).toNat = slot + 56 := slotOffNat 56 (by omega)
  have inp0 : oracleInput p0 = some (.inl (readBuffer p0 (state.getReg .x10).toNat 96)) := by
    have sv0 : rangeValid (p0.getReg .x10) 96 = true := by
      simp only [rangeValid, p0r10, s0nat, decide_eq_true_eq]; omega
    have sa0 : (p0.getReg .x10).toNat % 8 = 0 := by rw [p0r10, s0nat]; omega
    have dv0 : rangeValid (p0.getReg .x12) 32 = true := by
      dsimp only [p0]; simp only [rangeValid, p0r12, d0nat, decide_eq_true_eq]; omega
    have da0 : (p0.getReg .x12).toNat % 8 = 0 := by dsimp only [p0]; rw [p0r12, d0nat]; omega
    have h := oracleInput_compression p0 p0r11 p0r13 sv0 sa0 dv0 da0
    rwa [p0r10] at h
  rw [show 1 + (3 + (3 + (3 + (1 + fuel)))) = (3 + (3 + (3 + (1 + fuel)))) + 1 by omega,
    execute, f0, if_pos p0r5, inp0]
  simp only [writeOracleAnswer, p0r12, bind_assoc, pure_bind]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer p0 (state.getReg .x10).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a0
  change BitVec 256 at a0
  let s1 := leafCall0State state j a0
  have s1pc : s1.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 7)) := by
    dsimp only [s1]; rw [leafCall0State, writeBits_pc, p0pc]
    apply ofNat64_add_eq _ 4 _; omega
  have s1r5 : s1.getReg .x5 = 0 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r5
  have s1r11 : s1.getReg .x11 = 96 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r11
  have s1r13 : s1.getReg .x13 = 0 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r13
  have s1r10 : s1.getReg .x10 = state.getReg .x10 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r10
  have s1r23 : s1.getReg .x23 = state.getReg .x23 := by dsimp only [s1]; rw [leafCall0State, writeBits_register]; exact p0r23
  -- Call 1 (3 instructions at +7..+9)
  have s1_56 : (s1.getReg .x10 + BitVec.ofNat 64 56).toNat = slot + 56 := by rw [s1r10]; exact d0nat
  have s1_120 : (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64)).toNat = slot + 120 := by
    rw [s1r10]; exact slotOffNat 120 (by omega)
  have c1 := exec_two_addi_ecall s1 j 7 hj (Or.inl rfl) s1pc s1r5 s1r11 s1r13 56 rfl
    (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64)) rfl
    (by simp only [rangeValid, s1_56, decide_eq_true_eq]; omega) (by rw [s1_56]; omega)
    (by simp only [rangeValid, s1_120, decide_eq_true_eq]; omega) (by rw [s1_120]; omega)
    (3 + (3 + (1 + fuel)))
  have hs1 : @writeBits COMPRESSION_OUTPUT_LENGTH (leafPrepState state j) (state.getReg .x10 + 56) a0 = s1 := rfl
  rw [hs1, c1]
  simp only [bind_assoc, pure_bind]
  rw [show (s1.getReg .x10 + BitVec.ofNat 64 56).toNat = (state.getReg .x10 + 56).toNat by rw [s1r10]; rfl]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer s1 (state.getReg .x10 + 56).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a1
  change BitVec 256 at a1
  let s2 := leafCall1State s1 a1
  have s2eq : @writeBits COMPRESSION_OUTPUT_LENGTH (((s1.setReg .x10 (s1.getReg .x10 + BitVec.ofNat 64 56)).setReg .x12
      (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64))).setPC (s1.pc + 8))
      (s1.getReg .x10 + BitVec.ofNat 64 (56 + 64)) a1 = s2 := rfl
  rw [s2eq]
  have s2pc : s2.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 10)) := by
    have h84 : (8 : Word) + 4 = 12 := by decide
    change s1.pc + 8 + 4 = _
    rw [s1pc, BitVec.add_assoc, h84]
    apply ofNat64_add_eq _ 12 _; omega
  have s2r5 : s2.getReg .x5 = 0 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r5
  have s2r11 : s2.getReg .x11 = 96 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r11
  have s2r13 : s2.getReg .x13 = 0 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r13
  have s2r10 : s2.getReg .x10 = s1.getReg .x10 + 56 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide)]
  have s2r23 : s2.getReg .x23 = state.getReg .x23 := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s1r23
  -- Call 2 (3 instructions at +10..+12)
  have s2_64_eq : s2.getReg .x10 + BitVec.ofNat 64 64 = s1.getReg .x10 + 120 := by
    rw [s2r10, BitVec.add_assoc]; rfl
  have s2_64 : (s2.getReg .x10 + BitVec.ofNat 64 64).toNat = slot + 120 := by
    rw [s2_64_eq, s1r10]; exact slotOffNat 120 (by omega)
  have s2_128 : (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64)).toNat = slot + 184 := by
    rw [s2r10, s1r10, BitVec.add_assoc]
    exact slotOffNat 184 (by omega)
  have c2 := exec_two_addi_ecall s2 j 10 hj (Or.inr (Or.inl rfl)) s2pc s2r5 s2r11 s2r13 64 rfl
    (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64)) rfl
    (by simp only [rangeValid, s2_64, decide_eq_true_eq]; omega) (by rw [s2_64]; omega)
    (by simp only [rangeValid, s2_128, decide_eq_true_eq]; omega) (by rw [s2_128]; omega)
    (3 + (1 + fuel))
  rw [c2]
  simp only [bind_assoc, pure_bind]
  rw [show (s2.getReg .x10 + BitVec.ofNat 64 64).toNat = (s1.getReg .x10 + 120).toNat by rw [s2_64_eq]]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer s2 (s1.getReg .x10 + 120).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a2
  change BitVec 256 at a2
  let s3 := leafCall2State s2 a2
  have s3eq : @writeBits COMPRESSION_OUTPUT_LENGTH (((s2.setReg .x10 (s2.getReg .x10 + BitVec.ofNat 64 64)).setReg .x12
      (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64))).setPC (s2.pc + 8))
      (s2.getReg .x10 + BitVec.ofNat 64 (64 + 64)) a2 = s3 := rfl
  rw [s3eq]
  have s3pc : s3.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 13)) := by
    have h84 : (8 : Word) + 4 = 12 := by decide
    change s2.pc + 8 + 4 = _
    rw [s2pc, BitVec.add_assoc, h84]
    apply ofNat64_add_eq _ 12 _; omega
  have s3r5 : s3.getReg .x5 = 0 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r5
  have s3r11 : s3.getReg .x11 = 96 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r11
  have s3r13 : s3.getReg .x13 = 0 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r13
  have s3r10 : s3.getReg .x10 = s2.getReg .x10 + 64 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide)]
  have s3r23 : s3.getReg .x23 = state.getReg .x23 := by
    dsimp only [s3]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide)]
    exact s2r23
  -- Call 3 (3 instructions at +13..+15)
  have s3_64_eq : s3.getReg .x10 + BitVec.ofNat 64 64 = s2.getReg .x10 + 128 := by
    rw [s3r10, BitVec.add_assoc]; rfl
  have s3_64 : (s3.getReg .x10 + BitVec.ofNat 64 64).toNat = slot + 184 := by
    rw [s3_64_eq]; exact s2_128
  have s3_heap : (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j)).toNat = heap + heapOffset j := by
    rw [s3r23]; exact heapOffNat
  have c3 := exec_two_addi_ecall s3 j 13 hj (Or.inr (Or.inr rfl)) s3pc s3r5 s3r11 s3r13 64 rfl
    (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j)) rfl
    (by simp only [rangeValid, s3_64, decide_eq_true_eq]; omega) (by rw [s3_64]; omega)
    (by simp only [rangeValid, s3_heap, decide_eq_true_eq]; omega) (by rw [s3_heap]; omega)
    (1 + fuel)
  rw [c3]
  simp only [bind_assoc, pure_bind]
  rw [show (s3.getReg .x10 + BitVec.ofNat 64 64).toNat = (s2.getReg .x10 + 128).toNat by rw [s3_64_eq]]
  apply congrArg (fun k =>
    (liftM (World.query (.inr (.inl (readBuffer s3 (s2.getReg .x10 + 128).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= k)
  funext a3
  change BitVec 256 at a3
  let s4 := leafCall3State s3 j a3
  have s4eq : @writeBits COMPRESSION_OUTPUT_LENGTH (((s3.setReg .x10 (s3.getReg .x10 + BitVec.ofNat 64 64)).setReg .x12
      (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j))).setPC (s3.pc + 8))
      (s3.getReg .x23 + BitVec.ofNat 64 (heapOffset j)) a3 = s4 := rfl
  rw [s4eq]
  have s4pc : s4.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * j + 16)) := by
    have h84 : (8 : Word) + 4 = 12 := by decide
    change s3.pc + 8 + 4 = _
    rw [s3pc, BitVec.add_assoc, h84]
    apply ofNat64_add_eq _ 12 _; omega
  -- Final instruction: addi x10, x10, 72
  have fAdv : fetch (submission.image .commit) s4 = some (.base (.ADDI .x10 .x10 72)) :=
    prefixFetch s4 (34 + 17 * j + 16) (.ADDI .x10 .x10 72) (by omega) s4pc
      (commit_leaf_decode j 16 hj (by decide))
  have sAdv : ordinaryStep s4 (.base (.ADDI .x10 .x10 72)) = some (leafAdvanceState s4) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, leafAdvanceState]
  rw [show 1 + fuel = fuel + 1 by omega, execute_ordinary_step _ _ _ _ _ _ fAdv sAdv]
  simp [oracleCycles, COMPRESSION_CYCLES, instructionCycles, charge_charge]
  rfl

end CommitGolfCandidate.Trunc
