import CommitGolfCandidate.CommitLeaf

/-! Commitment execution: initialize the heap and salt pointers, sample all 128-bit
salts once, execute 32-leaf unrolled blocks, and copy the root. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def commitLoad (reg : Reg) (high : BitVec 12) : List Instr :=
  [.ADDI reg .x0 0, .SLLI reg reg 11, .ADDI reg reg high,
   .SLLI reg reg 11, .ADDI reg reg 0, .SLLI reg reg 11, .ADDI reg reg 0]

private def commitSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 4072, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0] ++
  commitLoad .x6 384 ++ [.ADD .x18 .x9 .x6] ++
  commitLoad .x6 192 ++ [.ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0] ++
  commitLoad .x11 64 ++ [.ADD .x20 .x18 .x11]

private def commitSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitSetupInstructions.take count).foldl execInstrBr state

def commitSetupState (state : MachineState) : MachineState := commitSetupPrefix state 29

set_option maxHeartbeats 1600000 in
/-- The 29-instruction setup computes pointers into the admitted private trapdoor,
the 16*n salt length, and the salt-end sentinel `x20 = x18 + 16*n`. -/
theorem commit_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (29 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSetupState state) allowCoins
          return result.charge 29 0) := by
  apply execute_unit_steps (states := commitSetupPrefix state)
  intro i hi
  refine ⟨.base ((commitSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [commitSetupPrefix, commitSetupInstructions, commitLoad, execInstrBr, pc,
          MachineState.setPC]
    · have hf := commit_filtered_preRandom i (by omega)
      interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- Exact ABI-derived registers at the randomness syscall. -/
theorem commit_setup_registers (state : MachineState) :
    (commitSetupState state).getReg .x5 = 2 ∧
    (commitSetupState state).getReg .x8 = state.getReg .x10 + 18446744073709551592 ∧
    (commitSetupState state).getReg .x9 = state.getReg .x12 ∧
    (commitSetupState state).getReg .x10 = state.getReg .x12 + 1610612736 ∧
    (commitSetupState state).getReg .x11 = 268435456 ∧
    (commitSetupState state).getReg .x18 = state.getReg .x12 + 1610612736 ∧
    (commitSetupState state).getReg .x23 = state.getReg .x12 + 805306368 ∧
    (commitSetupState state).getReg .x26 = state.getReg .x11 ∧
    (commitSetupState state).getReg .x20 = state.getReg .x12 + 1879048192 := by
  dsimp only [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
    List.append, List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    BitVec.add_assoc]

theorem commit_setup_pc (state : MachineState) (pc : state.pc = 4096) :
    (commitSetupState state).pc = 4212 := by
  simp [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
    execInstrBr, MachineState.setPC, pc]

/-- The real RANDOM syscall samples the 16*n salt buffer with private coins. -/
theorem commit_random (state : MachineState) (pc : state.pc = 4212)
    (selector : state.getReg .x5 = 2) (valid : randomArgumentsValid state = true)
    (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8 * (state.getReg .x11).toNat) :
            ProbComp (BitVec (8 * (state.getReg .x11).toNat)))
          let result ← execute (submission.image .commit) fuel
            (writeBits state (state.getReg .x10) answer) true
          return result.charge (1 + ((state.getReg .x11).toNat + 7) / 8) 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ 29 _ (by decide) pc
    rw [commit_code_word_at _ _ (commit_filtered_preRandom 29 (by decide))]; rfl
  rw [Nat.add_comm 1 fuel, execute, fetched]
  simp only [selector, valid]
  rfl

private def commitReadyInstructions : List Instr :=
  [.ADDI .x10 .x8 0, .ADDI .x5 .x0 0, .ADDI .x11 .x0 96, .ADDI .x13 .x0 0]

private def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

def commitReadyState (state : MachineState) : MachineState := commitReadyPrefix state 4

/-- Initialize `x10 := x8` (first leaf slot) and the constant compression arguments after RANDOM. -/
theorem commit_ready (state : MachineState) (pc : state.pc = 4216) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitReadyState state) true
          return result.charge 4 0) := by
  apply execute_unit_steps (states := commitReadyPrefix state)
  intro i hi
  refine ⟨.base ((commitReadyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (30 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]
    · have hf := commit_filtered_preRandom (30 + i) (by omega)
      interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_ready_pc (state : MachineState) (pc : state.pc = 4216) :
    (commitReadyState state).pc = 4232 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]

theorem commit_ready_regs (state : MachineState) :
    (commitReadyState state).getReg .x10 = state.getReg .x8 ∧
    (commitReadyState state).getReg .x5 = 0 ∧
    (commitReadyState state).getReg .x11 = 96 ∧
    (commitReadyState state).getReg .x13 = 0 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_ready_register (state : MachineState) (reg : Reg)
    (not10 : reg ≠ .x10) (not5 : reg ≠ .x5)
    (not11 : reg ≠ .x11) (not13 : reg ≠ .x13) :
    (commitReadyState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitReadyState, commitReadyPrefix, commitReadyInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-! ### 32-leaf unrolled block execution -/

/-- Run `count` consecutive leaf lanes starting at lane `start` (`start + count ≤ 32`). -/
def leafBlockLanes (state : MachineState) (start : Nat) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let next ← leafLaneRun state start
      leafBlockLanes next (start + 1) count

/-- Leaf loop latch at indices 578..580 (`pc = 6408`): `x18 += 512`, `x23 += 1536`,
branch back to `4232` while `x18 ≠ x20`, else exit to `6420`. -/
def commitBlockNextState (state : MachineState) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18 + 512)).setReg .x23 (state.getReg .x23 + 1536)).setPC
    (if state.getReg .x18 + 512 = state.getReg .x20 then 6420 else 4232)

private def commitLatchInstructions : List Instr :=
  [.ADDI .x18 .x18 512, .ADDI .x23 .x23 1536]

private def commitLatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitLatchInstructions.take count).foldl execInstrBr state

theorem commit_block_latch (state : MachineState) (pc : state.pc = 6408) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitBlockNextState state) true
          return result.charge 3 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (commitLatchPrefix state 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := commitLatchPrefix state)
    intro i hi
    refine ⟨.base ((commitLatchInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (578 + i) _ (by omega)
      · interval_cases i <;> simp [commitLatchPrefix, commitLatchInstructions, execInstrBr, pc, MachineState.setPC]
      · have hf := commit_filtered_leafLatch i (by omega)
        interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (commitLatchPrefix state 2) =
      some (.base (.BNE .x18 .x20 6008)) := by
    apply commit_fetch _ 580 _ (by decide)
    · simp [commitLatchPrefix, commitLatchInstructions, execInstrBr, pc, MachineState.setPC]
    · have hb := commit_code_branch_at 580 1 18 20 "commit-block" 34
        (commit_filtered_leafLatch 2 (by decide)) (by rw [commit_labelPositions]; rfl)
      rw [hb]; rfl
  have stepped : ordinaryStep (commitLatchPrefix state 2) (.base (.BNE .x18 .x20 6008)) =
      some (commitBlockNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      commitLatchPrefix, commitLatchInstructions, commitBlockNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, pc]
    split <;> simp_all
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, charge_charge]

/-- One complete 32-leaf block: 32 unrolled lanes followed by the 3-instruction latch. -/
def commitBlockRun (state : MachineState) : OracleComp World MachineState := do
  let hashed ← leafBlockLanes state 0 32
  return commitBlockNextState hashed

theorem leaf_block_lanes_registers (state finished : MachineState) (start count : Nat)
    (reachable : finished ∈ support (leafBlockLanes state start count)) :
    finished.getReg .x10 = state.getReg .x10 + BitVec.ofNat 64 (256 * count) ∧
    finished.pc = state.pc + BitVec.ofNat 64 (68 * count) ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → finished.getReg reg = state.getReg reg := by
  induction count generalizing state start with
  | zero =>
    simp only [leafBlockLanes, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [leafBlockLanes, mem_support_bind_iff] at reachable
    obtain ⟨next, hnext, hrest⟩ := reachable
    have r1 := leaf_lane_registers state next start hnext
    have r2 := ih next (start + 1) hrest
    refine ⟨?_, ?_, ?_⟩
    · rw [r2.1, r1.1, BitVec.add_assoc]
      change state.getReg .x10 + (BitVec.ofNat 64 256 + BitVec.ofNat 64 (256 * count)) = _
      rw [← BitVec.ofNat_add]
      exact congrArg (fun n => state.getReg .x10 + BitVec.ofNat 64 n) (by omega)
    · rw [r2.2.1, r1.2.1, BitVec.add_assoc]
      change state.pc + (BitVec.ofNat 64 68 + BitVec.ofNat 64 (68 * count)) = _
      rw [← BitVec.ofNat_add]
      exact congrArg (fun n => state.pc + BitVec.ofNat 64 n) (by omega)
    · intro reg n6 n10 n12
      exact (r2.2.2 reg n6 n10 n12).trans (r1.2.2 reg n6 n10 n12)

section
attribute [local irreducible] execute

/-- Execute `count` consecutive leaf lanes (`start + count ≤ 32`). -/
theorem commit_leaf_lanes (state : MachineState) (start count : Nat)
    (bounded : start + count ≤ 32)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * start)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 24 + 256 * count ≤ MEMORY_BYTES)
    (saltValid : ∀ word < 64,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (heap : Nat) (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (17 * count + fuel) state true =
      (do let finished ← leafBlockLanes state start count
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (45 * count) (4 * count)) := by
  induction count generalizing state start slot with
  | zero => simp [leafBlockLanes, Execution.charge]
  | succ count ih =>
    have s0v : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * start)) 8 = true := by
      simpa [show 8 * (2 * start) = 16 * start by clear * -; omega] using
        saltValid (2 * start) (by clear * - bounded; omega)
    have s1v : accessValid (state.getReg .x18 + BitVec.ofNat 64 (16 * start + 8)) 8 = true := by
      simpa [show 8 * (2 * start + 1) = 16 * start + 8 by clear * -; omega] using
        saltValid (2 * start + 1) (by clear * - bounded; omega)
    have hslot : slot + 280 ≤ MEMORY_BYTES := Nat.le_trans (by clear * -; omega) slotBound
    have hstep := commit_leaf_lane state start (by clear * - bounded; omega) pc r5 r11 r13
      slot slotPtr slotAligned hslot s0v s1v heap heapPtr heapAligned heapBound (17 * count + fuel)
    rw [show 17 * (count + 1) + fuel = 17 + (17 * count + fuel) by clear * -; omega, hstep]
    simp only [leafBlockLanes, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next hnext
    have regs := leaf_lane_registers state next start hnext
    have nextPC : next.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * (start + 1))) := by
      rw [regs.2.1, pc]
      apply ofNat64_add_eq _ 68 _; clear * -; omega
    have nextSlot : next.getReg .x10 = BitVec.ofNat 64 (slot + 256) := by
      rw [regs.1, slotPtr]
      exact ofNat64_add_eq slot 256 (slot + 256) rfl
    have nextSalt : ∀ word < 64,
        accessValid (next.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      rw [regs.2.2 .x18 (by decide) (by decide) (by decide)]; exact saltValid
    have hslotNext : slot + 256 + 24 + 256 * count ≤ MEMORY_BYTES :=
      Nat.le_trans (by clear * -; omega) slotBound
    rw [ih next (start + 1) (by clear * - bounded; omega) nextPC
      ((regs.2.2 .x5 (by decide) (by decide) (by decide)).trans r5)
      ((regs.2.2 .x11 (by decide) (by decide) (by decide)).trans r11)
      ((regs.2.2 .x13 (by decide) (by decide) (by decide)).trans r13)
      (slot + 256) nextSlot (by clear * - slotAligned; omega) hslotNext nextSalt
      ((regs.2.2 .x23 (by decide) (by decide) (by decide)).trans heapPtr)]
    simp only [bind_assoc, pure_bind, charge_charge,
      show 45 + 45 * count = 45 * (count + 1) by clear * -; omega,
      show 4 + 4 * count = 4 * (count + 1) by clear * -; omega]

/-- One complete 32-leaf block iteration: 547 instructions, 1,443 cycles, 128 queries. -/
theorem commit_block (state : MachineState) (pc : state.pc = 4232)
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (slot : Nat) (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (slotAligned : slot % 8 = 0) (slotBound : slot + 24 + 8192 ≤ MEMORY_BYTES)
    (saltValid : ∀ word < 64,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (heap : Nat) (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (heapAligned : heap % 8 = 0) (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (fuel : Nat) :
    execute (submission.image .commit) (547 + fuel) state true =
      (do let finished ← commitBlockRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 1443 128) := by
  have hpc : state.pc = BitVec.ofNat 64 (4096 + 4 * (34 + 17 * 0)) := by rw [pc]; rfl
  have hlanes := commit_leaf_lanes state 0 32 (by decide) hpc r5 r11 r13 slot slotPtr slotAligned
    (Nat.le_trans (by clear * -; omega) slotBound) saltValid heap heapPtr heapAligned heapBound (3 + fuel)
  rw [show 547 + fuel = 17 * 32 + (3 + fuel) by clear * -; omega, hlanes]
  simp only [commitBlockRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed hhashed
  have hregs := leaf_block_lanes_registers state hashed 0 32 hhashed
  have latchPC : hashed.pc = 6408 := by rw [hregs.2.1, pc]; rfl
  rw [commit_block_latch hashed latchPC]
  simp [charge_charge]

end

/-! ### Final root copy (8 instructions at indices 785..792) -/

private def commitRootCopyInstructions : List Instr :=
  [.LD .x6 .x9 32, .SD .x26 .x6 0,
   .LD .x6 .x9 40, .SD .x26 .x6 8,
   .LD .x6 .x9 48, .SD .x26 .x6 16,
   .LD .x6 .x9 56, .SD .x26 .x6 24]

private def commitRootCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitRootCopyInstructions.take count).foldl execInstrBr state

def commitRootCopyState (state : MachineState) : MachineState := commitRootCopyPrefix state 8

theorem commit_root_copy_expansion (state : MachineState) :
    commitRootCopyState state =
      ([.LD .x6 .x9 32, .SD .x26 .x6 0, .LD .x6 .x9 40, .SD .x26 .x6 8,
        .LD .x6 .x9 48, .SD .x26 .x6 16, .LD .x6 .x9 56, .SD .x26 .x6 24] :
        List Instr).foldl execInstrBr state := rfl

private theorem root_copy_prefix_reg (state : MachineState) (count : Nat) (hc : count ≤ 8)
    (reg : Reg) (n6 : reg ≠ .x6) :
    (commitRootCopyPrefix state count).getReg reg = state.getReg reg := by
  have memReg (s : MachineState) (a v : Word) (r : Reg) :
      (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl
  interval_cases count <;>
    simp only [commitRootCopyPrefix, commitRootCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memReg, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n6)]

theorem commit_root_copy_pc (state : MachineState) :
    (commitRootCopyState state).pc = state.pc + 32 := by
  simp [commitRootCopyState, commitRootCopyPrefix, commitRootCopyInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 1600000 in
theorem commit_root_copy (state : MachineState) (pc : state.pc = 7236)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitRootCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := commitRootCopyPrefix state)
  intro i hi
  refine ⟨.base ((commitRootCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (785 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitRootCopyPrefix, commitRootCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · have hf := commit_filtered_epilogue i (by omega)
      interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
  · have r9 := root_copy_prefix_reg state i (by omega) .x9 (by decide)
    have r26 := root_copy_prefix_reg state i (by omega) .x26 (by decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitRootCopyPrefix state i)
        ((commitRootCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp (config := { decide := true }) only [commitRootCopyInstructions,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          memoryArgumentsValid, memAccess, signExtend12, r9, r26] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitRootCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
