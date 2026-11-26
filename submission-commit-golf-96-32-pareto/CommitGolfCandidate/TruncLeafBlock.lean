import CommitGolfCandidate.Commit

import CommitGolfCandidate.TruncLeafLane

namespace CommitGolfCandidate.Trunc

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

set_option maxHeartbeats 1200000

def commitLoad (reg : Reg) (high : BitVec 12) : List Instr :=
  [.ADDI reg .x0 0, .SLLI reg reg 11, .ADDI reg reg high,
   .SLLI reg reg 11, .ADDI reg reg 0, .SLLI reg reg 11, .ADDI reg reg 0]

def commitSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 4072, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0] ++
  commitLoad .x6 384 ++ [.ADD .x18 .x9 .x6] ++
  commitLoad .x6 192 ++ [.ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0] ++
  commitLoad .x11 64 ++ [.ADD .x20 .x18 .x11]

def commitSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitSetupInstructions.take count).foldl execInstrBr state

theorem commit_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (29 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSetupState state) allowCoins
          return result.charge 29 0) := by
  apply execute_unit_steps (states := commitSetupPrefix state)
  intro i hi
  refine ⟨.base ((commitSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply prefixFetch _ i _ (by omega)
    · interval_cases i <;>
        simp [commitSetupPrefix, commitSetupInstructions, commitLoad, execInstrBr, pc,
          MachineState.setPC]
    · have hf := commit_filtered_preRandom i (by omega)
      interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

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
    apply prefixFetch _ 29 _ (by decide) pc
    rw [commit_code_word_at _ _ (commit_filtered_preRandom 29 (by decide))]; rfl
  rw [Nat.add_comm 1 fuel, execute, fetched]
  simp only [selector, valid]
  rfl

def commitReadyInstructions : List Instr :=
  [.ADDI .x10 .x8 0, .ADDI .x5 .x0 0, .ADDI .x11 .x0 96, .ADDI .x13 .x0 0]

def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

theorem commit_ready (state : MachineState) (pc : state.pc = 4216) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitReadyState state) true
          return result.charge 4 0) := by
  apply execute_unit_steps (states := commitReadyPrefix state)
  intro i hi
  refine ⟨.base ((commitReadyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply prefixFetch _ (30 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]
    · have hf := commit_filtered_preRandom (30 + i) (by omega)
      interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def commitLatchInstructions : List Instr :=
  [.ADDI .x18 .x18 512, .ADDI .x23 .x23 1536]

def commitLatchPrefix (state : MachineState) (count : Nat) : MachineState :=
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
    · apply prefixFetch _ (578 + i) _ (by omega)
      · interval_cases i <;> simp [commitLatchPrefix, commitLatchInstructions, execInstrBr, pc, MachineState.setPC]
      · have hf := commit_filtered_leafLatch i (by omega)
        interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (commitLatchPrefix state 2) =
      some (.base (.BNE .x18 .x20 6008)) := by
    apply prefixFetch _ 580 _ (by decide)
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


end CommitGolfCandidate.Trunc
