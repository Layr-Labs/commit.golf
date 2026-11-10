import CommitGolfCandidate.Check
import CommitGolfCandidate.HoistHelpers

/-! Execution of the commitment image's leaf subroutine. The actual instruction
addresses and return address differ from the checker; the scratch transform is the
same. Every oracle reply is covered by the execution and resource proofs. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096

theorem commit_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 200) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .commit).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .commit).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

private def commitCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

private def commitCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitCompressionInstructions.take count).foldl execInstrBr state

/-- The fixed syscall arguments remain live through every block. -/
def CommitLeafOracleReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x10 = 256 ∧ state.getReg .x11 = 64 ∧
    state.getReg .x12 = 256 ∧ state.getReg .x13 = 0

/-- Initial counter and hoisted syscall arguments for the eight-block leaf. -/
def commitLeafReadyState (state : MachineState) : MachineState :=
  commitCompressionPrefix ((state.setReg .x28 8).setPC 4436) 5

@[simp] theorem commit_leaf_ready_register (state : MachineState) (reg : Reg)
    (preserved : reg ∉ [.x5,.x10,.x11,.x12,.x13,.x28]) :
    (commitLeafReadyState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitLeafReadyState, commitCompressionPrefix,
    commitCompressionInstructions, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]

@[simp] theorem commit_leaf_ready_pc (state : MachineState) :
    (commitLeafReadyState state).pc = 4456 := by
  simp [commitLeafReadyState, commitCompressionPrefix, commitCompressionInstructions,
    execInstrBr, MachineState.setPC]

@[simp] theorem commit_leaf_ready_counter (state : MachineState) :
    (commitLeafReadyState state).getReg .x28 = 8 := rfl

@[simp] theorem commit_leaf_ready_oracle (state : MachineState)
    (scratch : state.getReg .x21 = 256) :
    CommitLeafOracleReady (commitLeafReadyState state) := by
  have r21 : state.regs .x21 = 256 := scratch
  simp [commitLeafReadyState, CommitLeafOracleReady, commitCompressionPrefix,
    commitCompressionInstructions, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC, r21]

private theorem commit_compression_prefix_ready (state : MachineState)
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state) :
    commitCompressionPrefix state 5 = state.setPC (state.pc + 20) := by
  cases state with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    dsimp [CommitLeafOracleReady, MachineState.getReg] at ready scratch
    dsimp [commitCompressionPrefix, commitCompressionInstructions, List.take,
      List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    simp only [Bool.false_eq_true, reduceIte, BitVec.zero_add, BitVec.add_zero]
    congr 1
    · funext reg
      cases reg <;> simp_all
    · simp [BitVec.add_assoc]

/-- Five one-time instructions set every fixed oracle argument before the block loop. -/
theorem commit_leaf_ready (state : MachineState) (pc : state.pc = 4436)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitCompressionPrefix state 5) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := commitCompressionPrefix state)
  intro i hi
  refine ⟨.base ((commitCompressionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (85+i) _ (by omega)
    · interval_cases i <;> simp [commitCompressionPrefix, commitCompressionInstructions,
        execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- State after the compression reply overwrites the low half of scratch memory. -/
def commitCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits (commitCompressionPrefix state 5) 256 answer

/-- With hoisted arguments the block executes only the eight-cycle syscall. -/
theorem commit_compression (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4488 + 44*block))
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state 256 64)))
          let result ← execute (submission.image .commit) fuel
            ((commitCompressionState state answer).setPC (state.pc + 4)) allowCoins
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ (98+11*block) _ (by omega)
    · rw [pc]; congr 1 <;> omega
    · interval_cases block <;> rfl
  rcases ready with ⟨r5,r10,r11,r12,r13⟩
  have input : oracleInput state = some (.inl (readBuffer state 256 64)) := by
    have kind : (state.getReg .x13).toNat = 0 := by rw [r13]; rfl
    unfold oracleInput
    simp only [kind]
    simp [r10,r11,r12, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH,
      rangeValid, MEMORY_BYTES]
    exact hoist_read_width state 256 _ kind
  have normalized (answer : BitVec 256) :
      (commitCompressionState state answer).setPC (state.pc + 4) = writeBits state 256 answer := by
    rw [commitCompressionState, commit_compression_prefix_ready state scratch
      ⟨r5,r10,r11,r12,r13⟩, hoist_write_bits_pc]
    rw [hoist_pc_pc]
    have outputpc : (writeBits state 256 answer).pc = state.pc + 4 := rfl
    rw [← outputpc, hoist_pc_self]
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos r5, input]
  simp only [writeOracleAnswer, r12]
  simp only [oracleCycles, COMPRESSION_CYCLES]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state 256 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [normalized answer]
  rfl

/-- Five setup instructions and the reply write advance to the next instruction. -/
theorem commit_compression_pc (state : MachineState) (answer : BitVec 256) :
    (commitCompressionState state answer).pc = state.pc + 24 := by
  simp [commitCompressionState, writeBits, commitCompressionPrefix, commitCompressionInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

/-- Compression preserves the loop counters, pointers, and return address. Only
syscall argument registers are overwritten by its five-instruction setup. -/
theorem commit_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not10 : reg ≠ .x10) (not11 : reg ≠ .x11)
    (not12 : reg ≠ .x12) (not13 : reg ≠ .x13) :
    (commitCompressionState state answer).getReg reg = state.getReg reg := by
  rw [commitCompressionState, writeBits_register]
  simp only [commitCompressionPrefix, commitCompressionInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13)]

private def commitLeafCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
   .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56]

private def commitLeafCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitLeafCopyInstructions.take count).foldl execInstrBr state

def commitLeafCopyState (state : MachineState) : MachineState := commitLeafCopyPrefix state 8

private theorem commit_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (commitLeafCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [commitLeafCopyPrefix, commitLeafCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

set_option maxHeartbeats 8000000 in
/-- Copy the next 256-bit message block into the upper scratch half. -/
theorem commit_leaf_copy (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4456+44*block))
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := commitLeafCopyPrefix state)
  intro i hi
  refine ⟨.base ((commitLeafCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (90 + 11*block + i) _ (by omega)
    · interval_cases block <;> interval_cases i <;>
        simp [commitLeafCopyPrefix, commitLeafCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases block <;> interval_cases i <;> rfl
  · have sourceReg := commit_copy_register state i (by omega) .x8 (by decide)
    have scratchReg := (commit_copy_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitLeafCopyPrefix state i)
        ((commitLeafCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [commitLeafCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 | rfl
    interval_cases i <;>
      simp only [commitLeafCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- Reference latch: advance the pointer and counter, and normalize the PC.
The unrolled execution lemmas explicitly replace this reference PC with its actual address. -/
def commitLeafNextState (state : MachineState) : MachineState :=
  ((state.setReg .x8 (state.getReg .x8 + 32)).setReg .x28 (state.getReg .x28 - 1)).setPC
    (if state.getReg .x28 - 1 = 0 then 4504 else 4456)

theorem commit_leaf_next_pc_irrel (state : MachineState) (pc : Word) :
    commitLeafNextState (state.setPC pc) = commitLeafNextState state := by
  cases state; rfl

/-- The unrolled image advances to the next block with two ordinary instructions. -/
theorem commit_leaf_next (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4492+44*block))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel
            ((commitLeafNextState state).setPC (state.pc + 8)) allowCoins
          return result.charge 2 0) := by
  let advanced := (state.setReg .x8 (state.getReg .x8 + 32)).setPC (state.pc + 4)
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x8 .x8 32)) := by
    apply commit_fetch _ (99+11*block) _ (by omega)
    · rw [pc]; congr 1 <;> omega
    · interval_cases block <;> rfl
  have f1 : fetch (submission.image .commit) advanced = some (.base (.ADDI .x28 .x28 4095)) := by
    apply commit_fetch _ (100+11*block) _ (by omega)
    · interval_cases block <;> simp [advanced,pc,MachineState.setPC]
    · interval_cases block <;> rfl
  have s0 : ordinaryStep state (.base (.ADDI .x8 .x8 32)) = some advanced := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,advanced]
  have s1 : ordinaryStep advanced (.base (.ADDI .x28 .x28 4095)) =
      some ((commitLeafNextState state).setPC (state.pc + 8)) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,
      advanced,commitLeafNextState,MachineState.getReg,MachineState.setReg,MachineState.setPC,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0,execute_ordinary_step _ _ _ _ _ _ f1 s1]
  simp [instructionCycles,Execution.charge,← Nat.add_assoc]

/-- One leaf block: copy 32 bytes, compress, then advance the pointer and counter. -/
def commitLeafStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  commitLeafNextState (commitCompressionState (commitLeafCopyState state) answer)

theorem commit_leaf_block (state : MachineState) (block : Nat) (blockBound : block < 8)
    (pc : state.pc = BitVec.ofNat 64 (4456+44*block))
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (11 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
          let result ← execute (submission.image .commit) fuel ((commitLeafStepState state answer).setPC
            (BitVec.ofNat 64 (4456+44*(block+1)))) allowCoins
          return result.charge 18 1) := by
  have copyPC : (commitLeafCopyState state).pc = BitVec.ofNat 64 (4488+44*block) := by
    interval_cases block <;> simp [commitLeafCopyState, commitLeafCopyPrefix, commitLeafCopyInstructions, execInstrBr,
      MachineState.setPC, pc]
  have copyScratch : (commitLeafCopyState state).getReg .x21 = 256 :=
    (commit_copy_register state 8 (by decide) .x21 (by decide)).trans scratch
  have copyReady : CommitLeafOracleReady (commitLeafCopyState state) := by
    rcases ready with ⟨r5,r10,r11,r12,r13⟩
    unfold CommitLeafOracleReady
    simpa only [commitLeafCopyState,
      commit_copy_register state 8 (by decide) .x5 (by decide),
      commit_copy_register state 8 (by decide) .x10 (by decide),
      commit_copy_register state 8 (by decide) .x11 (by decide),
      commit_copy_register state 8 (by decide) .x12 (by decide),
      commit_copy_register state 8 (by decide) .x13 (by decide)] using
      And.intro r5 ⟨r10,r11,r12,r13⟩
  rw [show 11 + fuel = 8 + (1 + (2 + fuel)) by omega,
    commit_leaf_copy state block blockBound pc scratch sourceValid,
    commit_compression _ block blockBound copyPC copyScratch copyReady]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  have queryPC : ((commitCompressionState (commitLeafCopyState state) answer).setPC
      ((commitLeafCopyState state).pc + 4)).pc = BitVec.ofNat 64 (4492+44*block) := by
    change (commitLeafCopyState state).pc + 4 = _
    rw [copyPC]; interval_cases block <;> rfl
  rw [commit_leaf_next _ block blockBound queryPC]
  have targetPC : (commitLeafCopyState state).pc + 4 + 8 =
      BitVec.ofNat 64 (4456+44*(block+1)) := by
    rw [copyPC]; interval_cases block <;> rfl
  have nextEq :
      (commitLeafNextState ((commitCompressionState (commitLeafCopyState state) answer).setPC
        ((commitLeafCopyState state).pc + 4))).setPC
          (((commitCompressionState (commitLeafCopyState state) answer).setPC
            ((commitLeafCopyState state).pc + 4)).pc + 8) =
      (commitLeafStepState state answer).setPC (BitVec.ofNat 64 (4456+44*(block+1))) := by
    rw [commit_leaf_next_pc_irrel]
    change (commitLeafStepState state answer).setPC ((commitLeafCopyState state).pc + 4 + 8) = _
    rw [targetPC]
  rw [nextEq]
  simp [Execution.charge, bind_assoc, pure_bind, ← Nat.add_assoc]

/-- The normalized reference transition records the fixed arguments for the next block. -/
theorem commit_leaf_step_ready (state : MachineState) (answer : BitVec 256)
    (scratch : state.getReg .x21 = 256) :
    CommitLeafOracleReady (commitLeafStepState state answer) := by
  have copyScratch : (commitLeafCopyState state).regs .x21 = 256 :=
    (commit_copy_register state 8 (by decide) .x21 (by decide)).trans scratch
  have regs : CommitLeafOracleReady (commitCompressionPrefix (commitLeafCopyState state) 5) := by
    simp [CommitLeafOracleReady, commitCompressionPrefix, commitCompressionInstructions,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg,
      MachineState.setPC, copyScratch]
  change CommitLeafOracleReady (commitCompressionState (commitLeafCopyState state) answer)
  unfold CommitLeafOracleReady at regs ⊢
  simpa only [commitCompressionState, writeBits_register] using regs

/-- The next iteration has the advanced source pointer and decremented counter;
its scratch pointer and subroutine return address are unchanged. -/
theorem commit_leaf_block_registers (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).getReg .x8 = state.getReg .x8 + 32 ∧
    (commitLeafStepState state answer).getReg .x28 = state.getReg .x28 - 1 ∧
    (commitLeafStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (commitLeafStepState state answer).getReg .x1 = state.getReg .x1 := by
  have preserved (reg : Reg) (not6 : reg ≠ .x6) (not5 : reg ≠ .x5) (not10 : reg ≠ .x10)
      (not11 : reg ≠ .x11) (not12 : reg ≠ .x12) (not13 : reg ≠ .x13) :
      (commitCompressionState (commitLeafCopyState state) answer).getReg reg = state.getReg reg :=
    (commit_compression_register _ answer reg not5 not10 not11 not12 not13).trans
      (commit_copy_register state 8 (by decide) reg not6)
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x8),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x1),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x1)]
  rw [preserved .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem commit_leaf_block_pc (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).pc =
      if state.getReg .x28 - 1 = 0 then 4504 else 4456 := by
  change (if (commitCompressionState (commitLeafCopyState state) answer).getReg .x28 - 1 = 0
    then 4504 else 4456) = _
  rw [commit_compression_register _ answer .x28 (by decide) (by decide) (by decide) (by decide) (by decide),
    commitLeafCopyState, commit_copy_register state 8 (by decide) .x28 (by decide)]

/-- Reference unfolding of the eight actual block computations. Each iteration issues
the image's exact scratch query and applies its byte writes and register transitions;
internal PCs are normalized and restored to actual addresses by the execution theorem. -/
def commitLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
      commitLeafLoop (commitLeafStepState state answer) count

theorem unroll_copy_pc (state : MachineState) (target : Word) :
    commitLeafCopyState (state.setPC target) =
      (commitLeafCopyState state).setPC (target + 32) := by
  change commitLeafCopyInstructions.foldl execInstrBr (state.setPC target) =
    (commitLeafCopyInstructions.foldl execInstrBr state).setPC (target + 32)
  cases state
  dsimp [commitLeafCopyInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.getMem,MachineState.setMem,MachineState.setPC]
  congr 1
  simp [BitVec.add_assoc]

theorem unroll_compression_pc (state : MachineState) (target : Word) (answer : BitVec 256) :
    commitCompressionState (state.setPC target) answer =
      (commitCompressionState state answer).setPC (target + 24) := by
  have argsShift : commitCompressionInstructions.foldl execInstrBr (state.setPC target) =
      (commitCompressionInstructions.foldl execInstrBr state).setPC (target + 20) := by
    cases state
    dsimp [commitCompressionInstructions,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
      MachineState.setReg,MachineState.setPC]
    congr 1
    simp [BitVec.add_assoc]
  change writeBits (commitCompressionInstructions.foldl execInstrBr (state.setPC target)) 256 answer =
    (writeBits (commitCompressionInstructions.foldl execInstrBr state) 256 answer).setPC (target + 24)
  rw [argsShift,hoist_write_bits_pc]
  simp [BitVec.add_assoc]

theorem unroll_read_pc (state : MachineState) (target : Word) (address bytes : Nat) :
    readBuffer (state.setPC target) address bytes = readBuffer state address bytes := rfl

theorem unroll_step_pc (state : MachineState) (target : Word) (answer : BitVec 256) :
    commitLeafStepState (state.setPC target) answer = commitLeafStepState state answer := by
  unfold commitLeafStepState
  rw [unroll_copy_pc,unroll_compression_pc,commit_leaf_next_pc_irrel]

theorem unroll_loop_pc_positive (state : MachineState) (target : Word) (count : Nat) :
    commitLeafLoop (state.setPC target) (count + 1) = commitLeafLoop state (count + 1) := by
  have inputEq : readBuffer (commitLeafCopyState (state.setPC target)) 256 64 =
      readBuffer (commitLeafCopyState state) 256 64 := by
    rw [unroll_copy_pc,unroll_read_pc]
  have tailEq : (fun answer : BitVec 256 =>
      commitLeafLoop (commitLeafStepState (state.setPC target) answer) count) =
      (fun answer : BitVec 256 => commitLeafLoop (commitLeafStepState state answer) count) := by
    funext answer
    exact congrArg (fun next => commitLeafLoop next count) (unroll_step_pc state target answer)
  exact congrArg₂ (fun (input : BitVec COMPRESSION_INPUT_LENGTH)
      (tail : BitVec 256 → OracleComp World MachineState) =>
        (liftM (World.query (.inr (.inl input))) : OracleComp World (BitVec 256)) >>= tail)
    inputEq tailEq

theorem unroll_loop_pc_bind {α : Type} (state : MachineState) (target finalPC : Word)
    (count : Nat) (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitLeafLoop (state.setPC target) count
        continuation (finished.setPC finalPC)) =
      (do let finished ← commitLeafLoop state count
          continuation (finished.setPC finalPC)) := by
  cases count with
  | zero => simp [commitLeafLoop,hoist_pc_pc]
  | succ count => rw [unroll_loop_pc_positive]

set_option maxHeartbeats 2000000 in
/-- The eight blocks occupy consecutive addresses and omit their branch instructions. -/
theorem commit_leaf_loop (state : MachineState) (count first : Nat) (total : first + count = 8)
    (pc : state.pc = BitVec.ofNat 64 (4456+44*first)) (counter : state.getReg .x28 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256) (ready : CommitLeafOracleReady state)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (11 * count + fuel) state allowCoins =
      (do let finished ← commitLeafLoop state count
          let result ← execute (submission.image .commit) fuel (finished.setPC 4808) allowCoins
          return result.charge (18 * count) count) := by
  induction count generalizing state first with
  | zero =>
    have firstEq : first = 8 := by omega
    have statePC : state.pc = 4808 := by simpa [firstEq] using pc
    have normalized : state.setPC 4808 = state := by rw [← statePC,hoist_pc_self]
    simp only [Nat.mul_zero, Nat.zero_add, commitLeafLoop, pure_bind]
    rw [normalized]
    simp [Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (commitLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(commit_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 4 * count) :
        accessValid ((commitLeafStepState state answer).getReg .x8 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 4) (by omega)
      rw [(commit_leaf_block_registers state answer).1]
      have address : state.getReg .x8 + 32 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 4)) := by
        rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [show 11 * (count + 1) + fuel = 11 + (11 * count + fuel) by omega,
      commit_leaf_block state first (by omega) pc scratch ready currentValid]
    simp only [commitLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    let next := commitLeafStepState state answer
    have nextScratch : next.getReg .x21 = 256 :=
      (commit_leaf_block_registers state answer).2.2.1.trans scratch
    have nextReady : CommitLeafOracleReady next := commit_leaf_step_ready state answer scratch
    let actualNext := next.setPC (BitVec.ofNat 64 (4456+44*(first+1)))
    have actualCounter : actualNext.getReg .x28 = BitVec.ofNat 64 count := by
      simpa only [actualNext,MachineState.getReg_setPC] using nextCounter answer
    have actualScratch : actualNext.getReg .x21 = 256 := by
      simpa only [actualNext,MachineState.getReg_setPC] using nextScratch
    have actualReady : CommitLeafOracleReady actualNext := by
      simpa only [actualNext,CommitLeafOracleReady,MachineState.getReg_setPC] using nextReady
    have actualValid : ∀ word < 4*count,
        accessValid (actualNext.getReg .x8 + BitVec.ofNat 64 (8*word)) 8 = true := by
      simpa only [actualNext,MachineState.getReg_setPC] using nextValid answer
    rw [ih actualNext (first+1) (by omega) rfl actualCounter actualScratch actualReady actualValid]
    dsimp only [actualNext]
    have tailEq := unroll_loop_pc_bind next
      (BitVec.ofNat 64 (4456+44*(first+1))) 4808 count
      (fun finished => do
        let result ← execute (submission.image .commit) fuel finished allowCoins
        return result.charge (18*count) count)
    rw [tailEq]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, next]

/-- Every possible run of the bounded loop exhausts its counter and preserves the
return address. A nonempty reference loop records its normalized return address. -/
theorem commit_leaf_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x28 = 0 ∧ finished.getReg .x1 = state.getReg .x1 ∧
      (0 < count → finished.pc = 4504) := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, rfl, by omega⟩
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have nextCounter : (commitLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(commit_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have remaining := ih _ (by omega) nextCounter reached
    refine ⟨remaining.1, remaining.2.1.trans (commit_leaf_block_registers state answer).2.2.2, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [commit_leaf_block_pc state answer, counter]
      rfl
    · exact remaining.2.2 (by omega)

/-- The leaf subroutine returns to its caller using the preserved link register. -/
theorem commit_leaf_return (state : MachineState) (pc : state.pc = 4808)
    (link : state.getReg .x1 = 4292) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4292) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply commit_fetch _ 178 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 4292) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Hoisted arguments cost five cycles once; eight eleven-instruction blocks follow. -/
theorem commit_leaf_subroutine (state : MachineState) (pc : state.pc = 4432)
    (link : state.getReg .x1 = 4292) (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (95 + fuel) state allowCoins =
      (do let finished ← commitLeafLoop (commitLeafReadyState state) 8
          let result ← execute (submission.image .commit) fuel (finished.setPC 4292) allowCoins
          return result.charge 151 8) := by
  let initialized := (state.setReg .x28 8).setPC 4436
  let ready := commitLeafReadyState state
  have fetched : fetch (submission.image .commit) state =
      some (.base (.ADDI .x28 .x0 8)) := by
    apply commit_fetch _ 84 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.ADDI .x28 .x0 8)) = some initialized := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      initialized, pc, MachineState.getReg]
  have initCounter : ready.getReg .x28 = BitVec.ofNat 64 8 := by simp [ready]
  have initScratch : ready.getReg .x21 = 256 := by simpa [ready] using scratch
  have initSource : ∀ word < 4 * 8,
      accessValid (ready.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa [ready] using sourceValid
  have oracleReady : CommitLeafOracleReady ready := commit_leaf_ready_oracle state scratch
  rw [show 95 + fuel = (5 + (11 * 8 + (1 + fuel))) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped,
    commit_leaf_ready initialized rfl]
  rw [show commitCompressionPrefix initialized 5 = ready by rfl,
    commit_leaf_loop ready 8 0 (by decide) rfl initCounter initScratch oracleReady initSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := commit_leaf_loop_finished ready 8 (by decide) initCounter finished reachable
  have finalLink : finished.getReg .x1 = 4292 := by
    rw [done.2.1]
    simpa [ready] using link
  rw [commit_leaf_return (finished.setPC 4808) rfl finalLink]
  rw [hoist_pc_pc]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

private theorem commit_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28]) :
    (commitLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28⟩
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (commit_compression_register _ answer reg not5 not10 not11 not12 not13).trans
    (commit_copy_register state 8 (by decide) reg not6)

/-- The complete hash preserves the position/path metadata, proof pointer, root
pointer, and scratch pointer. It consumes exactly 32 bytes per block from x8. -/
theorem commit_leaf_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) ∧
    ∀ reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have rest := ih _ reached
    constructor
    · rw [rest.1, (commit_leaf_block_registers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · intro reg preserved
      exact (rest.2 reg preserved).trans (commit_leaf_block_preserves state answer reg preserved)

end CommitGolfCandidate
