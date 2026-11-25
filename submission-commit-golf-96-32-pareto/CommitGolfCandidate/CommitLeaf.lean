import CommitGolfCandidate.Check

/-! Execution of the commitment image's in-place leaf chain. The four calls of one leaf
compress the contiguous 96 bytes `[chaining value | 64-byte block]` starting at
`x8 + 64*j` and write the 32-byte reply either over the last consumed 32 bytes
(`x8 + 64*j + 64`, calls 0..2) or into the heap slot `x23` (call 3). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

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

/-- The two pointer instructions before in-place call `j`. -/
def chainCallInstructions (j : Nat) : List Instr :=
  [.ADDI .x10 .x8 (BitVec.ofNat 12 (64*j)),
   if j = 3 then .ADDI .x12 .x23 0 else .ADDI .x12 .x8 (BitVec.ofNat 12 (64*j+64))]

private def chainCallPrefix (state : MachineState) (j count : Nat) : MachineState :=
  ((chainCallInstructions j).take count).foldl execInstrBr state

def chainSetupState (state : MachineState) (j : Nat) : MachineState := chainCallPrefix state j 2

/-- Output address of call `j`. -/
def chainOutput (state : MachineState) (j : Nat) : Word :=
  if j = 3 then state.getReg .x23 else state.getReg .x8 + BitVec.ofNat 64 (64*j+64)

/-- State after call `j`: the reply is written at the call's output address. -/
def chainCallState (state : MachineState) (j : Nat) (answer : BitVec 256) : MachineState :=
  writeBits (chainSetupState state j) (chainOutput state j) answer

theorem chain_setup_memory (state : MachineState) (j : Nat) :
    (chainSetupState state j).mem = state.mem := by
  unfold chainSetupState chainCallPrefix chainCallInstructions
  split <;> rfl

theorem chain_setup_register (state : MachineState) (j : Nat) (reg : Reg)
    (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainSetupState state j).getReg reg = state.getReg reg := by
  unfold chainSetupState chainCallPrefix chainCallInstructions
  split <;>
    simp only [List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12)]

theorem chain_setup_registers (state : MachineState) (j : Nat) (hj : j < 4) :
    (chainSetupState state j).getReg .x10 = state.getReg .x8 + BitVec.ofNat 64 (64*j) ∧
    (chainSetupState state j).getReg .x12 = chainOutput state j ∧
    (chainSetupState state j).pc = state.pc + 8 ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → (chainSetupState state j).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, fun reg n10 n12 => chain_setup_register state j reg n10 n12⟩ <;>
    interval_cases j <;>
    simp [chainSetupState, chainCallPrefix, chainCallInstructions, chainOutput, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.setPC, BitVec.add_assoc] <;>
    rfl

theorem chain_call_memory (state : MachineState) (j : Nat) (answer : BitVec 256) :
    (chainCallState state j answer).mem =
      (writeBits state (chainOutput state j) answer).mem :=
  write_bits_memory_congr _ _ _ answer (chain_setup_memory state j)

theorem chain_call_register (state : MachineState) (j : Nat) (hj : j < 4) (answer : BitVec 256)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainCallState state j answer).getReg reg = state.getReg reg := by
  rw [chainCallState, writeBits_register]
  exact (chain_setup_registers state j hj).2.2.2 reg n10 n12

theorem chain_call_pc (state : MachineState) (j : Nat) (hj : j < 4) (answer : BitVec 256) :
    (chainCallState state j answer).pc = state.pc + 12 := by
  simp only [chainCallState, writeBits, MachineState.setPC]
  rw [(chain_setup_registers state j hj).2.2.1, BitVec.add_assoc]
  rfl

set_option maxHeartbeats 1600000 in
/-- In-place call `j` (instructions 51+3j .. 53+3j): two pointer instructions and one
direct 96-byte compression query. Costs ten cycles and one public query. -/
theorem commit_chain_call (state : MachineState) (j : Nat) (hj : j < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (51 + 3*j)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x8 + BitVec.ofNat 64 (64*j)) 96 = true)
    (sourceAligned : (state.getReg .x8 + BitVec.ofNat 64 (64*j)).toNat % 8 = 0)
    (destinationValid : rangeValid (chainOutput state j) 32 = true)
    (destinationAligned : (chainOutput state j).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (.inl
            (readBuffer state (state.getReg .x8 + BitVec.ofNat 64 (64*j)).toNat 96)))
          let result ← execute (submission.image .commit) fuel (chainCallState state j answer) true
          return result.charge 10 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (chainCallPrefix state j 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := chainCallPrefix state j)
    intro i hi
    refine ⟨.base (((chainCallInstructions j)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (51 + 3*j + i) _ (by omega)
      · interval_cases j <;> interval_cases i <;>
          simp [chainCallPrefix, chainCallInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases j <;> interval_cases i <;> rfl
    · interval_cases j <;> interval_cases i <;> rfl
    · interval_cases j <;> interval_cases i <;> rfl
  let ready := chainCallPrefix state j 2
  have regs := chain_setup_registers state j hj
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (53 + 3*j)) := by
    change (chainSetupState state j).pc = _
    rw [regs.2.2.1, pc]
    interval_cases j <;> rfl
  have fetched : fetch (submission.image .commit) ready = some (.base .ECALL) := by
    apply commit_fetch _ (53 + 3*j) _ (by omega) readyPC
    interval_cases j <;> rfl
  have r5' : ready.getReg .x5 = 0 := (regs.2.2.2 .x5 (by decide) (by decide)).trans r5
  have r11' : ready.getReg .x11 = 96 := (regs.2.2.2 .x11 (by decide) (by decide)).trans r11
  have r13' : ready.getReg .x13 = 0 := (regs.2.2.2 .x13 (by decide) (by decide)).trans r13
  have r10' : ready.getReg .x10 = state.getReg .x8 + BitVec.ofNat 64 (64*j) := regs.1
  have r12' : ready.getReg .x12 = chainOutput state j := regs.2.1
  have sv : rangeValid (ready.getReg .x10) 96 = true := by rw [r10']; exact sourceValid
  have sa : (ready.getReg .x10).toNat % 8 = 0 := by rw [r10']; exact sourceAligned
  have dv : rangeValid (ready.getReg .x12) 32 = true := by rw [r12']; exact destinationValid
  have da : (ready.getReg .x12).toNat % 8 = 0 := by rw [r12']; exact destinationAligned
  have memory : readBuffer ready (ready.getReg .x10).toNat 96 =
      readBuffer state (ready.getReg .x10).toNat 96 := by
    have sameMem : ready.mem = state.mem := chain_setup_memory state j
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have input' : oracleInput ready = some (.inl (readBuffer state (ready.getReg .x10).toNat 96)) := by
    simp [oracleInput, r11', r13', sv, sa, dv, da, COMPRESSION_INPUT_LENGTH,
      COMPRESSION_OUTPUT_LENGTH, memory]
    try rw [r13']
    try simp [memory]
    try rfl
  have input : oracleInput ready = some (.inl
      (readBuffer state (state.getReg .x8 + BitVec.ofNat 64 (64*j)).toNat 96)) := by
    rw [input', r10']
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup, execute, fetched, if_pos r5', input]
  simp only [writeOracleAnswer, r12', bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl
      (readBuffer state (state.getReg .x8 + BitVec.ofNat 64 (64*j)).toNat 96)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, chainCallState, chainSetupState, ← Nat.add_assoc]
  congr

/-- Small offsets from an in-range pointer do not wrap. -/
theorem pointer_offset_nat (base offset : Nat) (bound : base + offset ≤ MEMORY_BYTES) :
    (BitVec.ofNat 64 base + BitVec.ofNat 64 offset).toNat = base + offset := by
  have b : base < 2^64 := by dsimp [MEMORY_BYTES] at bound; omega
  have o : offset < 2^64 := by dsimp [MEMORY_BYTES] at bound; omega
  have t : base + offset < 2^64 := by dsimp [MEMORY_BYTES] at bound; omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt b,
    Nat.mod_eq_of_lt o, Nat.mod_eq_of_lt t]

/-- Address and alignment side conditions of in-place call `j` for a salt slot at
`slot` (input `[slot+64j, slot+64j+96)`) and a heap output slot at `heap`. -/
theorem chain_call_valid (s : MachineState) (j : Nat) (hj : j < 4) (slot heap : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 slot) (slotAligned : slot % 8 = 0)
    (slotBound : slot + 288 ≤ MEMORY_BYTES)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap) (heapAligned : heap % 8 = 0)
    (heapBound : heap + 32 ≤ MEMORY_BYTES) :
    rangeValid (s.getReg .x8 + BitVec.ofNat 64 (64*j)) 96 = true ∧
    (s.getReg .x8 + BitVec.ofNat 64 (64*j)).toNat % 8 = 0 ∧
    rangeValid (chainOutput s j) 32 = true ∧ (chainOutput s j).toNat % 8 = 0 := by
  have source := pointer_offset_nat slot (64*j) (by omega)
  have heapNat : (BitVec.ofNat 64 heap).toNat = heap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [MEMORY_BYTES] at heapBound; omega)]
  rw [slotPointer]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rangeValid, source, decide_eq_true_eq]; omega
  · rw [source]; omega
  · unfold chainOutput
    split
    · simp only [rangeValid, heapPointer, heapNat, decide_eq_true_eq]; omega
    · rw [slotPointer]
      simp only [rangeValid, pointer_offset_nat slot (64*j+64) (by omega), decide_eq_true_eq]; omega
  · unfold chainOutput
    split
    · rw [heapPointer, heapNat]; exact heapAligned
    · rw [slotPointer, pointer_offset_nat slot (64*j+64) (by omega)]; omega

theorem chain_source_nat (s : MachineState) (j : Nat) (hj : j < 4) (slot : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 slot) (slotBound : slot + 288 ≤ MEMORY_BYTES) :
    (s.getReg .x8 + BitVec.ofNat 64 (64*j)).toNat = slot + 64*j := by
  rw [slotPointer]; exact pointer_offset_nat slot (64*j) (by omega)

end CommitGolfCandidate
