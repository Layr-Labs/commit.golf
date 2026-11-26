import CommitGolfCandidate.Check

/-! Execution of the commitment image's in-place leaf chain. Each iteration hashes two
leaves (lanes `k = 0, 1`); lane `k`'s salt slot is `x8 + 256*k`. The four calls of one
leaf compress the contiguous 96 bytes `[chaining value | 64-byte block]` starting at
`x8 + 256*k + 64*j` and write the 32-byte reply either over the last consumed 32 bytes
(`x8 + 256*k + 64*j + 64`, calls 0..2) or into the heap slot `x23 + 32*k` (call 3). -/
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

/-- The two pointer instructions before in-place call `j` of lane `k`. -/
def chainCallInstructions (k j : Nat) : List Instr :=
  [.ADDI .x10 .x8 (BitVec.ofNat 12 (64*j+256*k)),
   if j = 3 then .ADDI .x12 .x23 (BitVec.ofNat 12 (32*k))
   else .ADDI .x12 .x8 (BitVec.ofNat 12 (64*j+64+256*k))]

private def chainCallPrefix (state : MachineState) (k j count : Nat) : MachineState :=
  ((chainCallInstructions k j).take count).foldl execInstrBr state

def chainSetupState (state : MachineState) (k j : Nat) : MachineState := chainCallPrefix state k j 2

/-- Input address of call `j` of lane `k`. -/
def chainSource (state : MachineState) (k j : Nat) : Word :=
  state.getReg .x8 + BitVec.ofNat 64 (64*j+256*k)

/-- Output address of call `j` of lane `k`. -/
def chainOutput (state : MachineState) (k j : Nat) : Word :=
  if j = 3 then state.getReg .x23 + BitVec.ofNat 64 (32*k)
  else state.getReg .x8 + BitVec.ofNat 64 (64*j+64+256*k)

/-- State after call `j`: the reply is written at the call's output address. -/
def chainCallState (state : MachineState) (k j : Nat) (answer : BitVec 256) : MachineState :=
  writeBits (chainSetupState state k j) (chainOutput state k j) answer

theorem chain_setup_memory (state : MachineState) (k j : Nat) :
    (chainSetupState state k j).mem = state.mem := by
  unfold chainSetupState chainCallPrefix chainCallInstructions
  split <;> rfl

theorem chain_setup_register (state : MachineState) (k j : Nat) (reg : Reg)
    (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainSetupState state k j).getReg reg = state.getReg reg := by
  unfold chainSetupState chainCallPrefix chainCallInstructions
  split <;>
    simp only [List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12)]

theorem chain_setup_registers (state : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 4) :
    (chainSetupState state k j).getReg .x10 = chainSource state k j ∧
    (chainSetupState state k j).getReg .x12 = chainOutput state k j ∧
    (chainSetupState state k j).pc = state.pc + 8 ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → (chainSetupState state k j).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, ?_, fun reg n10 n12 => chain_setup_register state k j reg n10 n12⟩ <;>
    interval_cases k <;> interval_cases j <;>
    simp [chainSetupState, chainCallPrefix, chainCallInstructions, chainOutput, chainSource, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.setPC, BitVec.add_assoc] <;>
    rfl

theorem chain_call_memory (state : MachineState) (k j : Nat) (answer : BitVec 256) :
    (chainCallState state k j answer).mem =
      (writeBits state (chainOutput state k j) answer).mem :=
  write_bits_memory_congr _ _ _ answer (chain_setup_memory state k j)

theorem chain_call_register (state : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 4)
    (answer : BitVec 256) (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainCallState state k j answer).getReg reg = state.getReg reg := by
  rw [chainCallState, writeBits_register]
  exact (chain_setup_registers state k j hk hj).2.2.2 reg n10 n12

theorem chain_call_pc (state : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 4)
    (answer : BitVec 256) :
    (chainCallState state k j answer).pc = state.pc + 12 := by
  simp only [chainCallState, writeBits, MachineState.setPC]
  rw [(chain_setup_registers state k j hk hj).2.2.1, BitVec.add_assoc]
  rfl

set_option maxHeartbeats 3200000 in
/-- In-place call `j` of lane `k` (instructions 46+19k+3j .. 48+19k+3j): two pointer
instructions and one direct 96-byte compression query. Ten cycles and one query. -/
theorem commit_chain_call (state : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (46 + 19*k + 3*j)))
    (r5 : state.getReg .x5 = 0) (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (sourceValid : rangeValid (chainSource state k j) 96 = true)
    (sourceAligned : (chainSource state k j).toNat % 8 = 0)
    (destinationValid : rangeValid (chainOutput state k j) 32 = true)
    (destinationAligned : (chainOutput state k j).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let answer ← World.query (.inr (.inl
            (readBuffer state (chainSource state k j).toNat 96)))
          let result ← execute (submission.image .commit) fuel (chainCallState state k j answer) true
          return result.charge 10 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (chainCallPrefix state k j 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := chainCallPrefix state k j)
    intro i hi
    refine ⟨.base (((chainCallInstructions k j)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (46 + 19*k + 3*j + i) _ (by omega)
      · interval_cases k <;> interval_cases j <;> interval_cases i <;>
          simp [chainCallPrefix, chainCallInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases k <;> interval_cases j <;> interval_cases i <;> rfl
    · interval_cases k <;> interval_cases j <;> interval_cases i <;> rfl
    · interval_cases k <;> interval_cases j <;> interval_cases i <;> rfl
  let ready := chainCallPrefix state k j 2
  have regs := chain_setup_registers state k j hk hj
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (48 + 19*k + 3*j)) := by
    change (chainSetupState state k j).pc = _
    rw [regs.2.2.1, pc]
    interval_cases k <;> interval_cases j <;> rfl
  have fetched : fetch (submission.image .commit) ready = some (.base .ECALL) := by
    apply commit_fetch _ (48 + 19*k + 3*j) _ (by omega) readyPC
    interval_cases k <;> interval_cases j <;> rfl
  have r5' : ready.getReg .x5 = 0 := (regs.2.2.2 .x5 (by decide) (by decide)).trans r5
  have r11' : ready.getReg .x11 = 96 := (regs.2.2.2 .x11 (by decide) (by decide)).trans r11
  have r13' : ready.getReg .x13 = 0 := (regs.2.2.2 .x13 (by decide) (by decide)).trans r13
  have r10' : ready.getReg .x10 = chainSource state k j := regs.1
  have r12' : ready.getReg .x12 = chainOutput state k j := regs.2.1
  have sv : rangeValid (ready.getReg .x10) 96 = true := by rw [r10']; exact sourceValid
  have sa : (ready.getReg .x10).toNat % 8 = 0 := by rw [r10']; exact sourceAligned
  have dv : rangeValid (ready.getReg .x12) 32 = true := by rw [r12']; exact destinationValid
  have da : (ready.getReg .x12).toNat % 8 = 0 := by rw [r12']; exact destinationAligned
  have memory : readBuffer ready (ready.getReg .x10).toNat 96 =
      readBuffer state (ready.getReg .x10).toNat 96 := by
    have sameMem : ready.mem = state.mem := chain_setup_memory state k j
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, sameMem]
  have input' : oracleInput ready = some (.inl (readBuffer state (ready.getReg .x10).toNat 96)) := by
    simp [oracleInput, r11', r13', sv, sa, dv, da, COMPRESSION_INPUT_LENGTH,
      COMPRESSION_OUTPUT_LENGTH, memory]
    try rw [r13']
    try simp [memory]
    try rfl
  have input : oracleInput ready = some (.inl
      (readBuffer state (chainSource state k j).toNat 96)) := by
    rw [input', r10']
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, setup, execute, fetched, if_pos r5', input]
  simp only [writeOracleAnswer, r12', bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl
      (readBuffer state (chainSource state k j).toNat 96)))) :
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

theorem chain_source_nat (s : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 4) (base : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 base) (slotBound : base + 544 ≤ MEMORY_BYTES) :
    (chainSource s k j).toNat = base + 256*k + 64*j := by
  unfold chainSource
  rw [slotPointer, pointer_offset_nat base (64*j+256*k) (by omega)]
  omega

theorem chain_output_slot_nat (s : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 3) (base : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 base) (slotBound : base + 544 ≤ MEMORY_BYTES) :
    chainOutput s k j = BitVec.ofNat 64 (base + 256*k + 64*j + 64) := by
  unfold chainOutput
  rw [if_neg (by omega), slotPointer, ← BitVec.ofNat_add]
  congr 1
  omega

theorem chain_output_heap_nat (s : MachineState) (k : Nat) (heap : Nat)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap) :
    chainOutput s k 3 = BitVec.ofNat 64 (heap + 32*k) := by
  unfold chainOutput
  rw [if_pos rfl, heapPointer, ← BitVec.ofNat_add]

theorem word_small_toNat (x : Nat) (small : x < 2^64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

/-- Address and alignment side conditions of in-place call `j` of lane `k` for a pair
whose first salt slot is `base` (lane input `[base+256k+64j, +96)`) and whose heap
pair starts at `heap` (output `heap+32k`). -/
theorem chain_call_valid (s : MachineState) (k j : Nat) (hk : k < 2) (hj : j < 4) (base heap : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 base) (slotAligned : base % 8 = 0)
    (slotBound : base + 544 ≤ MEMORY_BYTES)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap) (heapAligned : heap % 8 = 0)
    (heapBound : heap + 64 ≤ MEMORY_BYTES) :
    rangeValid (chainSource s k j) 96 = true ∧
    (chainSource s k j).toNat % 8 = 0 ∧
    rangeValid (chainOutput s k j) 32 = true ∧ (chainOutput s k j).toNat % 8 = 0 := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have source := chain_source_nat s k j hk hj base slotPointer slotBound
  have output : (chainOutput s k j).toNat =
      if j = 3 then heap + 32*k else base + 256*k + 64*j + 64 := by
    by_cases last : j = 3
    · subst last
      rw [chain_output_heap_nat s k heap heapPointer, word_small_toNat _ (by omega), if_pos rfl]
    · rw [chain_output_slot_nat s k j hk (by omega) base slotPointer slotBound,
        word_small_toNat _ (by omega), if_neg last]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rangeValid, source, decide_eq_true_eq]; omega
  · rw [source]; omega
  · simp only [rangeValid, output, decide_eq_true_eq]; split <;> omega
  · rw [output]; split <;> omega

end CommitGolfCandidate
