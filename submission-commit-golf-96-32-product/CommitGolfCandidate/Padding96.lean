import CommitGolfCandidate.Padding96Memory

/-! Instruction-level implementation of one padded compression call. The adapter
uses only ordinary RV64 loads/stores, a single 96-byte compression syscall, and a
return. Its extra instructions are included in execution fuel and cycle counts. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem write_bits_set_pc {bits : Nat} (state : MachineState) (address pc : Word)
    (answer : BitVec bits) :
    writeBits (state.setPC pc) address answer =
      (writeBits state address answer).setPC (pc+4) := by
  have commute (indices : List Nat) (state : MachineState) :
      indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) (state.setPC pc) =
      (indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) state).setPC pc := by
    induction indices generalizing state with
    | nil => rfl
    | cons i rest ih =>
      rw [List.foldl_cons]
      change rest.foldl _ ((state.setByte _ _).setPC pc) = _
      rw [ih]
      rfl
  unfold writeBits
  rw [commute]
  rfl

theorem write_bits_set_reg {bits : Nat} (state : MachineState) (address : Word)
    (reg : Reg) (value : Word) (answer : BitVec bits) :
    writeBits (state.setReg reg value) address answer =
      (writeBits state address answer).setReg reg value := by
  have byteCommute (state : MachineState) (address : Word) (byte : Byte) :
      (state.setReg reg value).setByte address byte =
        (state.setByte address byte).setReg reg value := by cases reg <;> rfl
  have commute (indices : List Nat) (state : MachineState) :
      indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) (state.setReg reg value) =
      (indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) state).setReg reg value := by
    induction indices generalizing state with
    | nil => rfl
    | cons i rest ih =>
      rw [List.foldl_cons, byteCommute, ih]
      rfl
  unfold writeBits
  rw [commute]
  cases reg <;> rfl

def savePaddingRegisters (state : MachineState) : MachineState :=
  (((state.setReg .x14 (state.getMem (state.getReg .x10+64))).setReg
    .x15 (state.getMem (state.getReg .x10+72))).setReg
    .x16 (state.getMem (state.getReg .x10+80))).setReg
    .x17 (state.getMem (state.getReg .x10+88))

/-- The adapter's externally visible effect. It restores the 64-byte caller
argument in x11 and clobbers x14..x17 and the local return register x31. -/
def paddedCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits ((savePaddingRegisters (state.setReg .x31 (state.pc+4))).setReg .x11 64)
    (state.getReg .x12) answer

theorem padded_compression_memory (state : MachineState) (answer : BitVec 256) :
    (paddedCompressionState state answer).mem =
      (writeBits state (state.getReg .x12) answer).mem :=
  write_bits_memory_congr _ _ _ _ rfl

theorem padded_compression_pc (state : MachineState) (answer : BitVec 256) :
    (paddedCompressionState state answer).pc = state.pc+4 := rfl

theorem padded_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not14 : reg ≠ .x14) (not15 : reg ≠ .x15) (not16 : reg ≠ .x16)
    (not17 : reg ≠ .x17) (not31 : reg ≠ .x31) (not11 : reg ≠ .x11) :
    (paddedCompressionState state answer).getReg reg = state.getReg reg := by
  rw [paddedCompressionState, writeBits_register]
  simp only [savePaddingRegisters,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not14),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not15),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not16),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not17),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not31),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11)]

def paddingSetupInstructions : List Instr :=
  [.LD .x14 .x10 64, .LD .x15 .x10 72, .LD .x16 .x10 80, .LD .x17 .x10 88,
   .SD .x10 .x0 64, .SD .x10 .x0 72, .SD .x10 .x0 80, .SD .x10 .x0 88,
   .ADDI .x11 .x0 96]

def paddingSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (paddingSetupInstructions.take count).foldl execInstrBr state

def paddingFinishInstructions : List Instr :=
  [.SD .x10 .x14 64, .SD .x10 .x15 72, .SD .x10 .x16 80, .SD .x10 .x17 88,
   .ADDI .x11 .x0 64, .JALR .x0 .x31 0]

def paddingFinishPrefix (state : MachineState) (count : Nat) : MachineState :=
  (paddingFinishInstructions.take count).foldl execInstrBr state

theorem padding_setup_shape (state : MachineState) :
    paddingSetupPrefix state 9 =
      ((padMemory (savePaddingRegisters state) (state.getReg .x10)).setReg .x11 96).setPC
        (state.pc+36) := by
  simp [paddingSetupPrefix, paddingSetupInstructions, savePaddingRegisters, padMemory,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    MachineState.setMem, MachineState.getMem, BitVec.add_assoc]

/-- The suffix restores the four saved words before returning through x31. -/
theorem padding_finish_shape (state : MachineState) :
    paddingFinishPrefix state 6 =
      (((((state.setMem (state.getReg .x10+64) (state.getReg .x14)).setMem
        (state.getReg .x10+72) (state.getReg .x15)).setMem
        (state.getReg .x10+80) (state.getReg .x16)).setMem
        (state.getReg .x10+88) (state.getReg .x17)).setReg .x11 64).setPC
        (state.getReg .x31 &&& ~~~1) := by
  simp [paddingFinishPrefix, paddingFinishInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    MachineState.setMem, MachineState.getMem]

/-! ### The truncating adapter `tcomp` (A96): the padded compression, then
`andi x7,x9,1; srli x9,x9,1; beq x7,x0,+8; sh x0,30(x12); jalr x0,0(x31)`. -/

def tcompBit (state : MachineState) : Word := state.getReg .x9 &&& 1

/-- Instructions from the caller's `jal` to the return: 20, or 21 with the store. -/
def tcompSteps (state : MachineState) : Nat := if tcompBit state = 0 then 20 else 21

def tcompState (state : MachineState) (answer : BitVec 256) : MachineState :=
  let base := ((paddedCompressionState state answer).setReg .x7 (tcompBit state)).setReg .x9
    (state.getReg .x9 >>> 1)
  if tcompBit state = 0 then base else base.setHalfword (state.getReg .x12 + 30) 0

end CommitGolfCandidate
