import CommitGolfCandidate.TwoPermutationPackedTaglessLeafSpec
import CommitGolfCandidate.TwoPermutationLeafRun

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
def firstInstructions (slot : Fin 4096) : List Instr :=
  [.SD .x10 .x10 0, .SD .x10 .x0 8, .SD .x10 .x0 16,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot.val%128))), .SD .x10 .x31 24,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot.val%128) + 8)), .SD .x10 .x31 32,
   .ADDI .x12 .x10 0]

def secondInstructions (slot : Fin 4096) : List Instr :=
  [.ADDI .x10 .x10 96,
   .ADDI .x12 .x20 (BitVec.ofNat 12 (32*(slot.val%64)))]

def leafInstructions (slot : Fin 4096) : List Instr :=
  firstInstructions slot ++ [.ECALL] ++ secondInstructions slot ++ [.ECALL, .ADDI .x10 .x10 160]

private theorem store_preserves_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

private theorem zero_register (state : MachineState) : state.getReg .x0 = 0 := rfl

private theorem nonce_offsets_table : ∀ slot : Fin 128,
    signExtend12 (BitVec.ofNat 12 (16*slot.val)) = BitVec.ofNat 64 (16*slot.val) ∧
    signExtend12 (BitVec.ofNat 12 (16*slot.val + 8)) = BitVec.ofNat 64 (16*slot.val + 8) := by decide

private theorem nonce_offsets (slot : Fin 4096) :
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128))) = BitVec.ofNat 64 (16*(slot.val%128)) ∧
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128) + 8)) = BitVec.ofNat 64 (16*(slot.val%128) + 8) :=
  nonce_offsets_table ⟨slot.val%128, Nat.mod_lt _ (by decide)⟩

private theorem output_offset_table : ∀ slot : Fin 64,
    signExtend12 (BitVec.ofNat 12 (32*slot.val)) = BitVec.ofNat 64 (32*slot.val) := by decide

private theorem output_offset (slot : Fin 4096) :
    signExtend12 (BitVec.ofNat 12 (32*(slot.val%64))) = BitVec.ofNat 64 (32*(slot.val%64)) :=
  output_offset_table ⟨slot.val%64, Nat.mod_lt _ (by decide)⟩

def firstMemory (state : MachineState) (slot : Fin 4096) : MachineState :=
  let addr := state.getReg .x10
  let nonce := state.getReg .x22
  let nonce₀ := state.getMem (nonce + BitVec.ofNat 64 (16*(slot.val%128)))
  let nonce₁ := state.getMem (nonce + BitVec.ofNat 64 (16*(slot.val%128) + 8))
  let initialized := (((state.setMem addr addr).setMem (addr + 8) 0).setMem (addr + 16) 0)
  (initialized.setMem (addr + 24) nonce₀).setMem (addr + 32) nonce₁

theorem first_execution (state : MachineState) (slot : Fin 4096)
    (firstDisjoint : ∀ offset ∈ ([0, 8, 16] : List Word),
      state.getReg .x22 + BitVec.ofNat 64 (16*(slot.val%128)) ≠ state.getReg .x10 + offset)
    (secondDisjoint : ∀ offset ∈ ([0, 8, 16, 24] : List Word),
      state.getReg .x22 + BitVec.ofNat 64 (16*(slot.val%128) + 8) ≠ state.getReg .x10 + offset) :
    let before := (firstInstructions slot).foldl execInstrBr state
    before.mem = (firstMemory state slot).mem ∧
    before.getReg .x10 = state.getReg .x10 ∧ before.getReg .x12 = state.getReg .x10 ∧
    before.getReg .x5 = state.getReg .x5 ∧ before.getReg .x11 = state.getReg .x11 ∧
    before.getReg .x13 = state.getReg .x13 ∧ before.pc = state.pc + 32 := by
  have d0 := firstDisjoint 0 (by decide)
  have d8 := firstDisjoint 8 (by decide)
  have d16 := firstDisjoint 16 (by decide)
  have e0 := secondDisjoint 0 (by decide)
  have e8 := secondDisjoint 8 (by decide)
  have e16 := secondDisjoint 16 (by decide)
  have e24 := secondDisjoint 24 (by decide)
  have d0' : state.getReg .x22 + BitVec.ofNat 64 (16*(slot.val%128)) ≠ state.getReg .x10 := by
    simpa using d0
  have e0' : state.getReg .x22 + BitVec.ofNat 64 (16*(slot.val%128) + 8) ≠ state.getReg .x10 := by
    simpa using e0
  have offset := nonce_offsets slot
  simp only [firstInstructions, firstMemory, List.foldl_cons, List.foldl_nil, execInstrBr,
    show signExtend12 0 = (0 : Word) by decide, show signExtend12 8 = (8 : Word) by decide,
    show signExtend12 16 = (16 : Word) by decide, show signExtend12 24 = (24 : Word) by decide,
    show signExtend12 32 = (32 : Word) by decide,
    MachineState.getReg_setPC, store_preserves_register,
    MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x22),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x13),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x13),
    MachineState.getMem_setReg, MachineState.getMem_setPC,
    MachineState.getMem_setMem_ne d8, MachineState.getMem_setMem_ne d16,
    MachineState.getMem_setMem_ne e8, MachineState.getMem_setMem_ne e16,
    MachineState.getMem_setMem_ne e24, offset.1, offset.2]
  simp [MachineState.setReg, MachineState.setMem, MachineState.setPC, MachineState.getMem,
    BitVec.add_assoc, zero_register, d0', e0']

theorem second_execution (state : MachineState) (slot : Fin 4096) :
    let before := (secondInstructions slot).foldl execInstrBr state
    let addr := state.getReg .x10 + 96
    before.mem = state.mem ∧ before.getReg .x10 = addr ∧
    before.getReg .x12 = state.getReg .x20 + BitVec.ofNat 64 (32*(slot.val%64)) ∧
    before.getReg .x5 = state.getReg .x5 ∧ before.getReg .x11 = state.getReg .x11 ∧
    before.getReg .x13 = state.getReg .x13 ∧ before.pc = state.pc + 8 := by
  simp only [secondInstructions, List.foldl_cons, List.foldl_nil, execInstrBr,
    show signExtend12 0 = (0 : Word) by decide, show signExtend12 1 = (1 : Word) by decide,
    show signExtend12 96 = (96 : Word) by decide,
    MachineState.getReg_setPC, store_preserves_register,
    MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x13),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x13),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x13), output_offset]
  simp [MachineState.setReg, MachineState.setMem, MachineState.setPC, BitVec.add_assoc]


end TwoPermutationPrototype.RV64.PackedLeaves
