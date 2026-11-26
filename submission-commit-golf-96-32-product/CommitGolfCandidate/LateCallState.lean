import CommitGolfCandidate.LateCalls
import CommitGolfCandidate.LateLeafMemory

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem call_pc (s : MachineState) (src dst : Reg) (a b : BitVec 12) (w : Digest) :
    (callState s src dst a b w).pc = s.pc+12 := by
  change s.pc+4+4+4 = _
  simp only [BitVec.add_assoc]; rfl

theorem call_register (s : MachineState) (src dst reg : Reg) (a b : BitVec 12) (w : Digest)
    (h₁ : .x10 ≠ reg) (h₂ : .x12 ≠ reg) :
    (callState s src dst a b w).getReg reg = s.getReg reg := by
  simp only [callState, writeBits_register, prepareCall, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ h₁, MachineState.getReg_setReg_ne _ _ _ _ h₂]

theorem call_addresses (s : MachineState) (src dst : Reg) (a b : BitVec 12)
    (indep : Reg.x10 ≠ dst) :
    let ready := prepareCall s src dst a b
    ready.getReg .x10 = s.getReg src + signExtend12 a ∧
    ready.getReg .x12 = s.getReg dst + signExtend12 b := by
  simp only [prepareCall, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ indep, true_and]

theorem call_memory (s : MachineState) (src dst : Reg) (a b : BitVec 12) (w : Digest)
    (indep : Reg.x10 ≠ dst) :
    (callState s src dst a b w).mem =
      (writeBits s (s.getReg dst + signExtend12 b) w).mem := by
  dsimp only [callState]
  rw [(call_addresses s src dst a b indep).2]
  exact write_bits_memory_congr _ _ _ _ rfl

theorem call_read (s : MachineState) (src dst : Reg) (a b : BitVec 12) (w : Digest)
    (indep : Reg.x10 ≠ dst) (addr n : Nat) :
    readBuffer (callState s src dst a b w) addr n =
      readBuffer (writeBits s (s.getReg dst + signExtend12 b) w) addr n := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, call_memory s src dst a b w indep]

end CommitGolfCandidate.Late
