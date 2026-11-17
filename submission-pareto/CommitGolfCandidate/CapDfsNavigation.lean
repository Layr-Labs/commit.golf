import CommitGolfCandidate.CapVisitStep
import CommitGolfCandidate.CapDfsControl

/-! Real one-instruction navigation effects used by canonical cap DFS. The
natural node equations rule out wrapping; rank facts remain independent of
these machine bridges until whole-macro composition is established. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

inductive CapNavigation where
  | descend | ascend | sibling | parity

def capNavigationInstruction : CapNavigation → Instr
  | .descend => .SLLI .x20 .x20 1
  | .ascend => .SRLI .x20 .x20 1
  | .sibling => .ADDI .x20 .x20 1
  | .parity => .ANDI .x7 .x20 1

def capNavigationState (operation : CapNavigation) (state : MachineState) : MachineState :=
  execInstrBr state (capNavigationInstruction operation)

theorem cap_navigation_execute (image : Image) (operation : CapNavigation)
    (state : MachineState)
    (fetched : fetch image state = some (.base (capNavigationInstruction operation)))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1 + fuel) state allowCoins =
      (do let result ← execute image fuel (capNavigationState operation state) allowCoins
          return result.charge 1 0) := by
  have step : ordinaryStep state (.base (capNavigationInstruction operation)) =
      some (capNavigationState operation state) := by
    cases operation <;> rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched step]
  cases operation <;> rfl

theorem cap_navigation_pc (operation : CapNavigation) (state : MachineState) :
    (capNavigationState operation state).pc = state.pc + 4 := by
  cases operation <;> rfl

theorem cap_navigation_memory (operation : CapNavigation) (state : MachineState) :
    (capNavigationState operation state).mem = state.mem := by
  cases operation <;> rfl

theorem cap_navigation_register (operation : CapNavigation) (state : MachineState)
    (reg : Reg) (outside : reg ≠ .x20 ∧ reg ≠ .x7) :
    (capNavigationState operation state).getReg reg = state.getReg reg := by
  cases operation <;>
    simp only [capNavigationState, capNavigationInstruction, execInstrBr,
      MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2)]

private theorem descend_word (node : Nat) :
    BitVec.ofNat 64 node <<< 1 = BitVec.ofNat 64 (2 * node) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 node * BitVec.ofNat 64 2 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

private theorem ascend_word (node : Nat) (bounded : node < 512) :
    BitVec.ofNat 64 node >>> 1 = BitVec.ofNat 64 (node / 2) := by
  apply BitVec.eq_of_toNat_eq
  change node % 2^64 / 2 = node / 2 % 2^64
  rw [Nat.mod_eq_of_lt (by omega : node < 2^64),
    Nat.mod_eq_of_lt (by omega : node / 2 < 2^64)]

private theorem parity_word (node : Nat) (bounded : node < 512) :
    BitVec.ofNat 64 node &&& (1 : Word) = BitVec.ofNat 64 (node % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : node < 2^64),
    Nat.mod_eq_of_lt (by omega : node % 2 < 2^64),
    show (1 : Word).toNat = 1 by decide, Nat.and_one_is_mod]

theorem cap_navigation_descend (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capNavigationState .descend state).getReg .x20 = BitVec.ofNat 64 (2 * node) := by
  simp (disch := decide) only [capNavigationState, capNavigationInstruction, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, index,
    show (1 : BitVec 6).toNat = 1 by decide]
  exact descend_word node

theorem cap_navigation_ascend (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capNavigationState .ascend state).getReg .x20 = BitVec.ofNat 64 (node / 2) := by
  simp (disch := decide) only [capNavigationState, capNavigationInstruction, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, index,
    show (1 : BitVec 6).toNat = 1 by decide]
  exact ascend_word node bounded

theorem cap_navigation_sibling (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capNavigationState .sibling state).getReg .x20 = BitVec.ofNat 64 (node + 1) := by
  simp (disch := decide) only [capNavigationState, capNavigationInstruction, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, index,
    show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
  exact (BitVec.ofNat_add node 1).symm

theorem cap_navigation_parity (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capNavigationState .parity state).getReg .x7 = BitVec.ofNat 64 (node % 2) := by
  simp (disch := decide) only [capNavigationState, capNavigationInstruction, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, index,
    show signExtend12 (1 : BitVec 12) = (1 : Word) by decide]
  exact parity_word node bounded

end CommitGolfCandidate
