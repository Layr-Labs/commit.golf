import CommitGolfCandidate.CapCompressionStep
import CommitGolfCandidate.CapMarkImage

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capRootAddress (node : Nat) : Word := BitVec.ofNat 64 (12288 + 32 * node)

def capParentInstructions : List Instr :=
  [.SLLI .x10 .x20 6, .ADD .x10 .x18 .x10,
   .SLLI .x12 .x20 5, .ADD .x12 .x18 .x12]

def capParentPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capParentInstructions.take count).foldl execInstrBr state

def CapParentPrepareFetched (image : Image) (entry : Word) : Prop :=
  ∀ state : MachineState, ∀ i < 4, state.pc = entry →
    fetch image (capParentPrefix state i) =
      some (.base ((capParentInstructions[i]?).getD .EBREAK))

theorem cap_parent_prefix_succ (state : MachineState) (count : Nat)
    (bounded : count < 4) :
    capParentPrefix state (count + 1) =
      execInstrBr (capParentPrefix state count)
        ((capParentInstructions[count]?).getD .EBREAK) := by
  interval_cases count <;> rfl

theorem cap_parent_prefix_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 4) :
    (capParentPrefix state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capParentPrefix, capParentInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  · rfl
  · rfl
  · rfl
  · rfl

theorem cap_parent_prefix_memory (state : MachineState) (count : Nat)
    (bounded : count ≤ 4) : (capParentPrefix state count).mem = state.mem := by
  interval_cases count <;> rfl

theorem cap_parent_prefix_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 4) (reg : Reg) (outside : reg ≠ .x10 ∧ reg ≠ .x12) :
    (capParentPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capParentPrefix, capParentInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2)]

private theorem root_pointer (node shift width : Nat) (factor : 2^shift = width) :
    (12288 : Word) + (BitVec.ofNat 64 node <<< shift) =
      BitVec.ofNat 64 (12288 + width * node) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  rw [show BitVec.twoPow 64 shift = BitVec.ofNat 64 (2^shift) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_twoPow, BitVec.toNat_ofNat]]
  change BitVec.ofNat 64 12288 + BitVec.ofNat 64 node * BitVec.ofNat 64 (2^shift) = _
  rw [factor, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm node width]

theorem cap_parent_source (state : MachineState) (node : Nat)
    (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capParentPrefix state 4).getReg .x10 = BitVec.ofNat 64 (12288 + 64 * node) := by
  simp (disch := decide) only [capParentPrefix, capParentInstructions, List.take,
    List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    roots, index, show (6 : BitVec 6).toNat = 6 by decide]
  exact root_pointer node 6 64 (by decide)

theorem cap_parent_destination (state : MachineState) (node : Nat)
    (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capParentPrefix state 4).getReg .x12 = capRootAddress node := by
  simp (disch := decide) only [capParentPrefix, capParentInstructions, List.take,
    List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    roots, index, show (5 : BitVec 6).toNat = 5 by decide]
  exact root_pointer node 5 32 (by decide)

theorem cap_parent_access (node : Nat) (bounded : node < 256) :
    rangeValid (BitVec.ofNat 64 (12288 + 64 * node)) 64 = true ∧
    rangeValid (capRootAddress node) 32 = true ∧
    (BitVec.ofNat 64 (12288 + 64 * node)).toNat % 8 = 0 ∧
    (capRootAddress node).toNat % 8 = 0 := by
  have sourceNat : (BitVec.ofNat 64 (12288 + 64 * node)).toNat =
      12288 + 64 * node := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 12288 + 64 * node < 2^64)]
  have destinationNat : (capRootAddress node).toNat = 12288 + 32 * node := by
    rw [capRootAddress, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 12288 + 32 * node < 2^64)]
  simp only [rangeValid, sourceNat, destinationNat, decide_eq_true_eq, MEMORY_BYTES]
  omega

theorem cap_parent_prepare_execute (image : Image) (entry : Word)
    (fetched : CapParentPrepareFetched image entry)
    (state : MachineState) (pc : state.pc = entry) (fuel : Nat) (allowCoins : Bool) :
    execute image (4 + fuel) state allowCoins =
      (do let result ← execute image fuel (capParentPrefix state 4) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := capParentPrefix state)
  intro i bounded
  refine ⟨.base ((capParentInstructions[i]?).getD .EBREAK),
    fetched state i bounded pc, ?_, ?_⟩
  · rw [cap_parent_prefix_succ state i bounded]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_parent_prepare_fetched :
    CapParentPrepareFetched ((capExperimental 24).image .check) 4704 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capParentPrefix state i) (152 + i) _ (by omega)
  · rw [cap_parent_prefix_pc state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_parent_ecall_fetched (state : MachineState) (pc : state.pc = 4720) :
    fetch ((capExperimental 24).image .check) state = some (.base .ECALL) := by
  apply cap_image_fetch _ state 156 _ (by decide) pc
  rfl

end CommitGolfCandidate
