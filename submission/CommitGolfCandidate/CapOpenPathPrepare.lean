import CommitGolfCandidate.CapDigestCopy

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenPathInstructions : List Instr :=
  [.XORI .x7 .x20 1, .SLLI .x7 .x7 5, .ADD .x23 .x9 .x7]

def capOpenPathPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capOpenPathInstructions.take count).foldl execInstrBr state

theorem cap_open_path_prepare_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) :
    (capOpenPathPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capOpenPathPrefix, capOpenPathInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_open_path_prepare_memory (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) : (capOpenPathPrefix state count).mem = state.mem := by
  interval_cases count <;> rfl

theorem cap_open_path_prepare_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) (reg : Reg) (outside : reg ≠ .x7 ∧ reg ≠ .x23) :
    (capOpenPathPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capOpenPathPrefix, capOpenPathInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2)]

theorem cap_open_path_address (state : MachineState) (node rootBase : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (base : state.getReg .x9 = BitVec.ofNat 64 rootBase) :
    (capOpenPathPrefix state 3).getReg .x23 =
      BitVec.ofNat 64 (rootBase + 32*(node ^^^ 1)) := by
  simp (disch := decide) only [capOpenPathPrefix, capOpenPathInstructions, List.take,
    List.foldl, execInstrBr, signExtend12, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, index, base,
    show (5 : BitVec 6).toNat = 5 by decide]
  change BitVec.ofNat 64 rootBase + (BitVec.ofNat 64 node ^^^ BitVec.ofNat 64 1) <<< 5 = _
  rw [← BitVec.ofNat_xor, BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 5 = BitVec.ofNat 64 32 by decide,
    ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm (node ^^^ 1) 32]

theorem cap_open_path_prepare_execute (state : MachineState)
    (pc : state.pc = 4280) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (3+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenPathPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := capOpenPathPrefix state)
  intro i bounded
  refine ⟨.base ((capOpenPathInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (46+i) _ (by omega)
    · rw [cap_open_path_prepare_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_open_path_copy_fetched :
    CapDigestCopyFetched ((capExperimental 24).image .opening) false 4292 := by
  intro state i bounded pc
  apply cap_image_fetch _ _ (49+i) _ (by omega)
  · rw [cap_copy_prefix_pc false state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
