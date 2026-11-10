import CommitGolfCandidate.CapCheckGroupStart
import CommitGolfCandidate.CapMarkState

/-! The lookup's modular projections are independent of admission. Natural
group bounds then justify the real mark load and root-slot addresses. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_group_start_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 6) (reg : Reg)
    (outside : reg ∉ [.x20,.x7,.x30,.x23,.x6]) :
    (capCheckGroupStartPrefix state count).getReg reg = state.getReg reg := by
  have step : ∀ instruction ∈ capCheckGroupStartInstructions,
      ∀ current : MachineState,
        (execInstrBr current instruction).getReg reg = current.getReg reg := by
    intro instruction member current
    simp only [capCheckGroupStartInstructions, List.mem_cons, List.not_mem_nil,
      or_false] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [execInstrBr, MachineState.getReg_setPC]
      apply MachineState.getReg_setReg_ne
      intro equal
      subst reg
      tauto
  have fold : ∀ instructions : List Instr,
      (∀ instruction ∈ instructions, ∀ current : MachineState,
        (execInstrBr current instruction).getReg reg = current.getReg reg) →
      ∀ current : MachineState,
        (instructions.foldl execInstrBr current).getReg reg = current.getReg reg := by
    intro instructions
    induction instructions with
    | nil => intro _ current; rfl
    | cons instruction rest ih =>
      intro preserved current
      rw [List.foldl_cons, ih (fun i member => preserved i (List.mem_cons_of_mem _ member)),
        preserved instruction List.mem_cons_self]
  unfold capCheckGroupStartPrefix
  exact fold _ (fun instruction member => step instruction (List.mem_of_mem_take member)) state

theorem cap_check_group_start_projection (state : MachineState) :
    (capCheckGroupStartPrefix state 6).getReg .x20 =
      state.getReg .x20 + state.getReg .x19 ∧
    (capCheckGroupStartPrefix state 6).getReg .x30 =
      state.getReg .x9 + ((state.getReg .x20 + state.getReg .x19) <<< 3) ∧
    (capCheckGroupStartPrefix state 6).getReg .x23 =
      state.getReg .x18 + ((state.getReg .x20 + state.getReg .x19) <<< 5) ∧
    (capCheckGroupStartPrefix state 6).getReg .x6 =
      state.getMem (state.getReg .x9 + ((state.getReg .x20 + state.getReg .x19) <<< 3)) := by
  simp [capCheckGroupStartPrefix, capCheckGroupStartInstructions, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, MachineState.getMem_setPC]
  change state.getMem (state.getReg .x9 +
    ((state.getReg .x20 <<< 3) + (state.getReg .x19 <<< 3)) + (0#64)) = _
  rw [BitVec.add_zero]

theorem cap_check_group_start_addresses (state : MachineState) (group : Nat)
    (bounded : group < 128) (index : state.getReg .x20 = BitVec.ofNat 64 group)
    (leaves : state.getReg .x19 = 128) (marks : state.getReg .x9 = 20480)
    (roots : state.getReg .x18 = 12288) :
    (capCheckGroupStartPrefix state 6).getReg .x20 = BitVec.ofNat 64 (128+group) ∧
    (capCheckGroupStartPrefix state 6).getReg .x30 =
      BitVec.ofNat 64 (20480+8*(128+group)) ∧
    (capCheckGroupStartPrefix state 6).getReg .x23 =
      BitVec.ofNat 64 (12288+32*(128+group)) := by
  have projected := cap_check_group_start_projection state
  rw [index, leaves, marks, roots] at projected
  have add : BitVec.ofNat 64 group + (128 : Word) =
      BitVec.ofNat 64 (128+group) := by
    rw [show (128 : Word) = BitVec.ofNat 64 128 by rfl, ← BitVec.ofNat_add]
    congr 1
    omega
  rw [add] at projected
  have shifted3 : BitVec.ofNat 64 (128+group) <<< 3 =
      BitVec.ofNat 64 (8*(128+group)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 (128+group) * BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_mul]
    congr 1
    omega
  have shifted5 : BitVec.ofNat 64 (128+group) <<< 5 =
      BitVec.ofNat 64 (32*(128+group)) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 (128+group) * BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_mul]
    congr 1
    omega
  refine ⟨projected.1, ?_, ?_⟩
  · rw [projected.2.1, shifted3]
    exact (BitVec.ofNat_add (n := 64) 20480 _).symm
  · rw [projected.2.2.1, shifted5]
    exact (BitVec.ofNat_add (n := 64) 12288 _).symm

end CommitGolfCandidate
