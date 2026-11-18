import CommitGolfCandidate.CapNavigationImage

/-! The branches and zero-link jumps between cap DFS macros. They change
only PC and each costs one real instruction/cycle. Their decoded immediate
and phase-specific fetch are retained explicitly. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

inductive CapFlow where
  | equal (left right : Reg) (offset : BitVec 13)
  | below (left right : Reg) (offset : BitVec 13)
  | aboveEqual (left right : Reg) (offset : BitVec 13)
  | jump (offset : BitVec 21)

def capFlowInstruction : CapFlow → Instr
  | .equal left right offset => .BEQ left right offset
  | .below left right offset => .BLTU left right offset
  | .aboveEqual left right offset => .BGEU left right offset
  | .jump offset => .JAL .x0 offset

def capFlowState (flow : CapFlow) (state : MachineState) : MachineState :=
  execInstrBr state (capFlowInstruction flow)

theorem cap_flow_execute (image : Image) (flow : CapFlow) (state : MachineState)
    (fetched : fetch image state = some (.base (capFlowInstruction flow)))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1 + fuel) state allowCoins =
      (do let result ← execute image fuel (capFlowState flow state) allowCoins
          return result.charge 1 0) := by
  have step : ordinaryStep state (.base (capFlowInstruction flow)) =
      some (capFlowState flow state) := by
    cases flow <;> rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched step]
  cases flow <;> rfl

theorem cap_flow_memory (flow : CapFlow) (state : MachineState) :
    (capFlowState flow state).mem = state.mem := by
  cases flow <;> simp only [capFlowState, capFlowInstruction, execInstrBr]
  all_goals first | split <;> rfl | rfl

theorem cap_flow_register (flow : CapFlow) (state : MachineState) (reg : Reg) :
    (capFlowState flow state).getReg reg = state.getReg reg := by
  cases flow <;> simp only [capFlowState, capFlowInstruction, execInstrBr]
  all_goals first
    | split <;> exact MachineState.getReg_setPC
    | cases reg <;> rfl

theorem cap_flow_equal_pc (state : MachineState) (left right : Reg)
    (offset : BitVec 13) :
    (capFlowState (.equal left right offset) state).pc =
      if state.getReg left = state.getReg right
        then state.pc + signExtend13 offset else state.pc + 4 := by
  simp only [capFlowState, capFlowInstruction, execInstrBr]
  split <;> simp_all [MachineState.setPC]

theorem cap_flow_below_pc (state : MachineState) (left right : Reg)
    (offset : BitVec 13) :
    (capFlowState (.below left right offset) state).pc =
      if state.getReg left < state.getReg right
        then state.pc + signExtend13 offset else state.pc + 4 := by
  simp only [capFlowState, capFlowInstruction, execInstrBr, BitVec.ult_eq_decide_lt,
    decide_eq_true_eq]
  split <;> simp_all [MachineState.setPC]

theorem cap_flow_above_equal_pc (state : MachineState) (left right : Reg)
    (offset : BitVec 13) :
    (capFlowState (.aboveEqual left right offset) state).pc =
      if ¬ state.getReg left < state.getReg right
        then state.pc + signExtend13 offset else state.pc + 4 := by
  simp only [capFlowState, capFlowInstruction, execInstrBr, BitVec.ult_eq_decide_lt,
    decide_eq_true_eq]
  split <;> simp_all [MachineState.setPC]

theorem cap_flow_jump_pc (state : MachineState) (offset : BitVec 21) :
    (capFlowState (.jump offset) state).pc = state.pc + signExtend21 offset := rfl

/-- Actual DFS control sites, including the checker's proof-end guard. -/
def capFlowSites (checking : Bool) : List (Nat × CapFlow) :=
  if checking then
    [(130, .equal .x6 .x0 20), (131, .aboveEqual .x20 .x19 68),
     (133, .jump 2097128),
     (136, .below .x22 .x6 168), (148, .equal .x20 .x31 48),
     (150, .equal .x7 .x0 32), (157, .jump 1144),
     (159, .jump 2097024), (444, .jump 2095968)]
  else
    [(84, .equal .x6 .x0 20), (85, .aboveEqual .x20 .x29 60),
     (87, .jump 2097128),
     (100, .equal .x20 .x31 28), (102, .equal .x7 .x0 12),
     (104, .jump 2097136), (106, .jump 2097052)]

theorem cap_flow_image_fetched (checking : Bool) (site : Nat × CapFlow)
    (member : site ∈ capFlowSites checking) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * site.1)) :
    fetch (capWalkImage checking) state =
      some (.base (capFlowInstruction site.2)) := by
  cases checking <;> simp only [capFlowSites, Bool.false_eq_true, ↓reduceIte,
    List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply cap_image_fetch _ state _ _ (by decide) pc
    rfl

end CommitGolfCandidate
