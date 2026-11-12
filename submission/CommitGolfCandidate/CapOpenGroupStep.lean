import CommitGolfCandidate.CapOpenRetainedInputs
import CommitGolfCandidate.CapMarkAlgebra
import CommitGolfCandidate.CapOrdinary

/-! Actual opening record exit. The reconstructed cap-group heap index selects
one low occupancy word, then the index pointer and request counter advance.
Every store is admitted at its actual prefix state. Mark semantics and the
outer request loop are separate from this six-instruction macro. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenGroupInstructions : List Instr :=
  [.SLLI .x7 .x20 3, .ADD .x23 .x22 .x7, .SD .x23 .x31 0,
   .ADDI .x24 .x24 8, .ADDI .x27 .x27 4095, .BNE .x27 .x0 8044]

def capOpenGroupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capOpenGroupInstructions.take count).foldl execInstrBr state

private theorem add_zero_word (word : Word) : word + (0 : Word) = word :=
  BitVec.add_zero word

private theorem fold_take_next {A S : Type} (step : S → A → S)
    (code : List A) (state : S) (fallback : A) (i : Nat) (hi : i < code.length) :
    (code.take (i+1)).foldl step state =
      step ((code.take i).foldl step state) ((code[i]?).getD fallback) := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos code i hi, Option.getD_some]

theorem cap_open_group_succ (state : MachineState) (count : Nat)
    (bounded : count < 6) :
    capOpenGroupPrefix state (count+1) =
      execInstrBr (capOpenGroupPrefix state count)
        ((capOpenGroupInstructions[count]?).getD .EBREAK) := by
  exact fold_take_next execInstrBr capOpenGroupInstructions state .EBREAK count
    (by simpa only [capOpenGroupInstructions, List.length_cons, List.length_nil] using bounded)

theorem cap_open_group_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 5) :
    (capOpenGroupPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capOpenGroupPrefix, capOpenGroupInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_open_group_address (state : MachineState) (node : Nat)
    (marks : state.getReg .x22 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capOpenGroupPrefix state 2).getReg .x23 = BitVec.ofNat 64 (28672+8*node) := by
  simp (disch := decide) only [capOpenGroupPrefix, capOpenGroupInstructions,
    List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, marks, index,
    show (3 : BitVec 6).toNat = 3 by decide]
  rw [BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 3 = BitVec.ofNat 64 8 by decide, ← BitVec.ofNat_mul]
  change BitVec.ofNat 64 28672 + BitVec.ofNat 64 (node*8) = _
  rw [← BitVec.ofNat_add, Nat.mul_comm node 8]

theorem cap_open_group_store_access (state : MachineState) (node : Nat)
    (marks : state.getReg .x22 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    accessValid ((capOpenGroupPrefix state 2).getReg .x23) 8 = true := by
  rw [cap_open_group_address state node marks index]
  exact (cap_mark_address_valid 256 node (by decide) (by omega)).1

theorem cap_open_group_execute (state : MachineState) (node : Nat)
    (pc : state.pc = 4340) (marks : state.getReg .x22 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (6+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenGroupPrefix state 6) allowCoins
          return result.charge 6 0) := by
  have storeAccess := cap_open_group_store_access state node marks index bounded
  apply execute_unit_steps (states := capOpenGroupPrefix state)
  intro i hi
  refine ⟨.base ((capOpenGroupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (61+i) _ (by omega)
    · rw [cap_open_group_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · rw [cap_open_group_succ state i hi]
    interval_cases i <;>
      simp only [capOpenGroupInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, signExtend12,
        show BitVec.signExtend 64 (0 : BitVec 12) = (0 : Word) by decide,
        add_zero_word, storeAccess,
        ↓reduceIte]
  · interval_cases i <;> rfl

end CommitGolfCandidate
