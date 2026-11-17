import CommitGolfCandidate.CapPrograms
import CommitGolfCandidate.CapMarkPassExecution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cap_image_fetch (image : Image) (state : MachineState)
    (index : Nat) (instruction : Instr) (bounded : index < 512)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (image.code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch image state = some (.base instruction) := by
  have numeric : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, if_pos (by omega)]
  rw [show (4096 + 4 * index - 4096) / 4 = index by omega]
  cases entry : image.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

theorem cap_open_mark_header :
    CapMarkHeaderFetched ((capExperimental 24).image .opening) .x29 4364 := by
  intro state pc
  constructor
  · apply cap_image_fetch _ state 67 _ (by decide) pc
    rfl
  · apply cap_image_fetch _ (capMarkHeaderSet .x29 state) 68 _ (by decide)
    · simp only [capMarkHeaderSet, execInstrBr, MachineState.setPC]
      rw [pc]
      rfl
    · rfl

theorem cap_check_mark_header :
    CapMarkHeaderFetched ((capExperimental 24).image .check) .x19 4548 := by
  intro state pc
  constructor
  · apply cap_image_fetch _ state 113 _ (by decide) pc
    rfl
  · apply cap_image_fetch _ (capMarkHeaderSet .x19 state) 114 _ (by decide)
    · simp only [capMarkHeaderSet, execInstrBr, MachineState.setPC]
      rw [pc]
      rfl
    · rfl

theorem cap_open_mark_body :
    CapMarkFetched ((capExperimental 24).image .opening) .x22 4372 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capMarkPrefix .x22 state i) (69 + i) _ (by omega)
  · rw [cap_mark_prefix_pc .x22 state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_mark_body :
    CapMarkFetched ((capExperimental 24).image .check) .x9 4556 := by
  intro state i bounded pc
  apply cap_image_fetch _ (capMarkPrefix .x9 state i) (115 + i) _ (by omega)
  · rw [cap_mark_prefix_pc .x9 state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_open_mark_execute (state : MachineState) (marked : Nat → Bool)
    (equations : ∀ node, 0 < node → node < 256 →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (pc : state.pc = 4364) (base : state.getReg .x22 = 28672)
    (count : state.getReg .x29 = 256)
    (ready : CapMarksReady state 256 255 marked) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (2552 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capMarkMachinePass .x22 .x29 state 256) allowCoins
          return result.charge 2552 0) := by
  exact cap_mark_pass_execute _ .x22 .x29 4364 cap_open_mark_header
    cap_open_mark_body (Or.inr rfl) 256 marked (by decide) (by decide)
    equations state pc base count ready fuel allowCoins

theorem cap_check_mark_execute (state : MachineState) (marked : Nat → Bool)
    (equations : ∀ node, 0 < node → node < 256 →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (pc : state.pc = 4548) (base : state.getReg .x9 = 28672)
    (count : state.getReg .x19 = 256)
    (ready : CapMarksReady state 256 255 marked) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (2552 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capMarkMachinePass .x9 .x19 state 256) allowCoins
          return result.charge 2552 0) := by
  exact cap_mark_pass_execute _ .x9 .x19 4548 cap_check_mark_header
    cap_check_mark_body (Or.inl rfl) 256 marked (by decide) (by decide)
    equations state pc base count ready fuel allowCoins

end CommitGolfCandidate
