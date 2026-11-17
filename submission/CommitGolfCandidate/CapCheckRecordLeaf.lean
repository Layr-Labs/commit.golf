import CommitGolfCandidate.CapCheckSaltFrame
import CommitGolfCandidate.CapCheckLeafCall
import CommitGolfCandidate.CapCheckLeafFrame
import CommitGolfCandidate.CapCheckLeafSemantics

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckSaltState capCheckLeafCallState

def capCheckRecordLeafStart (state : MachineState) : MachineState :=
  ((capCheckLeafCallState (capCheckSaltState state)).setReg .x28 8).setPC 4824

def capCheckRecordLeaf (state : MachineState) : OracleComp World MachineState := do
  let finished ← capCheckLeafLoop (capCheckRecordLeafStart state) 8
  return finished.setPC 4256

theorem cap_check_record_leaf_start_register (state : MachineState) (reg : Reg)
    (outside : reg ∉ [Reg.x20, .x6, .x25, .x1, .x28]) :
    (capCheckRecordLeafStart state).getReg reg = state.getReg reg := by
  have not1 : reg ≠ .x1 := by simp_all
  have not28 : reg ≠ .x28 := by simp_all
  have saltOutside : reg ∉ [Reg.x20, .x6, .x25] := by simp_all
  unfold capCheckRecordLeafStart
  rw [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    cap_check_leaf_call_register _ reg not1,
    cap_check_salt_register state reg saltOutside]

theorem cap_check_record_leaf_execute (state : MachineState) (pc : state.pc = 4212)
    (scratch : state.getReg .x21 = 256)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (149 + fuel) state allowCoins =
      (do let finished ← capCheckRecordLeaf state
          let result ← execute ((capExperimental 24).image .check) fuel finished allowCoins
          return result.charge 205 8) := by
  have nextScratch := (cap_check_salt_register state .x21 (by decide)).trans scratch
  have nextSource : ∀ word < 32,
      accessValid ((capCheckSaltState state).getReg .x8 +
        BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa only [cap_check_salt_register state .x8 (by decide)] using sourceValid
  rw [show 149 + fuel = 10 + (139 + fuel) by omega,
    cap_check_salt_execute state pc scratch indexValid saltValid,
    cap_check_leaf_call_execute _ (cap_check_salt_pc state pc)
      nextScratch nextSource]
  simp only [capCheckRecordLeaf, capCheckRecordLeafStart, bind_assoc, pure_bind]
  congr 1
  funext finished
  simp [Execution.charge, ← Nat.add_assoc]

theorem cap_check_record_leaf_query_bound (state : MachineState) :
    IsTotalQueryBound (capCheckRecordLeaf state) 8 := by
  unfold capCheckRecordLeaf
  have pureBound : ∀ finished : MachineState,
      IsTotalQueryBound (pure (finished.setPC 4256) : OracleComp World MachineState) 0 :=
    fun _ => by trivial
  exact isTotalQueryBound_bind (cap_check_leaf_loop_query_bound _ 8) pureBound

theorem cap_check_record_leaf_register (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) (reg : Reg)
    (outside : reg ∉ [Reg.x20, .x6, .x25, .x1, .x28,
      .x5, .x8, .x10, .x11, .x12, .x13]) :
    finished.getReg reg = state.getReg reg := by
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, bodyReachable, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  subst finished
  rw [MachineState.getReg_setPC]
  exact (cap_check_leaf_loop_register_frame _ 8 body bodyReachable reg
    (by simp_all)).trans (cap_check_record_leaf_start_register state reg (by simp_all))

end CommitGolfCandidate
