import CommitGolfCandidate.CapCheckSaltFrame
import CommitGolfCandidate.CapCheckLeafCall
import CommitGolfCandidate.CapCheckLeafFrame
import CommitGolfCandidate.CapCheckLeafSemantics

/-! Actual salt setup and the paid stage-3 leaf routine form the first
part of each checker record. Every load is admitted before execution; the
arbitrary-reply computation is retained for subsequent path processing. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckSaltState capCheckLeafCallState

def capCheckRecordLeafStart (state : MachineState) : MachineState :=
  capCheckLeafCallState (capCheckSaltState state)

def capCheckRecordLeaf (state : MachineState) : OracleComp World MachineState := do
  let finished ← capCheckLeaf (capCheckRecordLeafStart state)
  return finished.setPC 4256

theorem cap_check_record_leaf_start_register (state : MachineState) (reg : Reg)
    (outside : reg ∉ [Reg.x20, .x6, .x25, .x1]) :
    (capCheckRecordLeafStart state).getReg reg = state.getReg reg := by
  have not1 : reg ≠ .x1 := by simp_all
  have saltOutside : reg ∉ [Reg.x20, .x6, .x25] := by simp_all
  unfold capCheckRecordLeafStart
  rw [cap_check_leaf_call_register _ reg not1,
    cap_check_salt_register state reg saltOutside]

/-- 101 instructions, 115 cycles and two permutation calls. -/
theorem cap_check_record_leaf_execute (state : MachineState) (pc : state.pc = 4212)
    (scratch : state.getReg .x21 = 256)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (101 + fuel) state allowCoins =
      (do let finished ← capCheckRecordLeaf state
          let result ← execute ((capExperimental 24).image .check) fuel finished allowCoins
          return result.charge 115 2) := by
  have nextSource : ∀ word < 32,
      accessValid ((capCheckSaltState state).getReg .x8 +
        BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa only [cap_check_salt_register state .x8 (by decide)] using sourceValid
  rw [show 101 + fuel = 10 + (91 + fuel) by omega,
    cap_check_salt_execute state pc scratch indexValid saltValid,
    cap_check_leaf_call_execute _ (cap_check_salt_pc state pc) nextSource]
  simp only [capCheckRecordLeaf, capCheckRecordLeafStart, bind_assoc, pure_bind]
  congr 1
  funext finished
  simp [Execution.charge, ← Nat.add_assoc]

theorem cap_check_record_leaf_query_bound (state : MachineState) :
    IsTotalQueryBound (capCheckRecordLeaf state) 2 := by
  unfold capCheckRecordLeaf
  have pureBound : ∀ finished : MachineState,
      IsTotalQueryBound (pure (finished.setPC 4256) : OracleComp World MachineState) 0 :=
    fun _ => by trivial
  exact isTotalQueryBound_bind (cap_check_leaf_query_bound _) pureBound

/-- Every reachable result is the leaf result with the return address as PC. -/
theorem cap_check_record_leaf_support (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    ∃ body, body ∈ support (capCheckLeaf (capCheckRecordLeafStart state)) ∧
      finished = body.setPC 4256 := by
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, bodyReachable, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  exact ⟨body, bodyReachable, tail⟩

theorem cap_check_record_leaf_pc (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) : finished.pc = 4256 := by
  obtain ⟨body, _, rfl⟩ := cap_check_record_leaf_support state finished reachable
  rfl

theorem cap_check_record_leaf_register (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) (reg : Reg)
    (outside : reg ∉ [Reg.x20, .x6, .x25, .x1, .x28,
      .x5, .x8, .x10, .x11, .x12, .x13]) :
    finished.getReg reg = state.getReg reg := by
  obtain ⟨body, bodyReachable, rfl⟩ := cap_check_record_leaf_support state finished reachable
  rw [MachineState.getReg_setPC]
  exact (cap_check_leaf_register_frame _ body bodyReachable reg
    (by simp_all)).trans (cap_check_record_leaf_start_register state reg (by simp_all))

end CommitGolfCandidate
