import CommitGolfCandidate.CapCheckRecordLeafFrame
import CommitGolfCandidate.CapCheckPathInit
import CommitGolfCandidate.CapCheckPathLoop
import CommitGolfCandidate.CapCheckPathOutcome

/-! A lower record pays for its salt, eight leaf queries and seventeen sibling
queries. Its parity-dependent instruction count uses the loaded index, which
is preserved through the arbitrary leaf replies and path-counter setup. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckPathInitPrefix capCheckPathLoopSteps execute

def capCheckLowerRecord (state : MachineState) : OracleComp World MachineState := do
  let leaf ← capCheckRecordLeaf state
  capCheckPathLoop (capCheckPathInitState leaf) 17

def capCheckLowerRecordSteps (state : MachineState) : Nat :=
  153+capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 17

theorem cap_check_record_leaf_pc (state finished : MachineState)
    (reachable : finished ∈ support (capCheckRecordLeaf state)) :
    finished.pc = 4256 := by
  simp only [capCheckRecordLeaf, mem_support_bind_iff] at reachable
  obtain ⟨body, _, tail⟩ := reachable
  simp only [support_pure, Set.mem_singleton_iff] at tail
  subst finished
  rfl

private theorem lower_charge (computation : OracleComp World Execution) (pathSteps : Nat) :
    (do
      let result ← (do
        let result ← (do
          let result ← computation
          return result.charge (pathSteps+119) 17)
        return result.charge 4 0)
      return result.charge 205 8) =
      (do let result ← computation; return result.charge (pathSteps+328) 25) := by
  simp [bind_assoc, Execution.charge, ← Nat.add_assoc]
  congr 1
  funext result
  congr 1
  omega

theorem cap_check_lower_record_execute (state : MachineState)
    (pc : state.pc = 4212) (scratch : state.getReg .x21 = 256)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8*word)) 8 = true)
    (siblingsValid : ∀ word < 68,
      accessValid (state.getReg .x25 + 32 + BitVec.ofNat 64 (8*word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check)
      (capCheckLowerRecordSteps state+fuel) state allowCoins =
      (do let finished ← capCheckLowerRecord state
          let result ← execute ((capExperimental 24).image .check) fuel finished allowCoins
          return result.charge
            (capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 17+328) 25) := by
  unfold capCheckLowerRecordSteps
  rw [show 153+capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 17+fuel =
      149+(4+(capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 17+fuel)) by omega,
    cap_check_record_leaf_execute state pc scratch indexValid saltValid sourceValid]
  unfold capCheckLowerRecord
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaf reachable
  have leafPC := cap_check_record_leaf_pc state leaf reachable
  have initScratch : (capCheckPathInitState leaf).getReg .x21 = 256 := by
    unfold capCheckPathInitState
    rw [MachineState.getReg_setPC,
      cap_check_path_init_register leaf 3 (by decide) .x21 (by decide),
      cap_check_record_leaf_register state leaf reachable .x21 (by decide)]
    exact scratch
  have initCounter : (capCheckPathInitState leaf).getReg .x29 = BitVec.ofNat 64 17 := by
    unfold capCheckPathInitState
    rw [MachineState.getReg_setPC, cap_check_path_init_counter]
    rfl
  have initIndex : (capCheckPathInitState leaf).getReg .x20 =
      state.getMem (state.getReg .x24) := by
    unfold capCheckPathInitState
    rw [MachineState.getReg_setPC,
      cap_check_path_init_register leaf 3 (by decide) .x20 (by decide)]
    exact cap_check_record_leaf_index state leaf reachable
  have initCursor : (capCheckPathInitState leaf).getReg .x25 = state.getReg .x25+32 := by
    unfold capCheckPathInitState
    rw [MachineState.getReg_setPC,
      cap_check_path_init_register leaf 3 (by decide) .x25 (by decide)]
    exact cap_check_record_leaf_cursor state leaf reachable
  have initValid : ∀ word < 4*17, accessValid
      ((capCheckPathInitState leaf).getReg .x25+BitVec.ofNat 64 (8*word)) 8 = true := by
    simpa only [initCursor] using siblingsValid
  rw [cap_check_path_init_execute leaf leafPC,
    ← initIndex,
    cap_check_path_loop_execute (capCheckPathInitState leaf) 17 (by decide)
      (fun _ => rfl) initCounter initScratch initValid]
  rw [initIndex]
  simp only [bind_assoc]
  apply congrArg (fun continuation =>
    capCheckPathLoop (capCheckPathInitState leaf) 17 >>= continuation)
  funext finished
  simpa only [bind_assoc] using lower_charge
    (execute ((capExperimental 24).image .check) fuel finished allowCoins)
    (capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 17)

theorem cap_check_lower_record_query_bound (state : MachineState) :
    IsTotalQueryBound (capCheckLowerRecord state) 25 := by
  unfold capCheckLowerRecord
  exact isTotalQueryBound_bind (cap_check_record_leaf_query_bound state)
    (fun leaf => cap_check_path_loop_query_bound (capCheckPathInitState leaf) 17)

end CommitGolfCandidate
