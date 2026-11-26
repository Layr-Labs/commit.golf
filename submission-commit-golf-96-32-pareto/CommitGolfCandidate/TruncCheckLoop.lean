import CommitGolfCandidate.TruncCheckStep
import CommitGolfCandidate.PairPathValue
namespace CommitGolfCandidate.Trunc.Check
open CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap
set_option maxRecDepth 14000
set_option maxHeartbeats 1000000
def pathInstructions (index : Word) : Nat→Nat
  | 0=>0
  | k+1=>Late.Check.Normal.pathPreparationSteps index+37+pathInstructions (index >>> 1) k
theorem path_instruction_bounds (idx : Word) (n : Nat) : 47*n≤pathInstructions idx n ∧ pathInstructions idx n≤56*n := by
  induction n generalizing idx with
  | zero => simp [pathInstructions]
  | succ k ih =>
    have h:=ih (idx >>> 1);simp only [pathInstructions,Late.Check.Normal.pathPreparationSteps];split <;> omega


theorem rec_check_path_step_registers (state : MachineState) (answer : BitVec 256) :
    (rec_checkPathStepState state answer).getReg .x25 = state.getReg .x25 + 32 ∧
    (rec_checkPathStepState state answer).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (rec_checkPathStepState state answer).getReg .x29 = state.getReg .x29 - 1 ∧
    (rec_checkPathStepState state answer).getReg .x21 = state.getReg .x21 :=
  PairCap.rec_check_path_step_registers state (adjusted state answer) 

theorem rec_check_path_step_pc (state : MachineState) (answer : BitVec 256) :
    (rec_checkPathStepState state answer).pc = if state.getReg .x29 - 1 = 0 then 5120 else 4972 :=
  PairCap.rec_check_path_step_pc state (adjusted state answer) 

theorem rec_path_step_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29, .x14, .x15, .x16, .x17, .x31]) :
    (rec_checkPathStepState state answer).getReg reg = state.getReg reg :=
  PairCap.rec_path_step_preserves state (adjusted state answer) reg preserved

theorem rec_check_path_step_outside (state : MachineState) (answer : Digest)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (rec_checkPathStepState state answer).getMem address = state.getMem address :=
  PairCap.rec_check_path_step_outside state (adjusted state answer) address scratch outside

theorem rec_check_path_step_digest (state : MachineState) (answer : Digest) :
    readBuffer (rec_checkPathStepState state answer) 256 32 = adjusted state answer :=
  PairCap.rec_check_path_step_digest state (adjusted state answer) 

def rec_checkPathLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))
      rec_checkPathLoop (rec_checkPathStepState state answer) count

theorem rec_check_path_loop (state : MachineState) (count : Nat) (bounded : count ≤ 24)
    (pc : 0 < count → state.pc = 4972) (counter : state.getReg .x29 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (pathInstructions (state.getReg .x20) count + fuel) state allowCoins =
      (do let finished ← rec_checkPathLoop state count
          let result ← execute (Trunc.wireImage true) fuel finished allowCoins
          return result.charge (pathInstructions (state.getReg .x20) count + 7 * count) count) := by
  induction count generalizing state with
  | zero => simp [pathInstructions, rec_checkPathLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (rec_checkPathStepState state answer).getReg .x29 = BitVec.ofNat 64 count := by
      rw [(rec_check_path_step_registers state answer).2.2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (rec_checkPathStepState state answer).pc = 4972 := by
      rw [rec_check_path_step_pc state answer]
      have nonzero : state.getReg .x29 - 1 ≠ 0 := by
        rw [← (rec_check_path_step_registers state answer).2.2.1, nextCounter]
        intro zero
        have numeric := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at numeric
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 4 * count) :
        accessValid ((rec_checkPathStepState state answer).getReg .x25 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 4) (by omega)
      rw [(rec_check_path_step_registers state answer).1]
      have address : state.getReg .x25 + 32 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 4)) := by
        rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [pathInstructions, Nat.add_assoc, rec_check_path_step state (pc (by omega)) scratch currentValid]
    simp only [rec_checkPathLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [← (rec_check_path_step_registers state answer).2.1,
      ih _ (by omega) (nextPC answer) (nextCounter answer)
        ((rec_check_path_step_registers state answer).2.2.2.trans scratch) (nextValid answer)]
    simp only [(rec_check_path_step_registers state answer).2.1, bind_assoc, pure_bind]
    have charges (result : Execution) :
        (result.charge (pathInstructions (state.getReg .x20 >>> 1) count + 7 * count) count).charge
          (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + 44) 1 =
        result.charge (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + 37 +
          pathInstructions (state.getReg .x20 >>> 1) count + 7 * (count + 1)) (count + 1) := by
      cases result
      simp only [Execution.charge, Execution.mk.injEq, true_and]
      constructor <;> omega
    simp only [charges]

theorem rec_check_path_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 24)
    (counter : state.getReg .x29 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (rec_checkPathLoop state count)) :
    finished.getReg .x29 = 0 ∧ (0 < count → finished.pc = 5120) := by
  induction count generalizing state with
  | zero =>
    simp only [rec_checkPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, by omega⟩
  | succ count ih =>
    simp only [rec_checkPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have nextCounter : (rec_checkPathStepState state answer).getReg .x29 = BitVec.ofNat 64 count := by
      rw [(rec_check_path_step_registers state answer).2.2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have rest := ih _ (by omega) nextCounter reached
    refine ⟨rest.1, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [rec_checkPathLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [rec_check_path_step_pc state answer, counter]
      rfl
    · exact rest.2 (by omega)

theorem rec_check_path_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (rec_checkPathLoop state count)) :
    finished.getReg .x25 = state.getReg .x25 + BitVec.ofNat 64 (32 * count) ∧
    finished.getReg .x20 = state.getReg .x20 >>> count ∧
    ∀ reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [rec_checkPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [rec_checkPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have rest := ih _ reached
    refine ⟨?_, ?_, ?_⟩
    · rw [rest.1, (rec_check_path_step_registers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · rw [rest.2.1, (rec_check_path_step_registers state answer).2.1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      congr 1
      simp [Nat.pow_succ, Nat.mul_comm]
    · intro reg preserved
      exact (rest.2.2 reg preserved).trans (rec_path_step_preserves state answer reg preserved)

theorem rec_check_path_setup (state : MachineState) (pc : state.pc = 4968)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (1 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (rec_checkPathInitializedState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (Trunc.wireImage true) state = some (.base (.ADDI .x29 .x30 0)) := by
    apply sharedFetch _ 218 _ (by unfold untouched; decide) pc; rfl
  have stepped : ordinaryStep state (.base (.ADDI .x29 .x30 0)) =
      some (rec_checkPathInitializedState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      rec_checkPathInitializedState, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem rec_check_path_subroutine (pathDepth : Nat) (depthBound : pathDepth ≤ 24)
    (state : MachineState) (pc : state.pc = 4968)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4 * pathDepth,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (1 + pathInstructions (state.getReg .x20) pathDepth + fuel)
        state allowCoins =
      (do let finished ← rec_checkPathLoop (rec_checkPathInitializedState state) pathDepth
          let result ← execute (Trunc.wireImage true) fuel finished allowCoins
          return result.charge (1 + pathInstructions (state.getReg .x20) pathDepth + 7 * pathDepth) pathDepth) := by
  have initialPC : (rec_checkPathInitializedState state).pc = 4972 := rfl
  have counter : (rec_checkPathInitializedState state).getReg .x29 = BitVec.ofNat 64 pathDepth :=
    depthReg
  have initialScratch := (rec_check_path_setup_register state .x21 (by decide)).trans scratch
  have initialSource : ∀ word < 4 * pathDepth,
      accessValid ((rec_checkPathInitializedState state).getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [rec_check_path_setup_register state .x25 (by decide)]
    exact sourceValid
  rw [Nat.add_assoc, rec_check_path_setup state pc,
    ← rec_check_path_setup_register state .x20 (by decide),
    rec_check_path_loop _ pathDepth depthBound (fun _ => initialPC) counter initialScratch initialSource]
  simp only [bind_assoc, pure_bind, rec_check_path_setup_register state .x20 (by decide)]
  simp [Execution.charge, Nat.add_assoc]

theorem rec_check_path_loop_outside (oracle : Oracle) (state : MachineState) (count : Nat)
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 8, address ≠ BitVec.ofNat 64 (256+8*i)) :
    (Late.Check.Normal.checkEvaluation oracle (rec_checkPathLoop state count)).1.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => simp [rec_checkPathLoop, Late.Check.Normal.check_evaluation_pure]
  | succ count ih =>
    rw [rec_checkPathLoop, Late.Check.Normal.check_evaluation_public_bind]
    let answer := oracle.compression (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))
    change (Late.Check.Normal.checkEvaluation oracle (rec_checkPathLoop (rec_checkPathStepState state answer) count)).1.getMem address = _
    have nextScratch : (rec_checkPathStepState state answer).getReg .x21 = 256 :=
      (rec_check_path_step_registers state answer).2.2.2.trans scratch
    rw [ih _ nextScratch]
    exact rec_check_path_step_outside state answer address scratch outside
end CommitGolfCandidate.Trunc.Check
