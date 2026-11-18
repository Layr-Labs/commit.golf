import CommitGolfCandidate.CapCheckPathEffect

/-! Lower siblings are consumed by the actual parity-dependent path loop.
Instruction totals follow the index bits; cycles add seven per paid
compression. The sibling-load admission is transported for every reply. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capCheckPathLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | remaining+1 => do
      let answer ← capCheckScratchQuery (readBuffer (capCheckPathPreparedState state) 256 64)
      capCheckPathLoop (capCheckPathBlockState state answer) remaining

def capCheckPathLoopSteps (index : Word) : Nat → Nat
  | 0 => 0
  | remaining+1 =>
      capCheckPathPreparationSteps index + 13 + capCheckPathLoopSteps (index >>> 1) remaining

theorem cap_check_path_loop_steps_bound (index : Word) (count : Nat) :
    capCheckPathLoopSteps index count ≤ 32*count := by
  induction count generalizing index with
  | zero => simp [capCheckPathLoopSteps]
  | succ count ih =>
    have tail := ih (index >>> 1)
    unfold capCheckPathLoopSteps
    unfold capCheckPathPreparationSteps
    split <;> omega

theorem cap_check_path_loop_execute (state : MachineState) (count : Nat)
    (bounded : count ≤ 17)
    (pc : 0 < count → state.pc = 4272)
    (counter : state.getReg .x29 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4*count,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check)
      (capCheckPathLoopSteps (state.getReg .x20) count+fuel) state allowCoins =
      (do let finished ← capCheckPathLoop state count
          let result ← execute ((capExperimental 24).image .check) fuel finished allowCoins
          return result.charge (capCheckPathLoopSteps (state.getReg .x20) count+7*count) count) := by
  induction count generalizing state with
  | zero => simp [capCheckPathLoop, capCheckPathLoopSteps, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (capCheckPathBlockState state answer).getReg .x29 = BitVec.ofNat 64 count := by
      simpa only [Nat.add_sub_cancel] using
        cap_check_path_block_counter state answer (count+1) (by omega) counter
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (capCheckPathBlockState state answer).pc = 4272 := by
      rw [cap_check_path_block_exit state answer (count+1) (by omega) bounded counter]
      exact if_neg (by omega)
    have nextScratch (answer : BitVec 256) :
        (capCheckPathBlockState state answer).getReg .x21 = 256 :=
      (cap_check_path_block_register state answer .x21 (by decide)).trans scratch
    have nextValid (answer : BitVec 256) (word : Nat) (inside : word < 4*count) :
        accessValid ((capCheckPathBlockState state answer).getReg .x25 +
          BitVec.ofNat 64 (8*word)) 8 = true := by
      have valid := sourceValid (word+4) (by omega)
      rw [(cap_check_path_block_projection state answer).1]
      have address : state.getReg .x25+32+BitVec.ofNat 64 (8*word) =
          state.getReg .x25+BitVec.ofNat 64 (8*(word+4)) := by
        rw [show 8*(word+4)=32+8*word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [capCheckPathLoopSteps,
      show capCheckPathPreparationSteps (state.getReg .x20)+13+
        capCheckPathLoopSteps (state.getReg .x20 >>> 1) count+fuel =
        capCheckPathBlockSteps state+
          (capCheckPathLoopSteps (state.getReg .x20 >>> 1) count+fuel) by
          unfold capCheckPathBlockSteps; omega,
      cap_check_path_block_execute state (pc (by omega)) scratch currentValid]
    simp only [capCheckPathLoop, bind_assoc]
    apply congrArg (fun continuation =>
      capCheckScratchQuery (readBuffer (capCheckPathPreparedState state) 256 64) >>= continuation)
    funext answer
    rw [← (cap_check_path_block_projection state answer).2.1,
      ih _ (by omega) (nextPC answer) (nextCounter answer) (nextScratch answer) (nextValid answer)]
    simp only [bind_assoc, pure_bind]
    simp [Execution.charge, capCheckPathBlockSteps,
      (cap_check_path_block_projection state answer).2.1,
      Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end CommitGolfCandidate
