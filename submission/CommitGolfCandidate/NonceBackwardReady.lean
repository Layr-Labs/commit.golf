import CommitGolfCandidate.NonceCopyReady

namespace CommitGolfCandidate.NonceBackwardReady
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure Backward (entry : Word) (source target count remaining : Nat)
    (state : MachineState) : Prop where
  remaining_le : remaining ≤ count
  count_bound : count<2^64
  order : source≤target
  source_start : 8≤source
  target_start : 8≤target
  source_window : source+8*count≤MEMORY_BYTES
  target_window : target+8*count≤MEMORY_BYTES
  source_aligned : source%8=0
  target_aligned : target%8=0
  counter : state.getReg .x28=BitVec.ofNat 64 remaining
  pc : state.pc=if remaining=0 then entry+24 else entry
  source : state.getReg .x23=BitVec.ofNat 64 (source+8*remaining-8)
  target : state.getReg .x25=BitVec.ofNat 64 (target+8*remaining-8)

theorem decrement_eight (value : Nat) (positive : 8≤value) :
    BitVec.ofNat 64 value + signExtend12 (4088 : BitVec 12)=BitVec.ofNat 64 (value-8) := by
  rw [show signExtend12 (4088 : BitVec 12)=-(8:Word) by decide]
  have equation : value=value-8+8 := by omega
  conv_lhs => rw [equation]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp

theorem backward_next (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Backward entry source target count (remaining+1) state) :
    Backward entry source target count remaining (NonceWordCopy.copyPrefix true state 6) := by
  refine ⟨by have rem:=ready.remaining_le; omega, ready.count_bound, ready.order,
    ready.source_start, ready.target_start, ready.source_window, ready.target_window,
    ready.source_aligned, ready.target_aligned, ?_, ?_, ?_, ?_⟩
  · rw [NonceWordCopy.iteration_counter, ready.counter,
      NonceWordCopy.decrement (remaining+1) (by omega)]
    simp
  · rw [NonceWordCopy.iteration_pc true state (remaining+1) (by omega)
      (by have bound:=ready.count_bound; have rem:=ready.remaining_le; omega) ready.counter]
    have pc : state.pc=entry := by simpa using ready.pc
    rw [pc]
    by_cases empty : remaining=0
    · simp [empty]
    · simp [empty]
  · rw [NonceWordCopy.iteration_source, ready.source]
    change BitVec.ofNat 64 (source+8*(remaining+1)-8)+signExtend12 (4088:BitVec 12)=_
    rw [decrement_eight _ (by have start:=ready.source_start; omega)]
    congr 1
  · rw [NonceWordCopy.iteration_target, ready.target]
    change BitVec.ofNat 64 (target+8*(remaining+1)-8)+signExtend12 (4088:BitVec 12)=_
    rw [decrement_eight _ (by have start:=ready.target_start; omega)]
    congr 1

theorem backward_source_valid (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Backward entry source target count (remaining+1) state) :
    accessValid (state.getReg .x23) 8=true := by
  have rem:=ready.remaining_le
  have window:=ready.source_window
  have start:=ready.source_start
  have aligned:=ready.source_aligned
  have range : source+8*(remaining+1)-8+8≤MEMORY_BYTES := by omega
  have small : source+8*(remaining+1)-8<2^64 := by
    norm_num [MEMORY_BYTES] at range
    omega
  rw [ready.source]
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨range, by omega⟩

theorem backward_target_valid (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Backward entry source target count (remaining+1) state) :
    accessValid (state.getReg .x25) 8=true := by
  have rem:=ready.remaining_le
  have window:=ready.target_window
  have start:=ready.target_start
  have aligned:=ready.target_aligned
  have range : target+8*(remaining+1)-8+8≤MEMORY_BYTES := by omega
  have small : target+8*(remaining+1)-8<2^64 := by
    norm_num [MEMORY_BYTES] at range
    omega
  rw [ready.target]
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨range, by omega⟩

def Fetched (image : Image) (entry : Word) : Prop :=
  ∀ state index, index<6 → state.pc=entry+BitVec.ofNat 64 (4*index) →
    fetch image state = some (.base (((NonceWordCopy.copyInstructions true)[index]?).getD .EBREAK))

theorem backward_execute (image : Image) (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Backward entry source target count remaining state)
    (fetched : Fetched image entry) (fuel : Nat) (coins : Bool) :
    execute image (6*remaining+fuel) state coins =
      (do let result ← execute image fuel
            (capCountedRun (fun current => NonceWordCopy.copyPrefix true current 6) remaining state) coins
          return result.charge (6*remaining) 0) := by
  refine cap_counted_run_execute image 6
    (fun current => NonceWordCopy.copyPrefix true current 6)
    (Backward entry source target count)
    (fun remaining current => backward_next entry source target count remaining current)
    ?_ remaining state ready fuel coins
  intro remaining current currentReady extra allowCoins
  apply NonceWordCopy.copy_iteration_execute image true current extra allowCoins
  · intro index bounded
    apply fetched _ index bounded
    rw [NonceWordCopy.prefix_pc true current index (by omega)]
    have pc : current.pc=entry := by simpa using currentReady.pc
    rw [pc]
  · exact backward_source_valid entry source target count remaining current currentReady
  · exact backward_target_valid entry source target count remaining current currentReady

theorem backward_finished (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Backward entry source target count remaining state) :
    let final := capCountedRun (fun current => NonceWordCopy.copyPrefix true current 6) remaining state
    final.pc=entry+24 ∧ final.getReg .x28=0 ∧
      final.getReg .x23=BitVec.ofNat 64 (source-8) ∧
      final.getReg .x25=BitVec.ofNat 64 (target-8) := by
  have final := cap_counted_run_ready
    (fun current => NonceWordCopy.copyPrefix true current 6)
    (Backward entry source target count)
    (fun remaining current => backward_next entry source target count remaining current)
    remaining state ready
  exact ⟨by simpa using final.pc, by simpa using final.counter,
    by simpa using final.source, by simpa using final.target⟩

end CommitGolfCandidate.NonceBackwardReady
