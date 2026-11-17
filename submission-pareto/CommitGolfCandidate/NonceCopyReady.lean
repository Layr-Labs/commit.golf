import CommitGolfCandidate.CapCountedLoop
import CommitGolfCandidate.NonceWordCopy

/-! Scratch readiness interface for a future forward in-place word copy.
No concrete compactor image or machine certificate is supplied here. -/
namespace CommitGolfCandidate.NonceCopyReady
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure Forward (entry : Word) (source target count remaining : Nat)
    (state : MachineState) : Prop where
  remaining_le : remaining ≤ count
  count_bound : count < 2^64
  source_le : target ≤ source
  source_window : source+8*count ≤ MEMORY_BYTES
  target_window : target+8*count ≤ MEMORY_BYTES
  source_aligned : source%8=0
  target_aligned : target%8=0
  counter : state.getReg .x28 = BitVec.ofNat 64 remaining
  pc : state.pc = if remaining=0 then entry+24 else entry
  source : state.getReg .x23 = BitVec.ofNat 64 (source+8*(count-remaining))
  target : state.getReg .x25 = BitVec.ofNat 64 (target+8*(count-remaining))

theorem forward_next (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Forward entry source target count (remaining+1) state) :
    Forward entry source target count remaining (NonceWordCopy.copyPrefix false state 6) := by
  refine ⟨by have rem := ready.remaining_le; omega, ready.count_bound, ready.source_le, ready.source_window,
    ready.target_window, ready.source_aligned, ready.target_aligned, ?_, ?_, ?_, ?_⟩
  · rw [NonceWordCopy.iteration_counter, ready.counter,
      NonceWordCopy.decrement (remaining+1) (by omega)]
    simp
  · rw [NonceWordCopy.iteration_pc false state (remaining+1) (by omega)
      (by have bound:=ready.count_bound; have rem:=ready.remaining_le; omega) ready.counter]
    have pc : state.pc=entry := by simpa using ready.pc
    rw [pc]
    by_cases empty : remaining=0
    · simp [empty]
    · simp [empty]
  · rw [NonceWordCopy.iteration_source, ready.source]
    have offset : signExtend12 (if false then 4088 else 8)=(8:Word) := by decide
    rw [offset]
    change BitVec.ofNat 64 (source+8*(count-(remaining+1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    have rem:=ready.remaining_le
    omega
  · rw [NonceWordCopy.iteration_target, ready.target]
    have offset : signExtend12 (if false then 4088 else 8)=(8:Word) := by decide
    rw [offset]
    change BitVec.ofNat 64 (target+8*(count-(remaining+1))) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    have rem:=ready.remaining_le
    omega

theorem forward_source_valid (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Forward entry source target count (remaining+1) state) :
    accessValid (state.getReg .x23) 8=true := by
  have rem := ready.remaining_le
  have window := ready.source_window
  have aligned := ready.source_aligned
  have range : source+8*(count-(remaining+1))+8 ≤ MEMORY_BYTES := by omega
  have small : source+8*(count-(remaining+1)) < 2^64 := by
    norm_num [MEMORY_BYTES] at range
    omega
  rw [ready.source]
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨range, by omega⟩

theorem forward_target_valid (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Forward entry source target count (remaining+1) state) :
    accessValid (state.getReg .x25) 8=true := by
  have rem := ready.remaining_le
  have window := ready.target_window
  have aligned := ready.target_aligned
  have range : target+8*(count-(remaining+1))+8 ≤ MEMORY_BYTES := by omega
  have small : target+8*(count-(remaining+1)) < 2^64 := by
    norm_num [MEMORY_BYTES] at range
    omega
  rw [ready.target]
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨range, by omega⟩

def Fetched (image : Image) (entry : Word) : Prop :=
  ∀ state index, index<6 → state.pc=entry+BitVec.ofNat 64 (4*index) →
    fetch image state = some (.base (((NonceWordCopy.copyInstructions false)[index]?).getD .EBREAK))

theorem forward_execute (image : Image) (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Forward entry source target count remaining state)
    (fetched : Fetched image entry) (fuel : Nat) (coins : Bool) :
    execute image (6*remaining+fuel) state coins =
      (do let result ← execute image fuel
            (capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) remaining state) coins
          return result.charge (6*remaining) 0) := by
  refine cap_counted_run_execute image 6
    (fun current => NonceWordCopy.copyPrefix false current 6)
    (Forward entry source target count)
    (fun remaining current => forward_next entry source target count remaining current)
    ?_ remaining state ready fuel coins
  intro remaining current currentReady extra allowCoins
  apply NonceWordCopy.copy_iteration_execute image false current extra allowCoins
  · intro index bounded
    apply fetched _ index bounded
    rw [NonceWordCopy.prefix_pc false current index (by omega)]
    have pc : current.pc=entry := by simpa using currentReady.pc
    rw [pc]
  · exact forward_source_valid entry source target count remaining current currentReady
  · exact forward_target_valid entry source target count remaining current currentReady

theorem forward_finished (entry : Word) (source target count remaining : Nat)
    (state : MachineState) (ready : Forward entry source target count remaining state) :
    let final := capCountedRun (fun current => NonceWordCopy.copyPrefix false current 6) remaining state
    final.pc=entry+24 ∧ final.getReg .x28=0 ∧
      final.getReg .x23=BitVec.ofNat 64 (source+8*count) ∧
      final.getReg .x25=BitVec.ofNat 64 (target+8*count) := by
  have final := cap_counted_run_ready
    (fun current => NonceWordCopy.copyPrefix false current 6)
    (Forward entry source target count)
    (fun remaining current => forward_next entry source target count remaining current)
    remaining state ready
  exact ⟨by simpa using final.pc, by simpa using final.counter,
    by simpa using final.source, by simpa using final.target⟩

end CommitGolfCandidate.NonceCopyReady
