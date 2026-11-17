import CommitGolfCandidate.FastOpeningImage
import CommitGolfCandidate.FastOpeningFrames
/-! Compose the checked path steps along all twenty-four physical body locations.
Fuel and charged cycles are accounted separately from memory refinement. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem fast_path_loop (count first : Nat) (bounded : first+count≤24)
    (state : MachineState)
    (reads : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] state).getReg .x9+
       (((openingPathState^[level] state).getReg .x20 ^^^ 1)<<<5)+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (writes : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] state).getReg .x25+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (14*count+fuel)
      ((openingPathState^[first] state).setPC (BitVec.ofNat 64 (4248+56*first))) coins=
      (do let result ← execute fastImage fuel
            ((openingPathState^[first+count] state).setPC
              (BitVec.ofNat 64 (4248+56*(first+count)))) coins
          return result.charge (14*count) 0) := by
  induction count generalizing first with
  | zero => simp [Execution.charge]
  | succ count ih =>
    have nextPC : BitVec.ofNat 64 (4248+56*first)+56=
        BitVec.ofNat 64 (4248+56*(first+1)) := by
      change BitVec.ofNat 64 (4248+56*first)+BitVec.ofNat 64 56=_
      rw [←BitVec.ofNat_add]
      congr 1 <;> omega
    have run := unrolled_path_execute fastImage _ (fast_path_fetched first (by omega))
      ((openingPathState^[first] state).setPC (BitVec.ofNat 64 (4248+56*first))) rfl
      (by simpa only [MachineState.getReg_setPC] using reads first (by omega))
      (by simpa only [MachineState.getReg_setPC] using writes first (by omega))
      (14*count+fuel) coins
    rw [path_frame_erasure] at run
    change execute fastImage (14+(14*count+fuel)) _ coins=
      (do let result ← execute fastImage (14*count+fuel)
            ((openingPathState (openingPathState^[first] state)).setPC
              (BitVec.ofNat 64 (4248+56*first)+56)) coins
          return result.charge 14 0) at run
    rw [nextPC,←Function.iterate_succ_apply' openingPathState first state] at run
    rw [show 14*(count+1)+fuel=14+(14*count+fuel) by omega,run,
      ih (first+1) (by omega)]
    simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add]
end CommitGolfCandidate
