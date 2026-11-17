import CommitGolfCandidate.Compact.FixedStep
import CommitGolfCandidate.Compact.FixedFrames
/-! Iterate fixed-base path steps while keeping the reference cursor virtual. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem fixed_path_loop (count first : Nat) (bounded : first+count≤24)
    (state : MachineState) (counter : Word)
    (reads : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] state).getReg .x9+
       (((openingPathState^[level] state).getReg .x20 ^^^ 1)<<<5)+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (writes : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] state).getReg .x25+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute fixedImage (12*count+fuel)
      (fixedFrame (openingPathState^[first] state) (state.getReg .x25) counter
        (BitVec.ofNat 64 (4232+48*first))) coins=
      (do let result ← execute fixedImage fuel
            (fixedFrame (openingPathState^[first+count] state) (state.getReg .x25) counter
              (BitVec.ofNat 64 (4232+48*(first+count)))) coins
          return result.charge (12*count) 0) := by
  induction count generalizing first with
  | zero => simp [Execution.charge]
  | succ count ih =>
    have nextPC : BitVec.ofNat 64 (4232+48*first)+48=
        BitVec.ofNat 64 (4232+48*(first+1)) := by
      change BitVec.ofNat 64 (4232+48*first)+BitVec.ofNat 64 48=_
      rw [←BitVec.ofNat_add]
      congr 1 <;> omega
    have cursor := opening_path_output first state
    have run := fixed_step_execute first (by omega)
      (fixedFrame (openingPathState^[first] state) (state.getReg .x25) counter
        (BitVec.ofNat 64 (4232+48*first))) rfl
      (by intro word; simpa [fixedFrame,MachineState.getReg,MachineState.setReg,MachineState.setPC]
          using reads first (by omega) word)
      (by
        intro word
        have write := writes first (by omega) word
        rw [cursor] at write
        simpa [fixedFrame,MachineState.getReg,MachineState.setReg,MachineState.setPC] using write)
      (12*count+fuel) coins
    rw [fixed_path_refine _ first (by omega) _ _ _ cursor,nextPC,
      ←Function.iterate_succ_apply' openingPathState first state] at run
    rw [show 12*(count+1)+fuel=12+(12*count+fuel) by omega,run,
      ih (first+1) (by omega)]
    simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add]
end CommitGolfCandidate.Compact
