import CommitGolfCandidate.Compact.NoJumpImage
import CommitGolfCandidate.Compact.SlimFrames
/-! Compose the thirteen-instruction path bodies from physical PC 4232, retaining the reference states and zero-counter invariant. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem noJump_path_loop (count first : Nat) (bounded : first+count≤24)
    (state : MachineState) (counter : Word)
    (reads : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] state).getReg .x9+
       (((openingPathState^[level] state).getReg .x20 ^^^ 1)<<<5)+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (writes : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] state).getReg .x25+
       BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute noJumpImage (13*count+fuel)
      (((openingPathState^[first] state).setReg .x28 counter).setPC
        (BitVec.ofNat 64 (4232+52*first))) coins=
      (do let result ← execute noJumpImage fuel
            (((openingPathState^[first+count] state).setReg .x28 counter).setPC
              (BitVec.ofNat 64 (4232+52*(first+count)))) coins
          return result.charge (13*count) 0) := by
  induction count generalizing first with
  | zero => simp [Execution.charge]
  | succ count ih =>
    have nextPC : BitVec.ofNat 64 (4232+52*first)+52=
        BitVec.ofNat 64 (4232+52*(first+1)) := by
      change BitVec.ofNat 64 (4232+52*first)+BitVec.ofNat 64 52=_
      rw [←BitVec.ofNat_add]
      congr 1 <;> omega
    have run := slim_path_execute noJumpImage _ (noJump_path_fetched first (by omega))
      (((openingPathState^[first] state).setReg .x28 counter).setPC
        (BitVec.ofNat 64 (4232+52*first))) rfl
      (by intro word; simpa [MachineState.getReg,MachineState.setReg,MachineState.setPC] using reads first (by omega) word)
      (by intro word; simpa [MachineState.getReg,MachineState.setReg,MachineState.setPC] using writes first (by omega) word)
      (13*count+fuel) coins
    simp only [path_frame_erasure,MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x28≠.x0)] at run
    rw [path_counter_frame] at run
    change execute noJumpImage (13+(13*count+fuel)) _ coins=
      (do let result ← execute noJumpImage (13*count+fuel)
            (((openingPathState (openingPathState^[first] state)).setReg .x28 counter).setPC
              (BitVec.ofNat 64 (4232+52*first)+52)) coins
          return result.charge 13 0) at run
    rw [nextPC,←Function.iterate_succ_apply' openingPathState first state] at run
    rw [show 13*(count+1)+fuel=13+(13*count+fuel) by omega,run,
      ih (first+1) (by omega)]
    simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add]
end CommitGolfCandidate.Compact
