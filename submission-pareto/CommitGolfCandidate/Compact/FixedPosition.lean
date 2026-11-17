import CommitGolfCandidate.Compact.FixedPrefix
import CommitGolfCandidate.Compact.FixedBounds
import CommitGolfCandidate.Compact.FixedEnds

/-! A position uses fourteen prefix instructions, 289 path instructions and three latch instructions, for 306 cycles. The zero-counter invariant is preserved. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem fixed_path_count_register (s : MachineState) :
    (openingPathState s).getReg .x27=s.getReg .x27 := by
  have prepared (s : MachineState) : openingPathPreparedState s=
      ([.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7] : List Instr).foldl execInstrBr s := rfl
  simp [openingPathState,openingLatchState,openingPathAdvancedState,
    opening_copy_register,prepared,execInstrBr,MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

theorem fixed_path_loop_count_register (iterations : Nat) (s : MachineState) :
    (openingPathState^[iterations] s).getReg .x27=s.getReg .x27 := by
  induction iterations with
  | zero => rfl
  | succ iterations ih => rw [Function.iterate_succ_apply',fixed_path_count_register,ih]

theorem fixed_position_pc (s : MachineState) :
    (openingPositionState s).pc=(if s.getReg .x27-1=0 then 4320 else 4176) := by
  change (if (openingPathState^[24] (openingPositionPathState s)).getReg .x27-1=0
    then 4320 else 4176)=_
  rw [fixed_path_loop_count_register,
    opening_position_path_register s .x27 (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem fixed_position_next_state (s : MachineState) :
    fixedNextState (openingPathState^[24] (openingPositionPathState s))=
      (openingPositionState s).setPC (if s.getReg .x27-1=0 then 5400 else 4176) := by
  unfold fixedNextState
  rw [fixed_path_loop_count_register,
    opening_position_path_register s .x27 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl

theorem fixed_position_counter (s : MachineState) :
    (openingPositionState s).getReg .x28=0 := by
  change (openingNextState (openingPathState^[24] (openingPositionPathState s))).getReg .x28=0
  have frame (s : MachineState) : (openingNextState s).getReg .x28=s.getReg .x28 := by
    simp [openingNextState,MachineState.getReg_setPC,MachineState.getReg_setReg_ne]
  rw [frame,path_counter_iterate,(opening_position_path_registers s).2.2]
  decide

/-- Exact execution of one nonce and full path, followed by the actual outer latch. -/
theorem fixed_position (s : MachineState) (pc : s.pc=4176)
    (counterZero : s.getReg .x28=0)
    (indexValid : accessValid (s.getReg .x24) 8=true)
    (indexBound : (s.getMem (s.getReg .x24)).toNat<2^24)
    (leaves : s.getReg .x19=16777216)
    (saltBound : (s.getReg .x18).toNat+2^29≤MEMORY_BYTES)
    (saltAligned : (s.getReg .x18).toNat%8=0)
    (heapBound : (s.getReg .x9).toNat+2^30≤MEMORY_BYTES)
    (heapAligned : (s.getReg .x9).toNat%8=0)
    (outputBound : (s.getReg .x25).toNat+792≤MEMORY_BYTES)
    (outputAligned : (s.getReg .x25).toNat%8=0)
    (fuel : Nat) (coins : Bool) :
    execute fixedImage (306+fuel) s coins=
      (do let result ← execute fixedImage fuel
            ((openingPositionState s).setPC (if s.getReg .x27-1=0 then 5400 else 4176)) coins
          return result.charge 306 0) := by
  let path := openingPositionPathState s
  have pathCounter : path.getReg .x28=24 := (opening_position_path_registers s).2.2
  have pathHeap : path.getReg .x9=s.getReg .x9 :=
    opening_position_path_register s .x9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have pathNode : (path.getReg .x20).toNat<2^25 := by
    rw [(opening_position_path_registers s).2.1,leaves,BitVec.toNat_add]
    change ((s.getMem (s.getReg .x24)).toNat+16777216)%2^64<2^25
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have outputNat : (path.getReg .x25).toNat=(s.getReg .x25).toNat+24 := by
    rw [(opening_position_path_registers s).1,BitVec.toNat_add]
    change ((s.getReg .x25).toNat+24)%2^64=_
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at outputBound
    omega
  have pathOutput : (path.getReg .x25).toNat+32*24≤MEMORY_BYTES := by rw [outputNat];omega
  have pathAligned : (path.getReg .x25).toNat%8=0 := by rw [outputNat];omega
  have reads := opening_salt_access (s.getReg .x18) (s.getMem (s.getReg .x24))
    saltBound saltAligned indexBound
  have writes := opening_digest_access_valid (s.getReg .x25) (by omega) outputAligned
  rw [show 306+fuel=14+(289+(3+fuel)) by omega,
    fixed_position_setup s pc counterZero indexValid reads writes,
    fixed_full_path path pathCounter (by simpa only [pathHeap] using heapBound)
      (by simpa only [pathHeap] using heapAligned) pathNode pathOutput pathAligned,
    fixed_next _ rfl,fixed_next_frame,fixed_position_next_state]
  simp [Execution.charge,←Nat.add_assoc]
end CommitGolfCandidate.Compact
