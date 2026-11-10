import CommitGolfCandidate.FastOpeningPrefix
import CommitGolfCandidate.FastOpeningBounds
import CommitGolfCandidate.FastOpeningEnds

/-! A complete position uses the same nonce and authentication-path records as the
reference opening. Removing its twenty-four path branches saves twenty-four cycles. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem fast_path_count_register (s : MachineState) :
    (openingPathState s).getReg .x27=s.getReg .x27 := by
  have prepared (s : MachineState) : openingPathPreparedState s=
      ([.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7] : List Instr).foldl execInstrBr s := rfl
  simp [openingPathState,openingLatchState,openingPathAdvancedState,
    opening_copy_register,prepared,execInstrBr,MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

theorem fast_path_loop_count_register (iterations : Nat) (s : MachineState) :
    (openingPathState^[iterations] s).getReg .x27=s.getReg .x27 := by
  induction iterations with
  | zero => rfl
  | succ iterations ih => rw [Function.iterate_succ_apply',fast_path_count_register,ih]

theorem fast_position_pc (s : MachineState) :
    (openingPositionState s).pc=(if s.getReg .x27-1=0 then 4320 else 4176) := by
  change (if (openingPathState^[24] (openingPositionPathState s)).getReg .x27-1=0
    then 4320 else 4176)=_
  rw [fast_path_loop_count_register,
    opening_position_path_register s .x27 (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem fast_position_next_state (s : MachineState) :
    fastNextState (openingPathState^[24] (openingPositionPathState s))=
      (openingPositionState s).setPC (if s.getReg .x27-1=0 then 5604 else 4176) := by
  unfold fastNextState
  rw [fast_path_loop_count_register,
    opening_position_path_register s .x27 (by decide) (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- Exact execution of one nonce and full path, followed by the actual outer latch. -/
theorem fast_position (s : MachineState) (pc : s.pc=4176)
    (indexValid : accessValid (s.getReg .x24) 8=true)
    (indexBound : (s.getMem (s.getReg .x24)).toNat<2^24)
    (leaves : s.getReg .x19=16777216)
    (saltBound : (s.getReg .x18).toNat+2^29≤MEMORY_BYTES)
    (saltAligned : (s.getReg .x18).toNat%8=0)
    (heapBound : (s.getReg .x9).toNat+2^30≤MEMORY_BYTES)
    (heapAligned : (s.getReg .x9).toNat%8=0)
    (outputBound : (s.getReg .x25).toNat+800≤MEMORY_BYTES)
    (outputAligned : (s.getReg .x25).toNat%8=0)
    (fuel : Nat) (coins : Bool) :
    execute fastImage (355+fuel) s coins=
      (do let result ← execute fastImage fuel
            ((openingPositionState s).setPC (if s.getReg .x27-1=0 then 5604 else 4176)) coins
          return result.charge 355 0) := by
  let path := openingPositionPathState s
  have pathPC : path.pc=4248 := fast_position_path_pc s pc
  have pathHeap : path.getReg .x9=s.getReg .x9 :=
    opening_position_path_register s .x9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have pathNode : (path.getReg .x20).toNat<2^25 := by
    rw [(opening_position_path_registers s).2.1,leaves,BitVec.toNat_add]
    change ((s.getMem (s.getReg .x24)).toNat+16777216)%2^64<2^25
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have outputNat : (path.getReg .x25).toNat=(s.getReg .x25).toNat+32 := by
    rw [(opening_position_path_registers s).1,BitVec.toNat_add]
    change ((s.getReg .x25).toNat+32)%2^64=_
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at outputBound
    omega
  have pathOutput : (path.getReg .x25).toNat+32*24≤MEMORY_BYTES := by rw [outputNat];omega
  have pathAligned : (path.getReg .x25).toNat%8=0 := by rw [outputNat];omega
  have reads := opening_salt_access (s.getReg .x18) (s.getMem (s.getReg .x24))
    saltBound saltAligned indexBound
  have writes := opening_digest_access_valid (s.getReg .x25) (by omega) outputAligned
  rw [show 355+fuel=16+(336+(3+fuel)) by omega,
    fast_position_setup s pc indexValid reads writes,
    fast_full_path path pathPC (by simpa only [pathHeap] using heapBound)
      (by simpa only [pathHeap] using heapAligned) pathNode pathOutput pathAligned,
    fast_next _ rfl,fast_next_frame,fast_position_next_state]
  simp [Execution.charge,←Nat.add_assoc]
end CommitGolfCandidate
