import CommitGolfCandidate.CapOpenRecordStart
import CommitGolfCandidate.CapOpenPathFrame
import CommitGolfCandidate.CapOpenGroupControl

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenRecordGroupState (state : MachineState) : MachineState :=
  capCountedRun capOpenPathState 16 (capOpenRecordPathState state)

def capOpenRecordState (state : MachineState) : MachineState :=
  capOpenGroupPrefix (capOpenRecordGroupState state) 6

attribute [local irreducible] capOpenRecordGroupState capOpenRecordState

theorem cap_open_record_group_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28) :
    (capOpenRecordGroupState state).getReg reg = state.getReg reg := by
  rw [capOpenRecordGroupState]
  exact (cap_open_path_loop_register 16 _ reg outside).trans
    (cap_open_record_path_register state reg
      ⟨outside.1, outside.2.2.2.2.1, outside.2.2.1,
        outside.2.2.2.1, outside.2.2.2.2.2⟩)

theorem cap_open_record_group_index (state : MachineState) (position : Nat)
    (bounded : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216) :
    (capOpenRecordGroupState state).getReg .x20 =
      BitVec.ofNat 64 (256+position/65536) := by
  rw [capOpenRecordGroupState, cap_open_path_loop_index 16 _
    (16777216+position) (by omega)
      (cap_open_record_path_index state position loaded leaves)]
  have division : (16777216+position)/2^16 = 256+position/65536 := by
    norm_num
    omega
  rw [division]

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_open_record_execute (state : MachineState)
    (position rootBase saltBase cursor limit : Nat)
    (pc : state.pc = 4212)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (positionBound : position < 16777216)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (rootAligned : rootBase % 8 = 0)
    (rootBound : rootBase+1073741824 ≤ MEMORY_BYTES)
    (salts : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (saltAligned : saltBase % 8 = 0)
    (saltBound : saltBase+24*position+32 ≤ MEMORY_BYTES)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (cursorAligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES)
    (leaves : state.getReg .x19 = 16777216)
    (marks : state.getReg .x22 = 28672)
    (stride : state.getReg .x17 = 24)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (263+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordState state) allowCoins
          return result.charge 266 0) := by
  have ready := cap_open_record_path_ready rootBase limit cursor position state
    pc roots pointer cursorAligned space positionBound loaded leaves
  have pathRun := cap_open_path_loop_execute rootBase limit rootBound rootAligned
    limitBound 16 (capOpenRecordPathState state) ready (6+fuel) allowCoins
  have groupPC : (capOpenRecordGroupState state).pc = 4340 := by
    rw [capOpenRecordGroupState]
    exact (cap_open_path_loop_finished rootBase limit limitBound 16 _ ready).1
  have groupMark : (capOpenRecordGroupState state).getReg .x22 = 28672 :=
    (cap_open_record_group_register state .x22 (by decide)).trans marks
  have groupIndex := cap_open_record_group_index state position positionBound loaded leaves
  have groupRun := cap_open_group_execute (capOpenRecordGroupState state)
    (256+position/65536) groupPC groupMark groupIndex (by omega) fuel allowCoins
  rw [show 263+fuel = 17+(15*16+(6+fuel)) by omega,
    cap_open_record_start_execute state position saltBase cursor pc indexValid loaded
      salts pointer saltAligned saltBound cursorAligned (by omega) stride,
    pathRun]
  rw [← capOpenRecordGroupState, groupRun, ← capOpenRecordState]
  simp only [bind_assoc, pure_bind, charge_pair, Nat.reduceAdd]

end CommitGolfCandidate
