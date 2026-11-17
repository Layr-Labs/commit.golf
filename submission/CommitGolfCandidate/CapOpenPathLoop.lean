import CommitGolfCandidate.CapOpenPathEffect
import CommitGolfCandidate.CapCountedLoop

/-! Bounded execution of the actual lower-path loop. Each iteration checks a
sibling root read and one output digest write. The residual counter and natural
output window prevent wrapping; honest sibling meaning is a separate frame. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

structure CapOpenPathReady (rootBase limit remaining : Nat) (state : MachineState) : Prop where
  roots : state.getReg .x9 = BitVec.ofNat 64 rootBase
  counter : state.getReg .x28 = BitVec.ofNat 64 remaining
  pc : state.pc = if remaining = 0 then 4340 else 4280
  bounded : remaining ≤ 16
  node : ∃ node, node < 33554432 ∧ state.getReg .x20 = BitVec.ofNat 64 node
  cursor : ∃ cursor, state.getReg .x25 = BitVec.ofNat 64 cursor ∧
    cursor % 8 = 0 ∧ cursor + 32*remaining ≤ limit

theorem cap_open_path_ready_next (rootBase limit remaining : Nat) (state : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (ready : CapOpenPathReady rootBase limit (remaining+1) state) :
    CapOpenPathReady rootBase limit remaining (capOpenPathState state) := by
  obtain ⟨node, nodeBound, index⟩ := ready.node
  obtain ⟨cursor, pointer, aligned, space⟩ := ready.cursor
  have bounded := ready.bounded
  have currentPC : state.pc = 4280 := by simpa using ready.pc
  refine ⟨(cap_open_path_register state .x9 (by decide)).trans ready.roots, ?_, ?_,
    by omega, ?_, ?_⟩
  · simpa using cap_open_path_counter state (remaining+1) (by omega) (by omega) ready.counter
  · have done := cap_open_path_exit state (remaining+1) currentPC
      (by omega) (by omega) ready.counter
    simpa using done
  · exact ⟨node/2, by omega,
      cap_open_path_index state node (by omega) index⟩
  · refine ⟨cursor+32, ?_, by omega, by omega⟩
    rw [(cap_open_path_projection state).1, pointer]
    exact (BitVec.ofNat_add cursor 32).symm

theorem cap_open_path_loop_execute (rootBase limit : Nat)
    (rootBound : rootBase + 1073741824 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0) (limitBound : limit ≤ MEMORY_BYTES)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenPathReady rootBase limit remaining state)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (15*remaining+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capCountedRun capOpenPathState remaining state) allowCoins
          return result.charge (15*remaining) 0) := by
  apply cap_counted_run_execute _ 15 capOpenPathState
    (CapOpenPathReady rootBase limit)
    (cap_open_path_ready_next rootBase limit · · limitBound) ?_ remaining state ready fuel allowCoins
  intro residual current currentReady extra coins
  obtain ⟨node, nodeBound, index⟩ := currentReady.node
  obtain ⟨cursor, pointer, aligned, space⟩ := currentReady.cursor
  have sibling : node ^^^ 1 < 33554432 :=
    Nat.xor_lt_two_pow (n := 25) nodeBound (by decide)
  apply cap_open_path_execute current node rootBase cursor
    (by simpa using currentReady.pc) index currentReady.roots pointer
    (by omega) rootAligned (by omega) aligned extra coins

theorem cap_open_path_loop_finished (rootBase limit : Nat)
    (limitBound : limit ≤ MEMORY_BYTES)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenPathReady rootBase limit remaining state) :
    (capCountedRun capOpenPathState remaining state).pc = 4340 ∧
    (capCountedRun capOpenPathState remaining state).getReg .x28 = 0 := by
  have finished := cap_counted_run_ready capOpenPathState
    (CapOpenPathReady rootBase limit)
    (cap_open_path_ready_next rootBase limit · · limitBound) remaining state ready
  exact ⟨by simpa using finished.pc, by simpa using finished.counter⟩

end CommitGolfCandidate
