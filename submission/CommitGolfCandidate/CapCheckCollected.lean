import CommitGolfCandidate.CapCheckInitialFacts
import CommitGolfCandidate.CapConsistency
import CommitGolfCandidate.CapMarkInvariant

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckRootAddress (group : Nat) : Nat :=
  12288+32*(256+group)

structure CapCheckCollected (state : MachineState) (roots : CapRootMap) : Prop where
  marks : ∀ group < 256,
    state.getMem (capMarkAddress (256+group)) =
      if (roots group).isSome then 1 else 0
  roots : ∀ group < 256, ∀ value, roots group = some value →
    readBuffer state (capCheckRootAddress group) 32 = value

theorem cap_check_collected_initial (input : CheckInput) :
    CapCheckCollected
      (capCheckRecordEntry (capCheckLengthState (capProgram.initialState .check input)))
      (fun _ => none) := by
  constructor
  · intro group bounded
    exact cap_check_initial_workspace_zero input (28672+8*(256+group)) (by omega)
  · intro group bounded value impossible
    contradiction

theorem cap_check_collected_memory (left right : MachineState) (roots : CapRootMap)
    (same : left.mem = right.mem) (ready : CapCheckCollected right roots) :
    CapCheckCollected left roots := by
  constructor
  · intro group bounded
    exact (congrFun same (capMarkAddress (256+group))).trans (ready.marks group bounded)
  · intro group bounded value known
    exact (read_buffer_memory_congr left right same _ 32).trans
      (ready.roots group bounded value known)

theorem cap_check_collected_mark_zero (state : MachineState) (roots : CapRootMap)
    (ready : CapCheckCollected state roots) (group : Nat) (bounded : group < 256) :
    state.getMem (capMarkAddress (256+group)) = 0 ↔ roots group = none := by
  rw [ready.marks group bounded]
  cases h : roots group <;> simp [h]

theorem cap_check_collected_mark_one (state : MachineState) (roots : CapRootMap)
    (ready : CapCheckCollected state roots) (group : Nat) (bounded : group < 256)
    (value : Digest) (known : roots group = some value) :
    state.getMem (capMarkAddress (256+group)) = 1 := by
  rw [ready.marks group bounded,known]
  rfl

end CommitGolfCandidate
