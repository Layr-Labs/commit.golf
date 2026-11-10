import CommitGolfCandidate.Group341Schedule
import CommitGolfCandidate.ParentGroupTree

/-! Specialize the generic schedule to 15 initial parents and 341-parent groups. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute commitBody

theorem group341_body (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (latchFetched : ContiguousLatchFetched (submission.image .commit))
    (entryFetched : ContiguousEntryFetched (submission.image .commit))
    (exitFetched : ContiguousExitFetched (submission.image .commit))
    (parentFetched : group341Schedule.Fetched (submission.image .commit))
    (state : MachineState) (count groups : Nat) (messageBase : Word)
    (countEq : count=341*groups+16) (positive : 0<groups) (bounded : count≤2^24)
    (leaves : CommitLeavesInvariant state count)
    (heapWindow : (state.getReg .x23).toNat+32*count=(state.getReg .x22).toNat)
    (total : state.getReg .x19=BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count-1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9+BitVec.ofNat 64 (32+8*word.val)) 8=true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) :
    execute (submission.image .commit) (35*count+1024*groups+70+fuel)
      (cursorLeafFrame state messageBase) true=
      (do let finished ← commitBody state count
          return ⟨.success,cursorBaseFrame finished messageBase,
            91*count+3411*groups+175,9*count-1⟩) := by
  have scheduleCount : count=group341Schedule.parents groups+1 := by
    rw [group341_schedule_parents]
    omega
  have run := parent_schedule_body group341Schedule group341_schedule_valid group341_schedule_entry
    saltFetched prefixFetched tailFetched latchFetched entryFetched exitFetched parentFetched
    state count groups messageBase scheduleCount bounded positive leaves heapWindow total parents
    rootValid outputValid fuel
  simpa only [group341_schedule_instructions,group341_schedule_cycles,Nat.add_assoc,show (50:Nat)+20=70 by decide,show (155:Nat)+20=175 by decide] using run

end CommitGolfCandidate
