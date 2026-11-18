import CommitGolfCandidate.TwoPermutationCheckerBodyFacts
import CommitGolfCandidate.TwoPermutationCheckerCapSuffix

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

theorem checker_cap_facts (oracle : Oracle) (input : CheckInput) (nonempty : input.positions.card ≠ 0)
    (state : MachineState) (rows : List PublicRow) (fuel : Nat) (enough : 14840 ≤ fuel)
    (cursor : RecordCursor input input.positions.card state) (framed : RecordInputFrame input input.positions.card state)
    (table : CollectedTable oracle input input.positions.card state rows) :
    CheckerCapFacts oracle input state fuel := by
  let groups := Opening.groupsBefore input.positions input.positions.card
  let pointer := checkNonceWord input.positions.card
  obtain ⟨above, room⟩ := checker_cap_memory_room input
  have ready : CapSuffixReady groups state pointer 536871424 := by
    refine ⟨?_,cursor.proof,cursor.capRoots,cursor.marks,cursor.capCount,cursor.selector,cursor.commitment,
      checker_cap_marks oracle input state rows table,above,room,by decide,by decide⟩
    rw [cursor.pc,ite_eq_left rfl]
  have finished := execute_cap_suffix oracle groups state pointer 536871424 fuel ready enough
  refine ⟨finished.terminates, ?_, finished.paths, ?_⟩
  · have calls := finished.honestCalls
    change (checkEvaluation oracle (recordRows (execute checkerImage fuel state false))).2 ≤ 8*groups.length at calls
    rw [show groups.length = input.positions.card from record_groups_length input _ (by omega)] at calls
    exact calls
  · intro message salts canonical
    obtain ⟨proof, root, endPointer⟩ :=
      checker_honest_cap_data oracle input state rows table framed cursor nonempty message salts canonical
    exact finished.honest _ (checker_honest_cap_heap oracle message salts) proof root endPointer

end TwoPermutationPrototype.Checker
