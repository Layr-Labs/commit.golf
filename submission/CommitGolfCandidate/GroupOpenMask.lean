import CommitGolfCandidate.GroupOpenImage
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1000000

theorem quartet_slot_mask (x : Word) : ((x <<< 8) &&& (3072#12).signExtend 64) = (x >>> 2) <<< 10 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j inside
  interval_cases j <;> simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight] <;>
    first | rfl | exact Bool.and_true _ | exact Bool.and_false _

end TwoPermutationPrototype.GroupedOpening
#print axioms TwoPermutationPrototype.GroupedOpening.quartet_slot_mask
