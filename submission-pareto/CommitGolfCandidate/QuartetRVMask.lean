import CommitGolfCandidate.QuartetRVImage
namespace TwoPermutationPrototype.QuartetRV
open CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1000000

theorem quartet_slot_mask (x : Word) : ((x <<< 7) &&& (3584#12).signExtend 64) = (x >>> 2) <<< 9 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j inside
  interval_cases j <;> simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight] <;>
    first | rfl | exact Bool.and_true _ | exact Bool.and_false _

end TwoPermutationPrototype.QuartetRV
#print axioms TwoPermutationPrototype.QuartetRV.quartet_slot_mask
