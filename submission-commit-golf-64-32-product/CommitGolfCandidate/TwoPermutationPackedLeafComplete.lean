import CommitGolfCandidate.C3CheckLeaf

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf TwoPermutationPrototype.Packed.Checker

/-- The checker's leaf recomputation for the 3c1p leaf, behind the one interface the record loop
consumes. -/
theorem actual_leaf_block : LeafBlockRefines C3RecordLeaf.c3Block := C3RecordLeaf.c3_leaf_block

end TwoPermutationPrototype.Packed.RecordLeaf
