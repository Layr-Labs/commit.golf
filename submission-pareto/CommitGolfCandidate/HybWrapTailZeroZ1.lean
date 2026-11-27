import CommitGolfCandidate.HybWrapKit

/-! Code facts for the wrapper's tail clears, split out of `HybWrapTail` to bound peak memory. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
theorem tail_codes_z1 : WrapAt 3342 (zeroStores .x6 255) := by decide +kernel

end TwoPermutationPrototype.HybWrap
