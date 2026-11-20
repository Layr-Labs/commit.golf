import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.QuadCommitGeometry

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves
set_option maxHeartbeats 900000

/-- Quartet block `g` (words): even blocks every 2,048 bytes; an odd block sits 200 bytes below its octet's even block. -/
def qSource (g : Nat) := 603980292+128*g-(if g%2=1 then 153 else 0)
def qLeaf (i : Nat) := qSource (i/4)+9+4*(i%4)
def qUpper (g : Nat) := 536871428+4*(4194304+g)
def qSalt (i : Nat) := 1140851204+2*i

theorem salt_address (i : Nat) :
    8*qSalt i = 4294971424+saltBaseOffset+16*i := by
  rw [base_offsets.2];unfold qSalt;omega


end TwoPermutationPrototype.QuartetCommit
