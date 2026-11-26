import CommitGolfCandidate.S4Padding
import CommitGolfCandidate.LateArtifact

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

abbrev Trapdoor := BitVec (8*submission.sizes.trapdoor)
def slice (td : Trapdoor) (addr n : Nat) : BitVec (8*n) :=
  td.extractLsb' (8*(addr-4294971424)) (8*n)

structure TrapdoorAgrees (td : Trapdoor) (levels : Levels) (salts : SaltTape) : Prop where
  nodes : ∀ d ≤ LOG_LENGTH, ∀ i < levelCount d, slice td (nodeAddress d i) 32 = node levels d i
  salt : ∀ i : Index, slice td (sharedSaltAddr i) 24 = salts i
  padding : ∀ h p k,Padding h p k → slice td (unusedSlotAddr h p k) 32=0
  missing : ∀ h≤LOG_LENGTH,∀ j,levelCount h≤j → node levels h j=0

end CommitGolfCandidate.Late
