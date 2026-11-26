import CommitGolfCandidate.S5Layout
import CommitGolfCandidate.InputMemory
import CommitGolf.Artifact
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv
abbrev Trapdoor := BitVec (8*Artifact.submission.sizes.trapdoor)
def slice (td : Trapdoor) (addr n : Nat) := td.extractLsb' (8*(addr-4294975488)) (8*n)
structure TrapdoorAgrees (td : Trapdoor) (levels : Late.Levels) (salt : Late.SaltTape) : Prop where
  nodes : ∀ d≤LOG_LENGTH,∀ i<levelCount d,slice td (nodeAddress d i) 32=Late.node levels d i
  salts : ∀ i : Index,slice td (saltAddress i) 24=salt i
  missing : ∀ d p k, d<24 → p<levelCount (d+1) → k<S4.radix d → levelCount d≤S4.radix d*p+k →
    slice td (rowAddress d p+32*k) 32=Late.node levels d (S4.radix d*p+k)
end CommitGolfCandidate.S5Machine
