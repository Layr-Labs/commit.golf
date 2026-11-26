import CommitGolfCandidate.ReconstructedHonestCapStages
import CommitGolfCandidate.ReconstructedHonestFrame

namespace CommitGolfCandidate.Reconstruction.HonestCapFrame
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapStages HonestCuts
open CommitBlocks (addr)

/-- All control registers outside the writes of each cap segment, on both
sides of all data-dependent branches. -/
def registers : Nat → List Reg
  | 1429 => [.x2,.x8,.x20,.x21,.x22,.x24,.x25,.x30]
  | 1449 => [.x2,.x8,.x11,.x20,.x21,.x22,.x24,.x25,.x26,.x30]
  | 1451 => [.x2,.x8,.x10,.x11,.x25,.x26,.x30]
  | 1469 => [.x2,.x8,.x10,.x11,.x20,.x21,.x22,.x24,.x25,.x26,.x30]
  | 1470 => [.x2,.x8,.x10,.x11,.x22,.x25,.x26,.x30]
  | 1483 => [.x2,.x8,.x10,.x11,.x20,.x26,.x30]
  | 1511 => [.x2,.x8,.x10,.x11,.x20,.x21,.x22,.x24,.x25,.x26,.x30]
  | 1512 => [.x2,.x8,.x10,.x11,.x20,.x21,.x22,.x25]
  | 1581 => [.x2,.x8,.x10,.x11,.x20,.x25,.x30]
  | 1602 => [.x2,.x8,.x10,.x11,.x20,.x21,.x22,.x24,.x25,.x26,.x30]
  | 1603 => [.x2,.x8,.x10,.x11,.x20,.x21,.x22,.x24,.x26]
  | 1610 => [.x2,.x8,.x10,.x11,.x20,.x21,.x22,.x24,.x26]
  | 1625 => [.x2,.x8,.x10,.x11,.x20,.x21,.x22,.x24,.x25,.x26,.x30]
  | 1626 => [.x2,.x8,.x10,.x11,.x20,.x25,.x26,.x30]
  | _ => []

def prices : List (Nat × Nat) := [(1429,19),(1449,2),(1451,14),(1469,1),(1470,17),(1483,26),(1511,1),(1512,59),(1581,16),(1602,1),(1603,7),(1610,18),(1625,1),(1626,19)]

theorem frame (idx fee : Nat) (mem : (idx,fee) ∈ prices) (s t : MachineState) (coins : Bool)
    (pc : s.pc = addr idx) (path : Reaches (Artifact.submission.image .opening) coins stops s t) :
    ∀ r ∈ registers idx, t.getReg r = s.getReg r := by
  have checked : ∀ pair ∈ prices, HonestFrame.check Artifact.openingCode stops (registers pair.1) pair.2 (addr pair.1) = true := by
    intro pair member
    simp only [prices,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  exact HonestFrame.sound Artifact.openingCode _ (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) stops _ _ _
    (checked _ mem) coins s t pc path

end CommitGolfCandidate.Reconstruction.HonestCapFrame
