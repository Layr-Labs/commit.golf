import CommitGolfCandidate.ReconstructedOpeningRecordList
import CommitGolfCandidate.ReconstructedOpeningCapSource
import CommitGolfCandidate.ReconstructedHonestSegmentFlags

namespace CommitGolfCandidate.Reconstruction.OpeningDelivery
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningCursor OpeningPut
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 16000
attribute [local irreducible] ArtifactEncoding.decode execute

theorem lower : HonestDelivery.LowerAll := by
  intro o k msg trap ps pos stored
  obtain ⟨s,m,n,b,r,p⟩ := OpeningRecordList.run o k msg trap stored ps pos ps.card (Nat.le_refl _)
  have pc : s.pc=addr 1429 := by simpa only [Nat.sub_self,if_true] using p.pc
  have rs := p.regs
  rw [Nat.sub_self,OpeningRecordList.complete] at rs
  refine ⟨n,s,b,r,OpeningCapSource.source trap ps pos ps.card _ s m p.fits rs p.live,pc,
    (p.fits.registers _).trans rs.bit,?_,(HonestSegmentFlags.from_first o trap ps pos n s r pc).2.2⟩
  have mem := p.data
  rw [OpeningRecordList.complete] at mem
  intro j good
  change (s.getMem (wordAddress (base+j))).toNat=_
  exact (congrArg BitVec.toNat (p.fits.memory (base+j) (by unfold base capacity at *;omega))).trans (mem j good)

end CommitGolfCandidate.Reconstruction.OpeningDelivery
