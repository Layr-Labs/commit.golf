import CommitGolfCandidate.ReconstructedOpeningLoopRegs
import CommitGolfCandidate.ReconstructedCapEntry

namespace CommitGolfCandidate.Reconstruction.OpeningCapSource
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningCursor OpeningPut OpeningRecordFrame OpeningLoopRegs
open TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
attribute [local irreducible] ArtifactEncoding.decode

theorem source (trap : CommitStorage.Trapdoor) (ps : Positions) (pos : 0<ps.card) (n c : Nat)
    (s : MachineState) (m : Model) (fits : Fits s m) (regs : Regs m n 0 c)
    (live : Agrees m.mem (memoryView (HonestInputs.first trap ps))) : CapEntry.Source s trap ps := by
  let first := HonestInputs.first trap ps
  have transfer (w : Nat) (h : stable w) (sm : w<2^33) :
      s.getMem (wordAddress w)=first.getMem (wordAddress w) := (fits.memory w sm).trans (live w h)
  obtain ⟨_,_,_,_,_,_,saved⟩ := HonestInputs.first_record trap ps pos 0
  refine ⟨(fits.registers _).trans regs.sp,(fits.registers _).trans regs.frame,
    (transfer 8589934541 (by decide) (by decide)).trans saved,
    (transfer 8589934264 (by decide) (by decide)).trans (OpeningHeaderReady.initial_constants trap ps).stack1872,
    (transfer 8589934263 (by decide) (by decide)).trans (OpeningHeaderReady.initial_constants trap ps).stack1864,
    ?_,?_,?_⟩
  · intro d
    have h := d.isLt
    have atWord : CapEntry.W (2097152+8*d.val)=wordAddress (262144+d.val) := by unfold wordAddress;congr 1;omega
    have ke : stable (262144+d.val) := by unfold stable OpeningRowEffect.outside base capacity CommitWindows.generatorBase;omega
    rw [atWord,transfer _ ke (by omega),←atWord]
    exact (HonestInputs.first_tables trap ps pos ⟨d.val,by omega⟩).1
  · intro d
    have h := d.isLt
    have atWord : CapEntry.W (2097352+8*d.val)=wordAddress (262169+d.val) := by unfold wordAddress;congr 1;omega
    have ke : stable (262169+d.val) := by unfold stable OpeningRowEffect.outside base capacity CommitWindows.generatorBase;omega
    rw [atWord,transfer _ ke (by omega),←atWord]
    exact (HonestInputs.first_tables trap ps pos ⟨d.val,by omega⟩).2
  · intro d j k _ hd cell hk
    have bound := cell.2.2.trans_le (Nat.pow_le_pow_right (n:=2) (by decide) (show d+1≤10 by omega))
    let w := CommitParents.addr d j/8+k
    have lim : w<2^33 := by unfold w CommitParents.addr;omega
    have eq : CapEntry.W (CommitParents.addr d j+8*k)=wordAddress w := by unfold w wordAddress CommitParents.addr;congr 1;omega
    calc
      _ = m.mem w := (congrArg s.getMem eq).trans (fits.memory w lim)
      _ = _ := ?_
    exact heap_of_agrees m.mem trap ps live d j cell k hk

end CommitGolfCandidate.Reconstruction.OpeningCapSource
