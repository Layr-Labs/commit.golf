import CommitGolfCandidate.ReconstructedOpeningHeaderReady

namespace CommitGolfCandidate.Reconstruction.OpeningLoopRegs
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningCursor OpeningPut OpeningQuery OpeningReply
open OpeningRowEntry OpeningRecordFrame TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
attribute [local irreducible] ArtifactEncoding.decode

structure Regs (m : Model) (ord count cursor : Nat) : Prop where
  zero : m.reg .x0=0
  sp : m.reg .x2=W 68719474016
  stack : m.reg .x6=wordAddress replyBase
  bit : m.reg .x7=W cursor
  frame : m.reg .x8=W 68719476336
  pointer : m.reg .x11=wordAddress (indexWord ord)
  left : m.reg .x12=W count
  tree : m.reg .x22=W OpeningHeaderAddress.heap
  dst : m.reg .x25=wordAddress base
  tag : m.reg .x31=2051

theorem start (trap : CommitStorage.Trapdoor) (ps : Positions) (pos : 0<ps.card) :
    Regs (loaded (HonestInputs.first trap ps)) 0 ps.card 0 := by
  let m := loaded (HonestInputs.first trap ps)
  have ent := first_entry trap ps pos
  obtain ⟨_,_,bit,count,_,sp,_⟩ := HonestInputs.first_record trap ps pos 0
  obtain ⟨_,_,_,reply,_,_,dst,tree,_⟩ := HonestOpeningStart.entry_registers (HonestInputs.body trap ps)
  exact ⟨ent.zero,sp,reply,bit,ent.base,ent.pointer,count,tree,dst,ent.tag⟩

def sequence (ps : Positions) (ord : Nat) (legal : ord<ps.card) : Index := (ps.sort (·≤·))[ord]'(by simpa using legal)

theorem setup (trap : CommitStorage.Trapdoor) (ps : Positions) (ord c : Nat) (m : Model)
    (reg : Regs m ord (ps.card-ord) c) (live : Agrees m.mem (memoryView (HonestInputs.first trap ps)))
    (legal : ord<ps.card) : Entry m ord (sequence ps ord legal) := by
  have positive : 0<ps.card := by omega
  have n : ps.card≤2^24 := by simpa only [Fintype.card_fin, LENGTH, LOG_LENGTH] using (Finset.card_le_univ ps)
  have first := first_entry trap ps positive
  have elem := HonestInputs.first_index trap ps ord legal
  have keep : stable (indexWord ord) := by unfold stable OpeningRowEffect.outside base capacity indexWord CommitWindows.generatorBase;omega
  have addr' : wordAddress (indexWord ord)=W (5905584160+8*ord) := by
    unfold wordAddress indexWord;congr 1;omega
  refine ⟨by omega,reg.zero,reg.frame,reg.tag,reg.pointer,?_,?_,?_,?_⟩
  · rw [live _ keep];change (HonestInputs.first trap ps).getMem (wordAddress (indexWord ord))=_
    rw [addr'];exact elem
  · exact (live _ (by decide : stable 8589934254)).trans first.reciprocal
  · exact (live _ (by decide : stable 8589934253)).trans first.mask
  · exact (live _ (by decide : stable 8589934258)).trans first.generator

end CommitGolfCandidate.Reconstruction.OpeningLoopRegs
