import CommitGolfCandidate.ReconstructedCheckCapLevel
import CommitGolfCandidate.ReconstructedCheckCapIterate
import CommitGolfCandidate.ReconstructedCheckCapEnter
import CommitGolfCandidate.ReconstructedCheckRecordABI

namespace CommitGolfCandidate.Reconstruction.CheckCapInitial
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckCapLevel CheckCapIterate
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CheckRecordABI (Persistent tableWord)
open CheckCapScanData (W)
set_option maxRecDepth 17000
set_option maxHeartbeats 1450000

private def imageWord (j : Nat) := W (∑ b ∈ Finset.range 8,
  (Artifact.checkData.get 8 ⟨(8*j+b)%1008,by omega⟩).toNat*2^(8*b))

private theorem image_word (j : Nat) (bound : j<126) : tableWord j=imageWord j := by
  apply congrArg (BitVec.ofNat 64)
  apply Finset.sum_congr rfl
  intro b hb
  have below:=Finset.mem_range.mp hb
  have h : 8*j+b<1008:=by omega
  have digit:=ArtifactEncoding.getD_decode 8 Artifact.checkData (8*j+b) h
  rw [List.getD_eq_getElem?_getD] at digit
  change ((ArtifactEncoding.decode 8 Artifact.checkData)[8*j+b]?.getD 0).toNat*_=_
  rw [digit]
  have idx : (⟨8*j+b,h⟩ : Fin 1008)=⟨(8*j+b)%1008,by omega⟩:=Fin.ext (Nat.mod_eq_of_lt h).symm
  exact congrArg (fun z=>(Artifact.checkData.get 8 z).toNat*2^(8*b)) idx

private theorem widths : ∀ i : Fin 10,imageWord (i.val+1)=W (Encoding.lows i.val) := by decide +kernel

private theorem data {s : MachineState} {input : CheckInput} (p : Persistent s input) :
    Data s (Wire.unpackBytes input.proof) := by
  refine ⟨?_,p.tables.mask,p.tables.ro,?_⟩
  · intro d _ small
    have a:=p.imageData (d+1) (by omega)
    have h:=(image_word (d+1) (by omega)).trans (widths ⟨d,by omega⟩)
    change s.getMem (W (8*(262145+d)))=_
    rw [show 8*(262145+d)=2097152+8*(d+1) by omega]
    exact a.trans h
  · intro i hi
    change s.getMem (W (8*(1291846156+i)))=_
    rw [show 8*(1291846156+i)=10334769248+8*i by omega]
    exact p.stream i hi

def CanonicalBottom (f : Nat→Bool) (s : MachineState) :=
  ∀ j,j<512→f j=true→Canonical 9 (node s (512+j))

theorem enter (o : Oracle) (input : CheckInput) (s : MachineState) (c : Nat) (f : Nat→Bool)
    (pc : s.pc=CommitBlocks.addr 409) (fp : s.getReg .x8=W CheckLayout.fp) (sp : s.getReg .x2=W CheckLayout.sp)
    (cur : s.getReg .x24=W c) (p : Persistent s input) (flags : HonestFlagState.Initial f s) (canon : CanonicalBottom f s) :
    ∃ u,Segment o 14 s u [] ∧ Boundary f (Wire.unpackBytes input.proof) 9 c u ∧ u.mem=s.mem := by
  have magic : s.getMem 2097152=W CheckGroupRadix.magic:=(p.imageData 0 (by decide)).trans
    ((image_word 0 (by decide)).trans (by decide +kernel))
  obtain ⟨u,seg,e,mem⟩:=CheckCapEnter.run o s c pc fp sp cur magic
  have fr : Frame s u:=fun q _ _=>congrFun mem _
  have rows : HonestSizeRows.Rows f 9 0 s:=HonestSizeRows.init flags (by decide)
  refine ⟨u,seg,⟨⟨e.pc,e.depth,e.one,e.two,e.limit,e.stack,e.frame,e.table,e.cursor,e.slots⟩,
    e.radix,e.magic,e.proof,CheckCapFrames.data fr (data p),?_,?_⟩,mem⟩
  · intro _
    exact HonestSizeRows.carry rows (by decide) (fun k _=>CheckCapScanFlags.copiedByte s u mem _)
  · intro id lo hi on
    change 512 ≤ id at lo
    change id<1024 at hi
    change f (id-512)=true at on
    have v:=canon (id-512) (by omega) on
    rw [show 512+(id-512)=id by omega] at v
    unfold node
    rw [CommitParents.cell_congr mem]
    exact v

theorem nine (o : Oracle) (input : CheckInput) (s : MachineState) (c : Nat)
    (pc : s.pc=CommitBlocks.addr 409) (fp : s.getReg .x8=W CheckLayout.fp) (sp : s.getReg .x2=W CheckLayout.sp)
    (cur : s.getReg .x24=W c) (p : Persistent s input) (flags : HonestFlagState.Initial (CapEntry.flags input.positions) s)
    (canon : CanonicalBottom (CapEntry.flags input.positions) s) (space : c+630000≤70000000000) :
    ∃ n u t log out,n≤165060 ∧ log.length≤2303 ∧ log.length≤16*input.positions.card ∧ Segment o n s t log ∧
      Frame s t ∧ u.mem=s.mem ∧ Trail o (CapEntry.flags input.positions) (Wire.unpackBytes input.proof) 9 c u out t log := by
  obtain ⟨u,seg,ready,mem⟩:=enter o input s c _ pc fp sp cur p flags canon
  obtain ⟨n,t,log,out,ticks,bound,count,run,frame,trail⟩:=
    CheckCapIterate.nine o input.positions _ c u (CheckCapLevel.run o _ _) space ready
  exact ⟨14+n,u,t,log,out,by omega,bound,count,compose seg run,
    fun q h a=>(frame q h a).trans (congrFun mem _),mem,trail⟩

end CommitGolfCandidate.Reconstruction.CheckCapInitial
