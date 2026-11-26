import CommitGolfCandidate.ReconstructedOpeningQuery

namespace CommitGolfCandidate.Reconstruction.OpeningReply
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel LeafSteps Generator CommitWindows
open TwoPermutationPrototype.RV64 OpeningOps OpeningIndex OpeningQuery LeafContent
open TwoPermutationPrototype (window writeWindow writeWord)
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000
attribute [local irreducible] ArtifactEncoding.decode Riscv.execute

abbrev replyBase : Nat := 8589934272

def loaded (s : MachineState) : Model := ⟨s.getReg,memoryView s⟩
theorem fits (s : MachineState) : Fits s (loaded s) := ⟨fun _ => rfl,fun _ _ => rfl⟩

def firstIndex (ps : Positions) (positive : 0<ps.card) : Index := (ps.sort (·≤·))[0]'(by simpa using positive)

private theorem index_word (s : MachineState) (v : Word)
    (h : s.getMem (BitVec.ofNat 64 (5905584160+8*0))=v) :
    (loaded s).mem (indexWord 0)=v := h

theorem first_entry (trap : CommitStorage.Trapdoor) (ps : Positions) (pos : 0<ps.card) :
    Entry (loaded (HonestInputs.first trap ps)) 0 (firstIndex ps pos) := by
  have setup := HonestOpeningStart.entry_registers (HonestInputs.body trap ps)
  have extra := HonestOpeningStart.entry_constants (HonestInputs.body trap ps)
  refine ⟨by decide,rfl,setup.2.2.1,extra.2.1,extra.1,?_,?_,?_,?_⟩
  · exact index_word _ (BitVec.ofNat 64 (firstIndex ps pos).val) (HonestInputs.first_index trap ps 0 pos)
  · rfl
  · rfl
  · rfl

private theorem saved_key (m : Model) (k : Key) (header : KeyRegion m.mem k) :
    KeyRegion (saves m).mem k := by
  intro w lo hi except
  have a : w≠savePtr := by unfold generatorBase at hi;unfold savePtr;omega
  have b : w≠saveCount := by unfold generatorBase at hi;unfold saveCount;omega
  simp only [saves,Model.store,writeWord,a,b,ite_false]
  exact header w lo hi except

theorem actual_input (o : Oracle) (m : Model) (ord : Nat) (k : Key) (i : Index)
    (ok : Entry m ord i) (header : KeyRegion m.mem k) :
    window (atQuery m ord).mem (start i) = (fun j : Fin 25 => inputWord (tileOf i) (groupOf i) k j.val) := by
  rw [(setup o m ord i ok).2.2]
  exact OpeningTrap.generate _ k i (saved_key m k header)

theorem reply (o : Oracle) (m : Model) (ord : Nat) (k : Key) (i : Index)
    (ok : Entry m ord i) (header : KeyRegion m.mem k) (j : Fin 25) :
    ((atQuery m ord).permute o (start i) replyBase).mem (replyBase+j.val)=replyWords (tapeReply o k i) j := by
  unfold Model.permute
  rw [actual_input o m ord k i ok header]
  simp only [writeWindow,show replyBase ≤ replyBase+j.val ∧ replyBase+j.val < replyBase+25 by have := j.isLt;omega,
    and_self,dite_true,Nat.add_sub_cancel_left,tapeReply]

attribute [local irreducible] atQuery HonestInputs.first

/-- From the first record of a nonempty ABI opening, the selected permutation reply
is exactly the same private tape block used by the actual commitment. -/
theorem first_query (o : Oracle) (k : Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (stored : CommitStorage.Stored o k msg trap) (ps : Positions) (pos : 0<ps.card) :
    let s := HonestInputs.first trap ps
    let i := firstIndex ps pos
    ∃ u, CommitExact.Segment o (Artifact.submission.image .opening) 42 s u ∧
      u.pc=CommitBlocks.addr 185 ∧
      (∀ j : Fin 25, memoryView u (replyBase+j.val)=replyWords (tapeReply o k i) j) ∧
      u.getReg .x16=highProduct (slot i) ∧ u.getReg .x14=word (slot i) := by
  let s := HonestInputs.first trap ps
  let m := loaded s
  let i := firstIndex ps pos
  have ent := first_entry trap ps pos
  have header := OpeningTrap.first_generator o k msg trap stored ps pos
  have loc := (HonestInputs.first_record trap ps pos 0).2.1
  obtain ⟨u,sg,pc,hh⟩ := query_run o m 0 i ent s loc (fits s)
  have ready := (setup o m 0 i ent).2.1
  refine ⟨u,sg,pc,fun j => (hh.memory _ (by have := j.isLt;unfold replyBase;omega)).trans
    (reply o m 0 k i ent header j),?_,?_⟩
  · calc
      u.getReg .x16 = (atQuery m 0).reg .x16 := hh.registers .x16
      _ = _ := ready.prod
  · calc
      u.getReg .x14 = (atQuery m 0).reg .x14 := hh.registers .x14
      _ = _ := ready.slot

end CommitGolfCandidate.Reconstruction.OpeningReply
