import CommitGolfCandidate.ReconstructedOpeningRecordTail
import CommitGolfCandidate.ReconstructedOpeningLower
import CommitGolfCandidate.ReconstructedOpeningSaltStream

namespace CommitGolfCandidate.Reconstruction.OpeningRecordExecution
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningCursor OpeningPut OpeningQuery
open TwoPermutationPrototype.RV64 OpeningRowEntry OpeningRowEffect OpeningRecordFrame OpeningLoopRegs
open CommitBlocks (addr)
set_option maxRecDepth 22000
set_option maxHeartbeats 2200000
attribute [local irreducible] ArtifactEncoding.decode execute

theorem saltBound (c : Nat) (i : Index) : OpeningRecordSalt.steps c i≤105 := by
  unfold OpeningRecordSalt.steps OpeningSaltHigh.steps;split_ifs <;> omega

theorem headerBound (c : Nat) : OpeningHeader.headerSteps c≤175 := by
  unfold OpeningHeader.headerSteps OpeningHeaderWrite.steps;split_ifs <;> omega

noncomputable def record (o : Oracle) (k : Generator.Key) (msg : Message) (i : Index) :=
  Encoding.record (LeafTree.tree o k msg) i (HidingTape.actualTape o.permutation k i)

theorem run (o : Oracle) (k : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor)
    (stored : CommitStorage.Stored o k msg trap) (ps : Positions) (ord : Nat) (legal : ord<ps.card)
    (fs : List Wire.Field) (room : (Wire.bits fs+3633)/64<capacity) (m : Model)
    (reg : Regs m ord (ps.card-ord) (Wire.bits fs)) (live : Agrees m.mem (memoryView (HonestInputs.first trap ps)))
    (data : Serialized m.mem (Wire.pack fs)) (s : MachineState) (pc : s.pc=addr 143) (f : Fits s m) :
    ∃ t out n, n≤2000 ∧ CommitExact.Segment o OpeningStraight.image n s t ∧
      t.pc=(if ps.card-(ord+1)=0 then addr 1429 else addr 143) ∧ Fits t out ∧
      Regs out (ord+1) (ps.card-(ord+1)) (Wire.bits fs+3633) ∧
      Agrees out.mem (memoryView (HonestInputs.first trap ps)) ∧
      Serialized out.mem (Wire.pack (fs++record o k msg (sequence ps ord legal))) := by
  let e : Env := ⟨sequence ps ord legal,Wire.bits fs,W (ps.card-ord),room⟩
  have ne : 0<ps.card := by omega
  have h64 : (e.cursor+64)/64<capacity := by change (Wire.bits fs+64)/64<capacity;omega
  have ent := OpeningLoopRegs.setup trap ps ord e.cursor m reg live legal
  obtain ⟨a,p,sa,pa,fa,salt⟩ := OpeningRecordSalt.run o m ord e.cursor e.index k ent
    (key_of_agrees m.mem trap ps ne o k msg stored live) reg.stack reg.bit reg.dst h64 s pc f
  let x : OpeningHeader.Context := ⟨p,e.index,e.cursor⟩
  let xs := fs++OpeningSaltStream.firstFields (HidingTape.actualTape o.permutation k e.index)
  have sd := OpeningSaltStream.serialized o k e.index m p ord fs ent data h64 salt
  have before : Agrees p.mem (memoryView (HonestInputs.first trap ps)) := fun w h =>
    (salt_stable o m p k ord e.cursor e.index ent salt h64 w h).trans (live w h)
  have saved := salt_saves o m p k ord e.cursor e.index ent salt h64
  have initial := OpeningHeader.initial_eq x (salt.zero.trans reg.zero) salt.cursor (salt.frame.trans reg.frame)
    salt.position (salt.tree.trans reg.tree) (salt.proofBase.trans reg.dst)
  have h184 : (x.cursor+184)/64<capacity := by change (Wire.bits fs+184)/64<capacity;omega
  obtain ⟨b,q,sb,pb,fb,st⟩ := OpeningHeader.run o x h184 a pa (initial.symm ▸ fa)
  let top := OpeningHeader.to416 x q
  have next := OpeningHeaderReady.inputs e p q (salt.sp.trans reg.sp) (OpeningHeaderReady.constants p.mem trap ps before)
    (saved.1.trans reg.left) st
  have afterHeader : Agrees top.mem (memoryView (HonestInputs.first trap ps)) := fun w h =>
    (OpeningHeaderReady.stable_words x q h184 st w h).trans (before w h)
  let ys := xs++OpeningHeader.fields (Encoding.recordHeader (LeafTree.tree o k msg) e.index)
  have bits : Wire.bits xs=x.cursor+120 := by dsimp only [xs];rw [Wire.bits_append];rfl
  have valid : Valid e top top trap ps ys 222 := by
    refine ⟨?_,OpeningHeader.serialized x q ps trap ne (heap_of_agrees p.mem trap ps before)
      o k msg stored xs bits sd h184 st,heap_of_agrees top.mem trap ps afterHeader,fun _ _ => rfl,next.2⟩
    dsimp only [ys];rw [Wire.bits_append,bits];change (e.cursor+120)+102=e.cursor+222;omega
  obtain ⟨c,last,j,jb,sc,pc',fc,ready,done_⟩ := OpeningLower.run o k msg trap stored ps ne e top ys next.1 valid b pb fb
  have ptr : last.mem savePtr=wordAddress (indexWord ord) :=
    (done_.frame _ (Or.inr (by decide))).trans ((OpeningHeaderReady.unchanged x q h184 st _ (Or.inr (by decide))).trans
      ((OpeningHeader.front_memory x _ (Or.inr (by decide))).trans (saved.2.trans reg.pointer)))
  let remain := ps.card-(ord+1)
  have cnt : e.count=W (remain+1) := by change W (ps.card-ord)=_;congr 1;dsimp [remain];omega
  have lim : ps.card≤2^24 := by simpa only [Fintype.card_fin,LENGTH,LOG_LENGTH] using Finset.card_le_univ ps
  have bounds : remain<2^64 := by dsimp [remain];omega
  obtain ⟨t,n,nb,sd',pd,fd⟩ := OpeningRecordTail.run o e last ready remain cnt bounds c pc' fc
  have ra := saltBound e.cursor e.index
  have rb := headerBound x.cursor
  refine ⟨t,_,_,by omega,CommitExact.compose (CommitExact.compose (CommitExact.compose sa sb) sc) sd',pd,fd,
    OpeningRecordTail.registers e last ready ord remain cnt ptr,?_,?_⟩
  · intro w h
    exact (OpeningRecordTail.keep e last w h.2.2.2).trans ((done_.frame w h.1).trans (afterHeader w h))
  · have eqFields : ys++OpeningLower.fields o k msg e=fs++record o k msg e.index := by
      simp only [ys,xs,OpeningHeader.fields,OpeningSaltStream.firstFields,OpeningLower.fields,OpeningRowEffect.fields,
        record,Encoding.record,List.append_assoc,List.cons_append,List.nil_append]
    intro w h
    rw [OpeningRecordTail.keep e last (base+w) (Or.inr (by unfold base;omega)),←eqFields]
    exact done_.data w h

end CommitGolfCandidate.Reconstruction.OpeningRecordExecution
