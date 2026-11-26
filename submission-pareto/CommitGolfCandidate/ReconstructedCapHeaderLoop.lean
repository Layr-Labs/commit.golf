import CommitGolfCandidate.ReconstructedCapHeaderPiece

namespace CommitGolfCandidate.Reconstruction.CapHeaderLoop
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningPut OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 24000
set_option maxHeartbeats 2300000

theorem loop (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (stored : CommitStorage.Stored o key msg trap) (nonempty : 0<ps.card) (f : Nat→Bool)
    (d : Fin 10) (paid : 8≤d.val) (xs : List Nat) (size : xs.length≤256)
    (cells : ∀ id∈xs, CommitParents.Cell d.val id)
    (todo done_ : List Nat) (present : todo≠[]) (split : xs=done_++todo)
    (s : MachineState) (pc : s.pc=addr 1603) (fs : List Wire.Field)
    (data : CapLevelData.Packed s trap ps f d.val xs fs) (input : CapHeaderPiece.Local s d.val xs.length done_.length)
    (room : Wire.bits (fs++Encoding.capHeaders (CapSchedule.digit (LeafTree.tree o key msg) d.val) todo)+192<capacity*64) :
    ∃ n t, n≤43*todo.length ∧ CommitExact.Segment o OpeningStraight.image n s t ∧ t.pc=addr 1449 ∧ t.getReg .x26=2 ∧
      CapLevelData.Packed t trap ps f d.val xs (fs++Encoding.capHeaders (CapSchedule.digit (LeafTree.tree o key msg) d.val) todo) := by
  let dig := CapSchedule.digit (LeafTree.tree o key msg) d.val
  let g := todo.take 4
  let tail := todo.drop 4
  let j := done_.length
  have span : xs.length=j+todo.length := by rw [split,List.length_append]
  have count : 0<todo.length := List.length_pos_iff.mpr present
  have sz : g.length=min 4 todo.length := List.length_take
  have tailSize : tail.length=todo.length-4 := List.length_drop
  have limit : j+g.length≤xs.length := by omega
  have inside : j < xs.length := by omega
  have joined : xs=(done_++g)++tail := by rw [List.append_assoc];exact split.trans (congrArg (done_++·) (List.take_append_drop 4 todo).symm)
  have sel (i : Fin g.length) : xs[j+i.val]'(by have bound := i.isLt;omega)=g[i.val] := by
    have bound : i.val<todo.length := by have b:=i.isLt;omega
    subst xs
    simp [j,g,List.getElem_append_right (show done_.length≤done_.length+i.val by omega)]
  have good : ∀ id∈g, CommitParents.Cell d.val id := by
    intro id h
    apply cells
    rw [joined]
    exact List.mem_append_left _ (List.mem_append_right _ h)
  have inputData := CapHeaderPiece.foldData o key msg trap ps stored nonempty f d paid xs g j s fs data input size limit sel good
  have header := CapSchedule.header_step dig todo present
  let hdr := Encoding.headerValue dig g
  let gs := fs++[⟨hdr,31⟩]
  have fieldsEq : fs++Encoding.capHeaders dig todo=gs++Encoding.capHeaders dig tail := by
    rw [header];simp [gs,hdr,g,tail,List.append_assoc]
  have sum : Wire.bits (gs++Encoding.capHeaders dig tail)+192<capacity*64 := by rw [←fieldsEq];exact room
  have named := data.common.regs
  obtain ⟨n,t,used,run,loc,post⟩ := CapHeaderPiece.run o s d xs g j dig fs pc input inputData
    (named .x17 (W HonestRecordMemory.proofBase) (by decide)) (named .x19 34 (by decide)) data.buffer
    (by have := CapSchedule.prefix_room fs _ room;omega) size inside (by rw [sz];congr 1;omega)
  have gBound := HonestCapPlan.width_bound d.val (by have bound:=d.isLt;omega)
  have atEnd := CapLevelData.change s t trap ps f d.val xs fs gs data gBound (by omega) post.buf post.kept post.mem
  have branch := CapHeaderPiece.guard o t loc (j+4) xs.length size (by omega) post.next post.count
  have shorter : tail.length<todo.length := by omega
  by_cases more : j+4 < xs.length
  · rw [ite_eq_left more] at branch
    have four : g.length=4 := by omega
    have newLen : (done_++g).length=j+4 := by rw [List.length_append,four]
    have cont : CapHeaderPiece.Local (t.setPC (addr 1603)) d.val xs.length (done_++g).length := by
      rw [newLen];exact ⟨post.count,post.next,post.back,post.pending (by omega),post.mask,post.headerMask,post.two⟩
    have nextData := CapLevelData.jump t trap ps f d.val xs gs atEnd (addr 1603) gBound (by omega)
    have left : tail≠[] := List.length_pos_iff.mp (by omega)
    obtain ⟨k,u,hu,deeper,last,two,after⟩ := loop o key msg trap ps stored nonempty f d paid xs size cells
      tail (done_++g) left joined _ rfl gs nextData cont sum
    refine ⟨n+1+k,u,by omega,CommitExact.compose (CommitExact.compose run branch) deeper,last,two,?_⟩
    change CapLevelData.Packed _ _ _ _ _ _ (fs++Encoding.capHeaders dig todo)
    rw [fieldsEq];exact after
  · rw [ite_eq_right more] at branch
    have endTail : tail=[] := List.length_eq_zero_iff.mp (by omega)
    have all : fs++Encoding.capHeaders dig todo=gs := by rw [fieldsEq,endTail];simp [Encoding.capHeaders]
    refine ⟨n+1,_,by omega,CommitExact.compose run branch,rfl,post.two,?_⟩
    change CapLevelData.Packed _ _ _ _ _ _ (fs++Encoding.capHeaders dig todo)
    rw [all];exact CapLevelData.jump t trap ps f d.val xs gs atEnd _ gBound (by omega)
termination_by todo.length

end CommitGolfCandidate.Reconstruction.CapHeaderLoop
