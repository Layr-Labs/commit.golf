import CommitGolfCandidate.ReconstructedCheckWalkValues

namespace CommitGolfCandidate.Reconstruction.CheckWalkStep
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckLayout CheckWalkValues
open TwoPermutationPrototype.RV64
set_option maxRecDepth 20000
set_option maxHeartbeats 1900000
abbrev W:=BitVec.ofNat 64

private theorem pointer : ∀ i : Fin 15,
    W (2097160+8*((CheckLowerRound.depth i).val+1))+(-8)=W (2097160+8*(CheckLowerRound.depth i).val) ∧
    wordAddress (262170+((CheckLowerRound.depth i).val+1))+(-8)=wordAddress (262170+(CheckLowerRound.depth i).val) ∧
    ((W (CheckLowerRound.depth i)).truncate 32+((-1#64).truncate 32)).signExtend 64=W ((CheckLowerRound.depth i).val-1) ∧
    W ((CheckLowerRound.depth i).val+1)+(-1)=W (CheckLowerRound.depth i) := by decide

theorem positive (o : Oracle) (idx : Index) (stream : Nat) (i : Fin 15) (v : View) (s : MachineState)
    (good : Ready v ((CheckLowerRound.depth i).val+1)) (atInput : At s idx ((CheckLowerRound.depth i).val+1) v)
    (data : StreamMemory s stream) (tables : CheckLayout.Tables s) :
    let d:=CheckLowerRound.depth i
    let parsed:=prep o idx stream i v
    ∃ t n,n≤305 ∧ Segment o n s t parsed.2 ∧ At t idx d parsed.1 ∧
      Nonempty (CheckPath.Edge o parsed.2 d (side idx (d.val+1)) v.node parsed.1.node) ∧ Untouched s t := by
  let d:=CheckLowerRound.depth i
  let g:=reader v.cursor i
  let r:=residue v.cursor
  let dir:=side idx (d.val+1)
  have hi : d.val+1=10+i.val:=by change 9+i.val+1=10+i.val;omega
  have dpos : d.val+1≠9:=by omega
  have b : v.cursor≤70000000000:=by have:=good.1;omega
  have c : 64*g.block+r.val=v.cursor:=by change 64*(v.cursor/64)+v.cursor%64=v.cursor;omega
  obtain ⟨q3,q2,q1,q0,hdr,actual⟩:=four s v.header atInput.head good.2.1
  have point : CheckLowerInput.In s g r i (divCell i):=by
    refine ⟨?_,?_,atInput.proof,?_,atInput.fp,tables.lows i,tables.mask,?_,?_,tables.bases i⟩
    · have sourcePC:=atInput.pc;change s.pc=CommitBlocks.addr (if d.val+1=9 then 381 else 280) at sourcePC
      simpa only [ite_eq_right dpos] using sourcePC
    · rw [c];exact atInput.bit
    · change s.getReg .x9=W (2097160+8*(10+i.val));rw [←hi];exact atInput.widthPtr
    · rw [←hi];exact atInput.childDepth
    · change s.getReg .x22=wordAddress (262170+(10+i.val));rw [←hi];exact atInput.basePtr
  have entry : CheckLowerRound.entered s geo i dir := by
    refine ⟨atInput.sp,atInput.fp,?_,?_⟩
    · simpa only [Nat.add_sub_cancel] using atInput.parentDepth
    · rw [atInput.route];exact parity idx i
  have run:=CheckLowerRound.positive o s g r i (divCell i) stream (placed _ b i) (source s stream _ i b data)
    (by have:=i.isLt;unfold divCell;omega) point q3 q2 q1 q0 actual geo geoPlaced (by decide) tables.ro dir entry v.node good.2.2 atInput.node
  dsimp only at run
  rw [c,←hdr] at run
  obtain ⟨t,n,small,seg,next,tv,edges,mem⟩:=run
  have retPC : (if d.val≤9 then 381 else 280)=(if d.val=9 then 381 else 280) := by
    have low : 9≤d.val:=by change 9≤9+i.val;omega
    by_cases same : d.val=9 <;> simp [same] <;> omega
  refine ⟨t,n,small,seg,?_,edges,mem⟩
  refine ⟨next.pc.trans (congrArg CommitBlocks.addr retPC),next.sp.trans atInput.sp,next.fp.trans atInput.fp,
    next.source.trans atInput.proof,?_,?_,?_,?_,?_,next.bit,next.header,tv⟩
  · rw [next.widthPtr,atInput.widthPtr];exact (pointer i).1
  · rw [next.basePtr,atInput.basePtr];exact (pointer i).2.1
  · rw [next.parentDepth,atInput.parentDepth,Nat.add_sub_cancel];exact (pointer i).2.2.1
  · rw [next.childDepth,atInput.childDepth];exact (pointer i).2.2.2
  · rw [next.route,atInput.route];exact CheckWalkValues.shift idx i

end CommitGolfCandidate.Reconstruction.CheckWalkStep
