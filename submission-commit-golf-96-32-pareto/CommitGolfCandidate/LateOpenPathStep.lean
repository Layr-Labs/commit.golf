import CommitGolfCandidate.LateOpenPathModel

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem no_load (b : Part) (s : MachineState) (pc : s.pc=pcAt b.start) (noReads : b.reads=[]) : BlockResult b s :=
  block_result b s pc (by intro a h; rw [noReads] at h; simp at h)

private def pathRegs : List Reg := [.x25,.x20,.x22,.x17,.x28]

private theorem same_path {s t : MachineState} {i d l out} (f : PathFrame s i d l out)
    (e : ∀ r ∈ pathRegs, t.getReg r = s.getReg r) : PathFrame t i d l out :=
  ⟨(e _ (by decide)).trans f.ptr,(e _ (by decide)).trans f.idx,(e _ (by decide)).trans f.base,
    (e _ (by decide)).trans f.span,(e _ (by decide)).trans f.left⟩

private theorem selected_source (s : MachineState) (i : Index) (d l out : Nat) (f : PathFrame s i d l out)
    (block : BlockResult .siblingSource s) :
    (Part.siblingSource.after s).getReg .x23=W (nodeAddress l (mate i l)) := by
  have e := block.regs .x23
  change _ = s.getReg .x22 + (((s.getReg .x20 ^^^ 1)+(s.getReg .x20 >>> 1)) <<< 5) at e
  rw [f.idx,f.base] at e
  have bound : indexAbove i l < 2^64 := by
    unfold indexAbove; have := i.isLt; change i.val<16777216 at this; have := Nat.div_le_self i.val (2^l);omega
  exact e.trans (sibling_ptr _ _ bound)

private theorem path_bump (s : MachineState) (i : Index) (d l out : Nat) (f : PathFrame s i d l out)
    (b : BlockResult .pathNext s) (hi : l<d) (depth : d≤LOG_LENGTH) : PathFrame (Part.pathNext.after s) i d (l+1) out := by
  have idxBound : indexAbove i l < 2^64 := by
    have h := i.isLt;change i.val < 16777216 at h;unfold indexAbove;have := Nat.div_le_self i.val (2^l);omega
  have spanBound : stride l < 2^64 := by have e:=level_count_le l;change _≤16777216 at e;unfold stride;omega
  have ptr := b.regs .x25
  have idx := b.regs .x20
  have base := b.regs .x22
  have span := b.regs .x17
  have left := b.regs .x28
  change _ = s.getReg .x25 + 32 at ptr
  change _ = s.getReg .x20 >>> 1 at idx
  change _ = s.getReg .x22 + s.getReg .x17 at base
  change _ = s.getReg .x17 >>> 1 at span
  change _ = s.getReg .x28 + 18446744073709551615 at left
  rw [f.ptr] at ptr
  rw [f.idx] at idx
  rw [f.base,f.span] at base
  rw [f.span] at span
  rw [f.left] at left
  refine ⟨ptr.trans ?_,idx.trans ?_,base.trans ?_,span.trans ?_,left.trans ?_⟩
  · exact (BitVec.ofNat_add (out+32*l) 32).symm.trans (congrArg W (by omega))
  · exact (shr _ 1 idxBound).trans (congrArg W (above_next i l).symm)
  · exact (BitVec.ofNat_add (layerBase l) (stride l)).symm.trans (congrArg W (step_base _ (by omega)))
  · exact (shr _ 1 spanBound).trans (congrArg W (step_stride _ (by omega)))
  · exact (decrement _ (by omega)).trans (congrArg W (by omega))

def oneSibling (s : MachineState) :=
  Test.morePath.after (Part.pathNext.after (copyWords (Part.siblingSource.after s) 4))

structure SiblingResult (s : MachineState) (i : Index) (d l out : Nat) (tree : Levels) : Prop where
  run : Runs s (oneSibling s) 19 19
  pc : (oneSibling s).pc=pcAt (if l+1<d then 38 else 57)
  frame : PathFrame (oneSibling s) i d (l+1) out
  common : Keeps s (oneSibling s)
  bytes : Written s (oneSibling s) (out+32*l) (bytes (n:=32) (node tree l (mate i l)))

theorem sibling_run (s : MachineState) (tree : Levels) (i : Index) (d l out : Nat) (lo : l<d) (depth : d≤LOG_LENGTH)
    (pc : s.pc=pcAt 38) (f : PathFrame s i d l out)
    (source : readBuffer s (nodeAddress l (mate i l)) 32=node tree l (mate i l))
    (high : proofBase≤out) (aligned : out%8=0) (fits : out+32*d≤MEMORY_BYTES) :
    SiblingResult s i d l out tree := by
  let addr := nodeAddress l (mate i l)
  let dest := out+32*l
  let a := Part.siblingSource.after s
  let c := copyWords a 4
  let u := Part.pathNext.after c
  have ha := no_load .siblingSource s pc rfl
  have pa : a.getReg .x23=W addr := selected_source s i d l out f ha
  have pd : a.getReg .x25=W dest := (ha.keep _ rfl).trans f.ptr
  have hb := node_ok l (mate i l) (mate_bound i l (by omega))
  have sa : AddrOK addr (8*4) := ⟨hb.2.2,by have e:=hb.2.1; unfold indexBase at e; change addr+32≤2^36; dsimp only [addr];omega⟩
  have da : AddrOK dest (8*4) := ⟨by dsimp [dest];omega,by dsimp [dest];omega⟩
  have sep : addr+32≤dest := by have e := hb.2.1; unfold indexBase at e; unfold proofBase at high;dsimp [addr,dest];omega
  have runC := copy_run .sibling a ha.pc addr dest pa pd 4 (by decide) sa da
  have cp := copied a addr dest pa pd 4 (by decide) sa da sep
  have data := copied_bytes cp sa.1 da.1 (node tree l (mate i l)) ((read_congr_mem _ _ _ _ ha.mem).trans source)
  have ac : c.pc=pcAt 51 := by change (copyWords a 4).pc=_; rw [copy_pc,ha.pc];rfl
  have hu := no_load .pathNext c ac rfl
  have ef : ∀ r ∈ pathRegs, Part.siblingSource.equation r=original r := by
    intro r mem; cases r <;> first | rfl | contradiction | simp [pathRegs] at mem
  have fc := same_path f (t:=c) (fun r hr => (copy_keeps a 4 r (by intro e;subst r; exact (by decide : ¬ Reg.x6 ∈ pathRegs) hr)).trans
      (ha.keep r (ef r hr)))
  have fu := path_bump c i d l out fc hu lo depth
  have rt := test_run .morePath u hu.pc
  have taken : Test.morePath.taken u = decide (l+1<d) := by
    change (u.getReg .x28 != (0 : Word)) = _
    rw [fu.left,W,count_test (d-(l+1)) (by change d≤24 at depth;omega)]
    by_cases yes : l+1<d <;> simp [yes,show (d-(l+1)≠0) ↔ l+1<d by omega]
  refine ⟨((ha.runs.trans runC).trans hu.runs).trans rt,?_,same_path fu (fun _ _ => MachineState.getReg_setPC),?_,?_⟩
  · change pcAt (if Test.morePath.taken u then _ else _) = _
    rw [taken]; by_cases more : l+1<d <;> simp [more,Test.target,Test.start]
  · exact ((ha.keeps (by decide)).then (copy_anchors a 4)).then ((hu.keeps (by decide)).then (test_anchors _ _))
  · exact data.congr_mem ha.mem.symm hu.mem

end CommitGolfCandidate.Late.Open
