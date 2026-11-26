import CommitGolfCandidate.ReconstructedCheckRecordFrame
import CommitGolfCandidate.ReconstructedCheckRecordSpec

namespace CommitGolfCandidate.Reconstruction.CheckRecordFlight
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckLayout CheckRecordABI CheckWalkValues CheckRecordSpec CheckRecorded
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 15000
set_option maxHeartbeats 1700000
set_option exponentiation.threshold 2048
abbrev W:=BitVec.ofNat 64

theorem positive (o : Oracle) (s : MachineState) (input : CheckInput) (i : Fin input.positions.card)
    (p : Persistent s input) (regs : Registers s i.val (cursor i)) :
    let bits:=Wire.unpackBytes input.proof
    let idx:=(position input i).val
    let msg:=entryWords (input.values (position input i))
    let scan:=lower o idx bits (cursor i) msg
    ∃ t n,n≤4854 ∧ Segment o n s t (rows o idx bits (cursor i) msg) ∧
      At t idx 9 scan.1 ∧ Ready scan.1 9 ∧ CheckWalk.Lifts o idx scan.2 24 (leaf o idx bits (cursor i) msg) scan.1.node ∧
      (rows o idx bits (cursor i) msg).length=84 ∧ t.getMem (W (CheckLayout.fp-2376))=W i.val ∧ CheckRecordFrame.Frame s t := by
  let bits:=Wire.unpackBytes input.proof
  let idx:=(position input i).val
  let msg:=entryWords (input.values (position input i))
  let c:=cursor i
  let r:=residue c
  let g:=reader c 0
  have eq : 64*g.block+r.val=c:=by change 64*(c/64)+c%64=c;omega
  have lim:=ordinal_limit input i
  have maxC : c≤70000000000:=by change 3633*i.val≤_;omega
  have cur : s.getReg .x24=W (64*g.block+r.val):=eq.symm ▸ regs.cursor
  obtain ⟨u,header,pc,heap,step,head0,lo,mi,up,hi,sp,fp,pbase,ordinal,compact⟩:=
    CheckRecordHeader.complete o s g r bits 8589934466 i idx msg (placed c maxC 0).toPlaced
      (source s bits c 0 maxC p.stream) regs.pc cur regs.proof (contents s input i p regs)
  rw [eq] at header step head0 lo mi up hi
  let fr:=CheckRecordFrame.fromHeader compact
  have pu:=CheckRecordFrame.persistent fr p
  obtain ⟨v,init,vpc,depth,prev,widths,bases,keep,clean⟩:=CheckInitLower.positive o u pc (fp.trans regs.fp) pu.widths
  let frV:=CheckRecordFrame.trans fr (CheckRecordFrame.fromWords clean)
  have pv:=CheckRecordFrame.persistent frV p
  let v0:=start o idx bits c msg
  have av : At v idx 24 v0:=by
    refine ⟨vpc,(keep .x2 (by decide)).trans (sp.trans regs.sp),(keep .x8 (by decide)).trans (fp.trans regs.fp),
      (keep .x19 (by decide)).trans (pbase.trans regs.proof),widths,bases,prev,depth,?_,(keep .x24 (by decide)).trans step,?_,?_⟩
    · rw [keep .x23 (by decide),heap]
      simp only [CheckWalkValues.heap,show 24-24=0 by decide,pow_zero,Nat.div_one]
      rw [BitVec.add_comm];exact (BitVec.ofNat_add (n:=64) (2^24) idx.val).symm
    · change CheckRecordHeader.limbs v=_
      unfold CheckRecordHeader.limbs
      rw [keep .x27 (by decide),keep .x18 (by decide),keep .x20 (by decide),keep .x25 (by decide)]
      exact head0
    · intro j;change v.getReg (CheckPair.current j)=CheckParentWords.digWord (unpack _) j
      rw [CheckParentWords.digWord,pack_unpack,keep _ ((by decide : ∀ k : Fin 4,CheckPair.current k∈CheckInitLower.saved) j)]
      fin_cases j
      · exact lo
      · exact mi
      · exact up
      · exact hi
  obtain ⟨t,n,bound,walk,post,rg,lifts,count,changeM⟩:=CheckWalk.records o idx bits v0 v (ready o idx bits i msg lim) av pv.stream pv.tables
  have cost := CheckHeaderPlan.checked r
  simp only [CheckHeaderPlan.receipt,Bool.and_eq_true,decide_eq_true_eq] at cost
  have hdr : (CheckHeaderPlan.done r).ticks≤53:=cost.1.2.2.2.2.2.2
  have keptOrd : t.getMem (W (CheckLayout.fp-2376))=W i.val := by
    change t.getMem (wordAddress (8589934466-297))=_
    rw [changeM _ (by decide) (by apply outside <;> decide),clean _ (by decide)]
    exact ordinal
  refine ⟨t,((CheckHeaderPlan.done r).ticks+218+8)+n,by omega,?_,post,rg,lifts,?_,keptOrd,CheckRecordFrame.trans frV (CheckRecordFrame.fromWalk changeM)⟩
  · change Segment o _ s t (CheckLeaf.rows o idx (CheckRecordHeader.salt bits c) msg ++ (CheckWalk.evaluate o idx bits 15 v0).2)
    simpa only [List.append_nil] using compose (compose header init) walk
  · change (CheckLeaf.rows _ _ _ _ ++ (CheckWalk.evaluate _ _ _ _ v0).2).length=_
    rw [List.length_append,count];rfl

end CommitGolfCandidate.Reconstruction.CheckRecordFlight
