import CommitGolfCandidate.S5FirstRound
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
attribute [local irreducible] readBuffer writeBits

structure Armed (H : Compression) (d : Height) (b : Nat) (lane : Lane) (j : Nat) (origin s : MachineState) : Prop where
  ctx : PairCtx d b s
  pc : s.pc=pcAt (chainStagePC (segmentPC d lane) j+2)
  src : s.getReg .x10=BitVec.ofNat 64 scratchBase
  dest : s.getReg .x12=BitVec.ofNat 64 scratchBase
  input : readBuffer s scratchBase 96=stageInput H d (leftChild origin d (2*b+lane.val)) (rightChild origin d (2*b+lane.val)) j
  pads : ScratchPad s
  frame : outsideLane d (2*b+lane.val) origin s

private theorem tag_advance : ∀ (d : Height) (j : Fin 15),
    tagWord d 0+signExtend12 (BitVec.ofNat 12 (j.val+1))=tagWord d ⟨j.val+1,by have :=j.isLt;omega⟩ := by decide +kernel

theorem arm_stage (o : Oracle) {d b lane j origin s} (before : ChainFrame o.compression d b lane j origin s)
    (cut : chained d) (more : j+1<calls d) :
    ∃ u,Runs .commit true o s u 2 2 0 ∧ Armed o.compression d b lane (j+1) origin u := by
  have lim:=(chain_shape d cut).2.1
  let k : Fin 15:=⟨j,by omega⟩
  let idx : Fin 16:=⟨j+1,by omega⟩
  let n:=chainStagePC (segmentPC d lane) (j+1)
  let t:=execInstrBr s (.ADDI .x6 .x29 (BitVec.ofNat 12 (j+1)))
  let u:=(tagStore t scratchBase (tagWord d idx)).setPC (t.pc+4)
  obtain ⟨small,add,store,_⟩:=(chainsites d cut lane).2 idx (by dsimp [idx];omega) more
  have ip : t.pc=pcAt (n+1) := by change s.pc+4=_;rw [before.pc,pc_succ]
  have tag : t.getReg .x6=tagWord d idx := by
    change s.getReg .x29+signExtend12 (BitVec.ofNat 12 (j+1))=_
    rw [before.ctx.tag];exact tag_advance d k
  have run₁ : Runs .commit true o s t 1 1 0 := runs_step (decoded_site (by omega) add s before.pc) rfl
  have keep₁ : Keeps s t:=fun r x _ _ _=>MachineState.getReg_setReg_ne _ _ _ _ x.symm
  have ctx:=ctx_kept before.ctx keep₁
  have addr : t.getReg .x24+signExtend12 64=BitVec.ofNat 64 (scratchBase+64) := by rw [ctx.scratch];rfl
  have run₂ : Runs .commit true o t u 1 1 0 := by
    apply runs_pure;intro fuel
    have run:=sd_run (pg:=.commit) fuel true ((decoded_site (by omega) store) t ip) (scratchBase+64) addr (by decide) (by decide)
    rw [tag] at run;exact run
  have used : unchanged s u (scratchBase+64) 8 := by
    intro x size fit apart
    apply (read_congr_mem u (tagStore t scratchBase (tagWord d idx)) _ _ rfl).trans
    apply (tag_outside t scratchBase (tagWord d idx) (by decide) (by decide) _ _ fit apart).trans
    exact read_congr_mem t s x size rfl
  let p:=2*b+lane.val
  have input := continuation_value t d k (stageReply o.compression d p origin j)
    (show ScratchPad t from ⟨(read_congr_mem t s _ _ rfl).trans before.pads.second,(read_congr_mem t s _ _ rfl).trans before.pads.last⟩)
    ((read_congr_mem t s _ _ rfl).trans before.value)
  have same : stageInput o.compression d (leftChild origin d p) (rightChild origin d p) (j+1) =
      encodeNext d (j+1) (stageReply o.compression d p origin j) := by
    unfold stageInput
    rw [parentQueries,List.getLastD_concat,workClass,if_pos (show 8≤d.val ∧ d.val<16 from cut)];rfl
  refine ⟨u,runs_comp run₁ run₂,⟨ctx_kept ctx (keeps_regs fun _=>rfl),?_,?_,?_,?_,?_,?_⟩⟩
  · change t.pc+4=_;rw [ip,pc_succ]
  · exact before.src
  · exact before.dest
  · exact (read_congr_mem u (tagStore t scratchBase (tagWord d idx)) _ _ rfl).trans (input.trans same.symm)
  · exact pads_after _ _ before.pads _ _ used (Or.inl (by omega)) (Or.inr (by omega))
  · apply outside_trans before.frame (outside_footprint used ?_)
    intro x size _ _ sep;rcases sep with a|a <;> unfold Apart <;> omega
end CommitGolfCandidate.S5Machine
