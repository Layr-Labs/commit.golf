import CommitGolfCandidate.Stage3cChainArm
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
theorem reply_pc {bits : Nat} (s : MachineState) (a : Word) (v : BitVec bits) : (writeBits s a v).pc=s.pc+4 := rfl
attribute [local irreducible] readBuffer writeBits stageInput

theorem middle_round (o : Oracle) {d b lane j origin s} (f : ChainFrame o.compression d b lane j origin s)
    (cut : chained d) (more : j+2<calls d) :
    ∃ t,Runs .commit true o s t 3 10 1 ∧ ChainFrame o.compression d b lane (j+1) origin t := by
  obtain ⟨u,prep,a⟩:=arm_stage o f cut (by omega)
  let idx : Fin 16:=⟨j+1,by have :=(chain_shape d cut).2.1;omega⟩
  obtain ⟨small,_,_,raw⟩:=(chainsites d cut lane).2 idx (by dsimp [idx];omega) (by dsimp [idx];omega)
  have nlast : idx.val+1≠calls d:=by dsimp [idx];omega
  rw [if_neg nlast] at raw
  let answer:=stageReply o.compression d (2*b+lane.val) origin (j+1)
  let t:=writeBits u (BitVec.ofNat 64 scratchBase) answer
  have run : Runs .commit true o u t 1 8 1 := by
    intro fuel
    have law:=hash_fixed .commit true o u fuel scratchBase scratchBase ((decoded_site (by omega) raw) u a.pc)
      a.ctx.mode a.ctx.len a.ctx.kind a.src a.dest (by decide) (by decide) (by decide) (by decide)
    rw [a.input] at law;exact law
  have kept : ∀ r,t.getReg r=u.getReg r:=fun r=>writeBits_register u _ answer r
  have store:=store_outside u scratchBase answer (by decide)
  refine ⟨t,runs_comp prep run,⟨ctx_kept a.ctx (keeps_regs kept),?_,(kept _).trans a.src,(kept _).trans a.dest,
    written u scratchBase answer,?_,?_⟩⟩
  · rw [show t.pc=u.pc+4 from reply_pc ..,a.pc,pc_succ];apply congrArg pcAt;unfold chainStagePC;omega
  · exact pads_after u t a.pads _ _ store (Or.inr (by omega)) (Or.inr (by omega))
  · apply outside_trans a.frame (outside_footprint store ?_)
    intro x n _ _ sep;rcases sep with l|r <;> unfold Apart <;> omega

theorem middles (o : Oracle) {d b lane origin} (cut : chained d) (n j : Nat) (s : MachineState)
    (f : ChainFrame o.compression d b lane j origin s) (enough : j+n+1<calls d) :
    ∃ t,Runs .commit true o s t (3*n) (10*n) n ∧ ChainFrame o.compression d b lane (j+n) origin t := by
  induction n generalizing j s with
  | zero=>exact ⟨s,by simpa using runs_id .commit true o s,by simpa using f⟩
  | succ n ih=>
    obtain ⟨u,head,next⟩:=middle_round o f cut (by omega)
    obtain ⟨t,tail,last⟩:=ih (j+1) u next (by omega)
    have eqn : j+(n+1)=j+1+n:=by omega
    rw [eqn];refine ⟨t,?_,last⟩
    have total:=runs_comp head tail;convert total using 1 <;> omega
end CommitGolfCandidate.Chained.BinaryMachine
