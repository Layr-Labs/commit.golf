import CommitGolfCandidate.R4bRows
import CommitGolfCandidate.R4bImage
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Open (initial resumeState setup)
open Machine (W Runs proofBase indexBase byte)
open Late (pcAt)

theorem enter (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128) (start : MachineState) (ready : Open.ReadyAtOne td ps start) :
    ∃ s,Runs .opening start s 44 44 ∧ s.pc=pcAt 16401 ∧ Frame td ps 0 0 s := by
  let u:=resumeState start ps.card
  have pre:=Open.resumeMode ps start ready.pc (ready.regs .x16) (ready.regs .x6)
  have regs (r : Reg) (ne : r≠.x6) : u.getReg r=(initial td ps).getReg r :=
    (ready.regs r).trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have at3 : u.pc=pcAt 3:=by simp [u,resumeState,Open.modePC,batch,MachineState.setPC]
  have jump:=Machine.jump .opening 3 16359 u at3 (by decide)
  let v:=u.setPC (pcAt 16359)
  obtain ⟨run,atEnd,same,ptr,three,ix,buf,flags,_⟩:=Open.entrySetup true v rfl
  let w:=setup true v
  have wb : w.getReg .x15=W proofBase:=buf.trans (by exact (regs .x15 (by decide)).trans rfl)
  have wo : w.getReg .x19=W proofBase:=ptr.trans (by exact (regs .x15 (by decide)).trans rfl)
  have wi : w.getReg .x13=W indexBase:=ix.trans (by exact (regs .x13 (by decide)).trans rfl)
  obtain ⟨flag,one,_⟩:=flags rfl
  obtain ⟨code,nz,noReads,len,cycles⟩:=initValid
  obtain ⟨steps,spec,memEnd,endPC⟩:=Machine.evalMath .opening initOps 16364 16401 w atEnd code
    (fun op h=>bne_iff_ne.mp (List.all_eq_true.mp nz op h)) (by intro a ha;rw [noReads] at ha;cases ha)
  let t:=Machine.Sym.evaluated initOps w
  have get (r : Reg) : t.getReg r=(setupValue r).eval w:=(spec r).trans (congrArg (Machine.Sym.Expr.eval w) (initRegs r))
  have memEq : t.mem=start.mem:=memEnd.trans same
  have consts : Agree (fixed 0) t:=by
    intro r n h;rw [get];cases r <;> simp only [fixed,Option.some.injEq,reduceCtorEq] at h
    all_goals subst n;first | rfl | exact wi | exact three
  have source : Open.Sources td ps t := ready.sources.sameMem memEq
  have eqByte (a : Nat) : byte t a = byte start a:=by simp only [byte,MachineState.getByte,MachineState.getMem,memEq]
  have mk : Open.Marked ps 0 t:=fun j h=>(eqByte _).trans ((ready.bytes _ (by omega)).trans (Open.initialFlags td ps j h))
  rw [len,cycles] at steps
  rw [Open.resumeSteps,if_pos batch] at pre
  refine ⟨t,((pre.trans jump).trans run).trans steps,endPC,⟨consts,(get _).trans wo,get .x9,(get _).trans flag,
     (get _).trans one,(get _).trans wb,source,tableOfBytes (initialTable td ps) (fun a _ hi=>(eqByte a).trans (ready.bytes a (by unfold tableBase at hi;omega))),mk,?_⟩⟩
  exact ⟨fun j h=>by change j<0 at h;omega,fun h=>False.elim (h rfl)⟩
end CommitGolfCandidate.R4b
