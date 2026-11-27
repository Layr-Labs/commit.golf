import CommitGolfCandidate.Stage3cCheckChainInit
import CommitGolfCandidate.Stage3cCheckEdges
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Open (W)
private theorem prep_unchanged (s : MachineState) (q : Reg) (h : q∉([.x5,.x6,.x11,.x13] : List Reg)) :
    (prepared s).getReg q=s.getReg q := by
  apply reg_path
  cases q <;> first | decide | (exfalso;apply h;decide)

structure ChainEntry (o : Oracle) (s t : MachineState) (h : Height) (dst : Nat) : Prop where
  run : Flow o s t 17 0
  pc : t.pc=pcAt 192
  sys : ChainSys h dst t
  level : t.getReg .x29=W (h.val+1)
  source : t.getReg .x10=W rowBuf
  scratch : ScratchFields t
  pad : readBuffer t (rowBuf+72) 24=0
  left : readBuffer t rowBuf 32=readBuffer s rowBuf 32
  right : readBuffer t (rowBuf+32) 32=readBuffer s (rowBuf+32) 32
  keep : ParentPreserves s t
  frame : ChainOutside s t dst

attribute [local irreducible] readBuffer
theorem chain_entry (o : Oracle) (s : MachineState) (h : Height) (dst : Nat) (more : 1<calls h)
    (pc : s.pc=pcAt 173) (count : s.getReg .x30=W (calls h)) (width : s.getReg .x31=W (wireWidth h))
    (level : s.getReg .x29=W (h.val+1)) (src : s.getReg .x10=W rowBuf) (dest : s.getReg .x12=W dst)
    (scratch : s.getReg .x26=W chainBuf) : ∃ t,ChainEntry o s t h dst := by
  let u:=prepared s
  have flag : (s.getReg .x30 != 1)=true:=by
    rw [count];exact (by decide +kernel : ∀ k : Height,1<calls k → (W (calls k) != 1)=true) h more
  obtain ⟨ready,ip,mem,sys,mode,len,src',dst',w⟩:=prepare_parent s pc true flag
  have head : Flow o s u 5 0:=path_flow o (code:=prepare) (by decide +kernel) ready
  let z:=(u.setReg .x28 (W dst)).setPC (pcAt 181)
  have save:=imm_step o u 180 .x28 .x12 0 (W dst) ip (known (by decide +kernel)) (by
    rw [show signExtend12 0=0#64 by rfl,BitVec.add_zero];exact dst'.trans dest)
  have keepZ (q : Reg) (ne : q≠.x28) : z.getReg q=u.getReg q:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have prev:=fun q (hq : q∉([.x5,.x6,.x11,.x13,.x28] : List Reg))=>
    (keepZ q (by intro e;subst q;simp at hq)).trans (prep_unchanged s q (by intro mem;apply hq;cases q <;> simp_all))
  obtain ⟨t,clear,ep,regs,pads,empty,l,r,frame⟩:=chain_zero o z dst rfl ((prev .x26 (by decide)).trans scratch)
    ((keepZ _ (by decide)).trans (src'.trans src))
  have reg (q : Reg) (h : q∉([.x5,.x6,.x11,.x13,.x28] : List Reg)):t.getReg q=s.getReg q:=(regs q).trans (prev q h)
  have same : z.mem=s.mem:=mem
  refine ⟨t,⟨(head.trans save).trans clear,ep,⟨(reg _ (by decide)).trans scratch,(regs _).trans
    (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_eq (by decide))),
    (reg _ (by decide)).trans width,(reg _ (by decide)).trans count,
    (regs _).trans ((keepZ _ (by decide)).trans sys),(regs _).trans ((keepZ _ (by decide)).trans len),
    (regs _).trans ((keepZ _ (by decide)).trans mode)⟩,(reg _ (by decide)).trans level,(reg _ (by decide)).trans src,
    pads,empty,l.trans (read_buffer_memory_congr _ _ same _ _),r.trans (read_buffer_memory_congr _ _ same _ _),?_,
    (ChainOutside.same same).trans frame⟩⟩
  intro q live;apply reg;cases q <;> simp_all only [parentLive,List.mem_cons,List.not_mem_nil,or_false,not_or] <;> tauto
end CommitGolfCandidate.Chained.BinaryMachine.Check
