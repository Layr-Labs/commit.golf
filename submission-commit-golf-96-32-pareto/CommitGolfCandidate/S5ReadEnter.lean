import CommitGolfCandidate.S5ClearWords
import CommitGolfCandidate.S5ReadStore
import CommitGolfCandidate.S5ReadWordsData
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
open Check (Flow)
def enterOps : List Check.Sym.Calc:=[.addi .x12 .x10 0,.addi .x13 .x11 0]
theorem enter_field (o : Oracle) (s : MachineState) (base bytes v bit k dst n : Nat) (pc : s.pc=pcAt 21)
    (dest : s.getReg .x10=W dst) (size : s.getReg .x11=W n) (low : dst+32≤base)
    (room : base+bytes≤MEMORY_BYTES) (al : dst%8=0) (c : Cursor s base bytes v bit k) :
    ∃ t,Flow o s t 6 0 ∧ t.pc=pcAt 27 ∧ t.getReg .x12=W dst ∧ t.getReg .x13=W n ∧
      Cursor t base bytes v bit k ∧ FieldMemory t dst v bit n 0 ∧ Outside s t dst 32 ∧
      ∀ q,fieldKeep q→t.getReg q=s.getReg q := by
  obtain ⟨u,cleared⟩:=Check.clear_words o s 21 dst 4 .x10 (by unfold Check.ZeroSites;decide +kernel) (by decide) pc dest (by omega) al
  let t:=Check.Sym.evaluated enterOps u
  obtain ⟨head,regs,mem,ip⟩:=Check.Sym.compiled o enterOps 25 u cleared.last (by decide +kernel)
    (by change ∀ e∈([] : List (Check.Sym.Expr×Nat)),_;simp)
  have stable (q : Reg) (x : q≠.x12) (y : q≠.x13) : t.getReg q=s.getReg q:=by
    apply (regs q).trans;apply Eq.trans _ (cleared.regs q);cases q <;> first | rfl | contradiction
  have frame : Outside s t dst 32:=fun i b a ne=>(congrFun mem _).trans (cleared.outside i b a ne)
  have data : Source t base bytes v:=by
    intro j hj;exact (congrArg BitVec.toNat (Open.outside_byte frame al (by decide) (by omega : base+j<MEMORY_BYTES)
      (Or.inr (by omega)))).trans (c.input j hj)
  have src12 : t.getReg .x12=u.getReg .x10:=(regs .x12).trans (BitVec.add_zero _)
  have src13 : t.getReg .x13=u.getReg .x11:=(regs .x13).trans (BitVec.add_zero _)
  refine ⟨t,cleared.run.trans head,ip,src12.trans ((cleared.regs _).trans dest),src13.trans ((cleared.regs _).trans size),
    ⟨(stable _ (by decide) (by decide)).trans c.ptr,(stable _ (by decide) (by decide)).trans c.end_,
     (stable _ (by decide) (by decide)).trans c.count,(congrArg BitVec.toNat (stable _ (by decide) (by decide))).trans c.buf,c.whole,data⟩,
    ?_,frame,fun q h=>stable q h.2.1 h.2.2⟩
  intro j hj;rw [if_neg (by omega)];exact (congrFun mem _).trans (cleared.zero j hj)

theorem return_field (o : Oracle) (s : MachineState) (back : Nat) (bound : back<2336) (pc : s.pc=pcAt 61)
    (ra : s.getReg .x1=pcAt back) : Flow o s (s.setPC (pcAt back)) 1 0 := by
  apply Check.one_flow o pc (Check.known (by decide +kernel)) (i:=.JALR .x0 .x1 0)
  change some (s.setPC ((s.getReg .x1+signExtend12 0) &&& ~~~1#64))=_
  rw [ra,show signExtend12 0=0#64 by rfl,BitVec.add_zero, (by decide +kernel : ∀ i : Fin 2336,pcAt i.val &&& ~~~1#64=pcAt i.val) ⟨back,bound⟩]

end CommitGolfCandidate.S5Machine.Reader
