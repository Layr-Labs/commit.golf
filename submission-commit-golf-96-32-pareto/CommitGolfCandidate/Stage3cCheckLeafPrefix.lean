import CommitGolfCandidate.Stage3cCheckCopy
import CommitGolfCandidate.Stage3cClearWords
import CommitGolfCandidate.Stage3cCheckLeafData
import CommitGolfCandidate.Stage3cCheckCalc
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside wordAt)
def leafLive (q : Reg) := q∉([.x0,.x5,.x6,.x7,.x10,.x11,.x12,.x13,.x18,.x28,.x29] : List Reg)
def LeafPreserves (s t : MachineState) := ∀ q,leafLive q → t.getReg q=s.getReg q
theorem LeafPreserves.trans {s t u} (a : LeafPreserves s t) (b : LeafPreserves t u) : LeafPreserves s u :=
  fun q h=>(b q h).trans (a q h)
def inputCopy : CopySpec := ⟨.x6,.x18,.x24,0,0⟩
structure LeafPrefix (o : Oracle) (s t : MachineState) (value : Entry) (a : Nat) (salt : Late.Salt) : Prop where
  run : Flow o s t 77 0
  pc : t.pc=pcAt 139
  value : readBuffer t leafBuf 256=value
  salt : readBuffer t saltBuf 24=salt
  zeros : ∀ j<12,wordAt t (rowBuf+8*j)=0
  advance : t.getReg .x18=W (a+256)
  keep : LeafPreserves s t
  frame : Outside s t leafBuf 352

attribute [local irreducible] readBuffer
set_option maxRecDepth 7000 in
theorem leaf_prefix (o : Oracle) (s : MachineState) (a : Nat) (v : Entry) (salt : Late.Salt)
    (pc : s.pc=pcAt 62) (msg : readBuffer s a 256=v) (random : readBuffer s saltBuf 24=salt)
    (sp : s.getReg .x18=W a) (cached : s.getReg .x24=W leafBuf) (row : s.getReg .x25=W rowBuf)
    (low : leafBuf+256≤a) (room : a+256≤MEMORY_BYTES) (al : a%8=0) : ∃ t,LeafPrefix o s t v a salt := by
  obtain ⟨u,copied⟩:=copy_words o s 62 a leafBuf 32 inputCopy (by unfold CopySites;decide +kernel)
    (by decide) (by decide) pc sp cached ⟨al,room⟩ ⟨by decide,by decide⟩ (Or.inr low)
  let z:=execInstrBr u (.ADDI .x18 .x18 256)
  have step:=one_flow o (t:=z) (show u.pc=pcAt 126 from copied.pc) (known (by decide +kernel)) (i:=.ADDI .x18 .x18 256) rfl
  have ip : z.pc=pcAt 127:=(congrArg (·+4) copied.pc).trans (pc_succ 126)
  have keepZ (r : Reg) (h : r≠.x18) : z.getReg r=u.getReg r:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm)
  have upt : z.getReg .x18=W (a+256):=(congrArg (·+signExtend12 256) ((copied.keep _ (by decide)).trans sp)).trans (BitVec.ofNat_add a 256).symm
  obtain ⟨t,zero⟩:=clear_words o z 127 rowBuf 12 .x25 (by unfold ZeroSites;decide +kernel) (by decide) ip
    ((keepZ _ (by decide)).trans ((copied.keep _ (by decide)).trans row)) (by decide) (by decide)
  have mem : z.mem=u.mem:=rfl
  have out : Outside s t leafBuf 352:=by
    intro q h aq away
    have inLeaf : q<leafBuf ∨ leafBuf+256≤q:=by omega
    have inRow : q<rowBuf ∨ rowBuf+96≤q:=by unfold rowBuf leafBuf at *;omega
    exact (zero.outside q h aq inRow).trans ((congrFun mem _).trans (copied.data.outside q h aq inLeaf))
  refine ⟨t,⟨(copied.run.trans step).trans zero.run,zero.last,?_,?_,zero.zero,(zero.regs _).trans upt,?_,out⟩⟩
  · have original : readBuffer u leafBuf 256=readBuffer s a 256:=copied_read (n:=32) (a:=a) (b:=leafBuf) copied.data al (by decide)
    exact (Open.outside_read zero.outside (by decide) (by decide) leafBuf 256 (by decide) (Or.inl (by decide))).trans
      ((read_buffer_memory_congr z u mem _ _).trans (original.trans msg))
  · exact (Open.outside_read out (by decide) (by decide) saltBuf 24 (by decide) (Or.inr (by decide))).trans random
  · intro q h;apply (zero.regs q).trans;apply (keepZ q (by intro e;subst q;apply h;decide)).trans
    apply copied.keep;intro e;subst q;apply h;decide
end CommitGolfCandidate.Chained.BinaryMachine.Check
