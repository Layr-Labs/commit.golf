import CommitGolfCandidate.Stage3cCheckRowSites
import CommitGolfCandidate.Stage3cCheckCursor
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
private theorem low_one (n : Nat) : (W n &&& 1#64)=W (n%2) := by
  change (BitVec.ofNat 64 n &&& BitVec.ofNat 64 (2^1-1))=_
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod];rfl

private theorem locator (s : MachineState) (p : RowSite) (j : Nat) (small : j<2^64)
    (idx : s.getReg .x14=W j) (gp : s.getReg .x3=3) (rp : s.getReg .x25=W rowBuf) :
    let f:=p.header.foldl Sym.bump Sym.original
    (f .x4).eval s=W (j%p.radix) ∧ (f .x14).eval s=W (j/p.radix) ∧ (f .x6).eval s=W (rowCell (j%p.radix)) := by
  have addr (lane : Nat) : s.getReg .x25+(W lane <<< 5)=W (rowCell lane):=by
    rw [rp];unfold W;rw [Open.shifted];apply (BitVec.ofNat_add ..).symm.trans;apply congrArg W;unfold rowCell;omega
  have rad : p.radix=2:=rfl
  simp only [RowSite.header,List.cons_append,List.nil_append]
  refine ⟨?_,?_,?_⟩
  · change s.getReg .x14 &&& 1#64=_;rw [idx,rad,low_one]
  · change s.getReg .x14 >>> 1=_;rw [idx,rad];exact Open.shr j 1 small
  · change s.getReg .x25+((s.getReg .x14 &&& 1#64) <<< 5)=_;rw [idx,low_one,rad];exact addr _

private theorem header_reg (p : RowSite) (s : MachineState) (q : Reg) (legal : q∉([.x4,.x6,.x14] : List Reg)) :
    ((p.header.foldl Sym.bump Sym.original) q).eval s=s.getReg q := by
  unfold RowSite.header;cases q <;> first | (exfalso;apply legal;decide) | rfl

structure Placed (o : Oracle) (s t : MachineState) (p : RowSite) (j : Nat) (v : Late.Digest) : Prop where
  run : Flow o s t 24 0
  pc : t.pc=pcAt (p.pc+24)
  digit : t.getReg .x4=W (j%p.radix)
  parent : t.getReg .x14=W (j/p.radix)
  cells : CellData t (setCell (fun _=>0) (j%p.radix) v)
  frame : RowFrame s t
  keep : ∀ q,q∉([.x4,.x6,.x7,.x14] : List Reg)→t.getReg q=s.getReg q

attribute [local irreducible] readBuffer
set_option maxRecDepth 12000 in
theorem place_digest (o : Oracle) (s : MachineState) (p : RowSite) (j : Nat) (v : Late.Digest)
    (allowed : p.allowed=true) (small : j<2^64) (pc : s.pc=pcAt p.pc) (idx : s.getReg .x14=W j)
    (gp : s.getReg .x3=3) (row : s.getReg .x25=W rowBuf) (out : s.getReg .x27=W digestBuf)
    (value : readBuffer s digestBuf 32=v) : ∃ t,Placed o s t p j v := by
  obtain ⟨z,clear⟩:=clear_words o s p.pc rowBuf 12 .x25 (row_sites p allowed).1 (by decide) pc row (by decide) (by decide)
  let u:=Sym.evaluated p.header z
  obtain ⟨math_,regs,mem,ip⟩:=Sym.compiled o p.header (p.pc+12) z clear.last (row_sites p allowed).2.1 (by
    unfold RowSite.header;change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have len : p.header.length=4:=rfl
  rw [len] at math_ ip
  have steady (q : Reg) (ok : q∉([.x4,.x6,.x14] : List Reg)) : u.getReg q=s.getReg q:=
    (regs q).trans ((header_reg p z q ok).trans (clear.regs q))
  obtain ⟨lane,up,cell⟩:=locator z p j small ((clear.regs _).trans idx) ((clear.regs _).trans gp) ((clear.regs _).trans row)
  let dest:=rowCell (j%p.radix)
  have bound : j%p.radix<3:=by unfold RowSite.radix Geo.radix;omega
  have align : dest%8=0:=by dsimp [dest,rowCell,rowBuf];omega
  have space : dest+32≤digestBuf:=by dsimp [dest,rowCell,rowBuf,digestBuf];omega
  obtain ⟨t,copy⟩:=copy_words o u (p.pc+16) digestBuf dest 4 currentCopy (row_sites p allowed).2.2.1 (by decide) (by decide) ip
    ((steady _ (by decide)).trans out) ((regs .x6).trans cell) ⟨by decide,by decide⟩ ⟨align,space.trans (by decide)⟩ (Or.inr space)
  have seen : readBuffer u digestBuf 32=v:=(read_buffer_memory_congr u z mem _ _).trans
    ((Open.outside_read clear.outside (by decide) (by decide) _ _ (by decide) (Or.inr (by decide))).trans value)
  have actual : readBuffer t dest 32=v:=(copied_read (n:=4) (a:=digestBuf) (b:=dest) copy.data (by decide) align).trans seen
  have cleared : CellData u (fun _=>0):=(blank_cells z clear.zero).same mem
  have frame : RowFrame s u:=fun q h al away=>(congrFun mem (W q)).trans (clear.outside q h al (by omega))
  refine ⟨t,⟨(clear.run.trans math_).trans copy.run,copy.pc,(copy.keep _ (by decide)).trans ((regs _).trans lane),
    (copy.keep _ (by decide)).trans ((regs _).trans up),put_cell cleared _ bound v actual copy.data.outside,
    frame.trans (RowFrame.enlarge copy.data.outside (by dsimp [dest,rowCell,currentCopy];omega) (by dsimp [dest,rowCell,currentCopy];omega)),?_⟩⟩
  intro q no;apply (copy.keep q (by change q≠.x7;intro e;subst q;simp at no)).trans
  apply steady;intro mem;apply no;cases q <;> simp_all
end CommitGolfCandidate.Chained.BinaryMachine.Check
