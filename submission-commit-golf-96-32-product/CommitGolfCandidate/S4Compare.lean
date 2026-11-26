import CommitGolfCandidate.S4BranchRun
import CommitGolfCandidate.S4Dwords
import CommitGolfCandidate.S4CheckSystem
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
inductive CompareSite | ordinary | seen | root deriving DecidableEq
def CompareSite.start : CompareSite→Nat | .ordinary=>2635 | .seen=>4364 | .root=>4836
def CompareSite.left : CompareSite→Reg | .seen=>.x1 | _=>.x14
def CompareSite.right : CompareSite→Reg | .seen=>.x15 | _=>.x27
def CompareSite.loads (p : CompareSite) (j : Nat) : List Sym.Calc :=
  [.ld .x6 p.left (BitVec.ofNat 12 (8*j)),.ld .x7 p.right (BitVec.ofNat 12 (8*j))]
def CompareSite.wordPC (p : CompareSite) (j : Nat) := p.start+4*j
private theorem sites : ∀ p : CompareSite,∀ j : Fin 4,
    let n:=p.wordPC j
    (Fragment.arithmetic (p.loads j)).valid .check n (n+2) ∧
    conditional .check (n+2) (n+4) .x6 .x7 true ∧ directs .check (n+3) 4855 ∧
    signExtend12 (BitVec.ofNat 12 (8*j.val))=W (8*j.val) := by intro p;cases p <;> decide

def sameWord (s : MachineState) (a b j : Nat) :=
  s.getMem (W (a+8*j))=s.getMem (W (b+8*j))
structure CompareContinue (o : Oracle) (s t : MachineState) (pc n : Nat) : Prop where
  run : CheckRuns o s t n 0
  pc : t.pc=pcAt pc
  mem : t.mem=s.mem
  regs : ∀ r,r≠.x6 → r≠.x7 → t.getReg r=s.getReg r

set_option maxRecDepth 3000 in
theorem compareOne (p : CompareSite) (j : Fin 4) (o : Oracle) (s : MachineState) (a b : Nat)
    (start : s.pc=pcAt (p.wordPC j)) (l : s.getReg p.left=W a) (r : s.getReg p.right=W b)
    (aok : AddrOK a 32) (bok : AddrOK b 32) :
    (sameWord s a b j ∧ ∃ t,CompareContinue o s t (p.wordPC j+4) 3) ∨
    (¬sameWord s a b j ∧ Finishes o s 7 0 .failure) := by
  let n:=p.wordPC j;let ops:=p.loads j
  obtain ⟨code,yes,no,imm⟩:=sites p j
  have neutral : ops.all (fun c=>c.dst != .x0)=true:=rfl
  have distinctL : p.left≠.x6:=by cases p <;> decide
  have distinctR : p.right≠.x6:=by cases p <;> decide
  have prior (rg : Reg) (ne : rg≠.x6) : Sym.bump Sym.original (.ld .x6 p.left (BitVec.ofNat 12 (8*j.val))) rg=Sym.original rg:=if_neg (Ne.symm ne)
  have add (rg : Reg) (addr : Nat) (base : s.getReg rg=W addr) : s.getReg rg+signExtend12 (BitVec.ofNat 12 (8*j.val))=W (addr+8*j.val):=by
    rw [base,imm];exact (BitVec.ofNat_add ..).symm
  have readAddr (rg : Reg) (addr : Nat) (base : s.getReg rg=W addr) (nz : rg≠.x0) :
      (Sym.mkOp .add (Sym.original rg) (.lit (signExtend12 (BitVec.ofNat 12 (8*j.val))))).eval s=W (addr+8*j.val):=by
    simp only [Sym.original,if_neg nz,Sym.eval_mkOp,Sym.Bin.apply,Sym.Expr.eval,add rg addr base]
  have v1:=readAddr p.left a l (by cases p <;> decide)
  have v2:=readAddr p.right b r (by cases p <;> decide)
  have access (d : Nat) (bound : AddrOK d 32) : accessValid (W (d+8*j.val)) 8=true:=by
    apply Safe.valid;have hj:=j.isLt;have da:=bound.1;have db:=bound.2;constructor <;> omega
  have safe : ∀ e∈Sym.requirements Sym.original ops,accessValid (e.1.eval s) e.2=true:=by
    intro e he
    change e∈[ (Sym.mkOp .add (Sym.original p.left) (.lit (signExtend12 (BitVec.ofNat 12 (8*j.val)))),8),
      (Sym.mkOp .add (Sym.bump Sym.original (.ld .x6 p.left (BitVec.ofNat 12 (8*j.val))) p.right)
        (.lit (signExtend12 (BitVec.ofNat 12 (8*j.val)))),8)] at he
    rw [prior _ distinctR] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · rw [v1];exact access a aok
    · rw [v2];exact access b bok
  let t:=Sym.evaluated ops s
  obtain ⟨run,regs,mem,pc⟩:=evalMath .check ops n (n+2) s start code (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp neutral c h)) safe
  have gotL : t.getReg .x6=s.getMem (W (a+8*j.val)):=by
    rw [show t.getReg .x6=((ops.foldl Sym.bump Sym.original) .x6).eval s from regs .x6]
    change s.getMem ((Sym.mkOp .add (Sym.original p.left) (.lit _)).eval s)=_;rw [v1]
  have gotR : t.getReg .x7=s.getMem (W (b+8*j.val)):=by
    rw [show t.getReg .x7=((ops.foldl Sym.bump Sym.original) .x7).eval s from regs .x7]
    change s.getMem ((Sym.mkOp .add (Sym.bump Sym.original _ p.right) (.lit _)).eval s)=_;rw [prior p.right distinctR,v2]
  have edge:=alternate .check (n+2) (n+4) 4855 .x6 .x7 true yes no rfl t pc
  have keep (reg : Reg) (h6 : reg≠.x6) (h7 : reg≠.x7) : t.getReg reg=s.getReg reg:=by
    apply (regs reg).trans
    change (Sym.bump (Sym.bump Sym.original _) (.ld .x7 p.right (BitVec.ofNat 12 (8*j.val))) reg).eval s=_
    rw [show Sym.bump (Sym.bump Sym.original _) (.ld .x7 p.right (BitVec.ofNat 12 (8*j.val))) reg=
      Sym.bump Sym.original (.ld .x6 p.left (BitVec.ofNat 12 (8*j.val))) reg from if_neg (Ne.symm h7),prior reg h6]
    cases reg <;> rfl
  by_cases eqv : sameWord s a b j
  · have cond : ((t.getReg .x6==t.getReg .x7)==true)=true:=by rw [gotL,gotR,beq_iff_eq.mpr eqv];rfl
    rw [cond] at edge
    exact Or.inl ⟨eqv,_,⟨(ofRuns o run).trans (ofRuns o edge),rfl,mem,fun reg h6 h7=>MachineState.getReg_setPC.trans (keep reg h6 h7)⟩⟩
  · have cond : ((t.getReg .x6==t.getReg .x7)==true)=false:=by rw [gotL,gotR,beq_eq_false_iff_ne.mpr eqv];rfl
    rw [cond] at edge
    exact Or.inr ⟨eqv,((ofRuns o run).trans (ofRuns o edge)).finish (verdict false _ o rfl)⟩
end CommitGolfCandidate.S4.Machine
