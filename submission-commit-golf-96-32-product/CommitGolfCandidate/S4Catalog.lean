import CommitGolfCandidate.S4Edges
import CommitGolfCandidate.S4Expressions
import CommitGolfCandidate.S4CopyBlock
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

structure Burst where
  sr : Reg
  dr : Reg
  si : Nat
  di : Nat
  widths : List Width

inductive Fragment
  | arithmetic (ops : List Sym.Calc)
  | copy (part : Burst)
  | single (instr : Instr)

def Fragment.words : Fragment→List Instr
  | .arithmetic ops=>ops.map Sym.Calc.instr
  | .copy part=>moveCode part.sr part.dr part.si part.di part.widths
  | .single op=>[op]

def listed (c : Code) (pc : Nat) (ops : List Instr) : Bool :=
  (List.finRange ops.length).all (fun j=>stands c (pc+j.val) ops[j.val])
theorem matchesListed {c : Code} {pc : Nat} {ops : List Instr} (h : listed c pc ops) : Matches c pc ops := by
  intro i bi
  apply stood
  exact List.all_eq_true.mp h ⟨i,bi⟩ (List.mem_finRange ..)

def Fragment.valid (f : Fragment) (c : Code) (a b : Nat) : Bool :=
  decide (a+f.words.length=b ∧ b≤c.count) && listed c a f.words

theorem Fragment.code {f : Fragment} {c : Code} {a b : Nat} (h : f.valid c a b) :
    a+f.words.length=b ∧ b≤c.count ∧ Matches c a f.words := by
  obtain ⟨edge,words⟩:=Bool.and_eq_true_iff.mp h
  exact ⟨(of_decide_eq_true edge).1,(of_decide_eq_true edge).2,matchesListed words⟩

theorem evalMath (c : Code) (ops : List Sym.Calc) (pc stop : Nat) (s : MachineState)
    (start : s.pc=pcAt pc) (valid : (Fragment.arithmetic ops).valid c pc stop)
    (live : ∀ x∈ops,x.dst≠.x0) (safe : ∀ a∈Sym.requirements Sym.original ops,accessValid (a.1.eval s) a.2=true) :
    let t:=Sym.evaluated ops s
    Runs c s t ops.length (Sym.price ops) ∧ (∀ r,t.getReg r=((ops.foldl Sym.bump Sym.original) r).eval s) ∧
    t.mem=s.mem ∧ t.pc=pcAt stop := by
  obtain ⟨eqv,lim,code⟩:=Fragment.code valid
  simp only [Fragment.words,List.length_map] at eqv
  have pos : Sym.live s s Sym.original:=by intro r;cases r <;> rfl
  have h:=Sym.evaluate_block c ops pc s s Sym.original pos rfl start (by omega) live safe (fun i bi=>by
    have e:=code i (by simpa only [Fragment.words,List.length_map] using bi)
    simpa only [Fragment.words,List.getElem_map] using e)
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.trans (congrArg pcAt eqv)⟩

theorem evalCopy (c : Code) (p : Burst) (pc stop src dst : Nat) (s : MachineState)
    (start : s.pc=pcAt pc) (valid : (Fragment.copy p).valid c pc stop)
    (sr : Reg.x6≠p.sr) (dr : Reg.x6≠p.dr) (srcPtr : s.getReg p.sr=W src) (dstPtr : s.getReg p.dr=W dst)
    (align : validOffsets src dst p.si p.di p.widths) (bound : src+p.si+bytesOf p.widths≤MEMORY_BYTES)
    (apart : src+p.si+bytesOf p.widths≤dst+p.di ∨ dst+p.di+bytesOf p.widths≤src+p.si) :
    AfterCopy c pc s (copyBlock p.sr p.dr p.si p.di p.widths s) (src+p.si) (dst+p.di) (bytesOf p.widths) (2*p.widths.length) := by
  obtain ⟨edge,lim,eqv⟩:=Fragment.code valid
  rw [Fragment.words,moveCodeLen] at edge
  exact copyBlockRun c p.sr p.dr src dst p.si p.di pc p.widths s sr dr srcPtr dstPtr start (by omega) align bound apart eqv
end CommitGolfCandidate.S4.Machine
