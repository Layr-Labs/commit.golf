import CommitGolfCandidate.S4EdgeSites
import CommitGolfCandidate.S4CheckSystem
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

abbrev conditional (c : Code) (site destPC : Nat) (a b : Reg) (equal : Bool) :=
  let e : Control:=⟨site,destPC,if equal then .eqv else .neq,a,b⟩
  e.valid c

theorem branch (c : Code) (site destPC : Nat) (a b : Reg) (equal : Bool) (valid : conditional c site destPC a b equal)
    (s : MachineState) (pc : s.pc=pcAt site) :
    Runs c s (s.setPC (pcAt (if ((s.getReg a==s.getReg b)==equal) then destPC else site+1))) 1 1 := by
  let e : Control:=⟨site,destPC,if equal then .eqv else .neq,a,b⟩
  have h:=e.run c s pc valid
  have same : e.taken s=((s.getReg a==s.getReg b)==equal):=by
    cases equal <;> simp [e,Control.taken,bne]
  simpa only [Control.dest,same,e] using h

abbrev directs (c : Code) (site destPC : Nat) := (⟨site,destPC,.jump,.x0,.x0⟩ : Control).valid c
theorem jump (c : Code) (site destPC : Nat) (s : MachineState) (pc : s.pc=pcAt site) (v : directs c site destPC) :
    Runs c s (s.setPC (pcAt destPC)) 1 1 :=
  (⟨site,destPC,.jump,.x0,.x0⟩ : Control).run c s pc v

theorem alternate (c : Code) (site yes no : Nat) (a b : Reg) (equal : Bool)
    (short : conditional c site (site+2) a b equal) (far : directs c (site+1) no)
    (yesPC : yes=site+2) (s : MachineState) (pc : s.pc=pcAt site) :
    let choose:=((s.getReg a==s.getReg b)==equal)
    Runs c s (s.setPC (pcAt (if choose then yes else no))) (if choose then 1 else 2) (if choose then 1 else 2) := by
  have first:=branch c site (site+2) a b equal short s pc
  by_cases pick : ((s.getReg a==s.getReg b)==equal)=true
  · simpa only [pick,ite_true,yesPC] using first
  · have f : Runs c s (s.setPC (pcAt (site+1))) 1 1:=by simpa only [if_neg pick] using first
    have both:=f.trans (jump c (site+1) no (s.setPC (pcAt (site+1))) rfl far)
    simp only [if_neg pick];exact both
end CommitGolfCandidate.S4.Machine
