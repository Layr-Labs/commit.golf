import CommitGolfCandidate.S4RowValues
import CommitGolfCandidate.S4Directions
import CommitGolfCandidate.S4ZeroRow
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
abbrev untouchedFill (r : Reg) := r∉[Reg.x1,.x6,.x14,.x15,.x20]
structure FillState (o : Oracle) (s t : MachineState) (site used parent lane : Nat) (cells : Nat→Digest) : Prop where
  run : CheckRuns o s t used 0
  pc : t.pc=pcAt site
  index : t.getReg .x20=W parent
  digit : t.getReg .x1=W lane
  keep : ∀ r,untouchedFill r → t.getReg r=s.getReg r
  frame : SameOutside s t 512 96
  read : ∀ k<3,cell t k=cells k
def insertCell (cells : Nat→Digest) (k : Nat) (w : Digest) := fun a=>if a=k then w else cells a

theorem fillStart (tern : Bool) (o : Oracle) (s : MachineState) (n j : Nat) (pc : s.pc=pcAt n)
    (room : n+2≤Code.check.count) (code : Matches .check n (calcCode (digits tern)))
    (index : s.getReg .x20=W j) (small : j<2^64) (three : s.getReg .x23=3) :
    FillState o s (Sym.evaluated (digits tern) s) (n+2) 2 (j/radixOf tern) (j%radixOf tern) (cell s) := by
  obtain ⟨run,endPC,m,idx,lane,stable⟩:=digitsRun tern o s n j pc room code index small three
  refine ⟨run,endPC,idx,lane,?_,unchangedBytes m _ _,fun k _=>cellPreserved m k⟩
  intro r hr
  exact stable r (by intro e;subst r;exact hr (by decide)) (by intro e;subst r;exact hr (by decide))

theorem FillState.turn {o : Oracle} {s u : MachineState} {n steps p lane : Nat} {row : Nat→Digest}
    (f : FillState o s u n steps p lane row) (tern : Bool) (room : n+(rotate tern).length≤Code.check.count)
    (code : Matches .check n (calcCode (rotate tern))) (small : lane<radixOf tern) (three : s.getReg .x23=3) :
    FillState o s (Sym.evaluated (rotate tern) u) (n+(rotate tern).length) (steps+(rotate tern).length)
      p ((lane+1)%radixOf tern) row := by
  obtain ⟨run,pc,m,rot,keep⟩:=rotateRun tern o u n lane f.pc room code f.digit small ((f.keep _ (by decide)).trans three)
  refine ⟨f.run.trans run,pc,(keep _ (by decide)).trans f.index,rot,?_,
    bothRows f.frame (unchangedBytes m _ _),fun k h=>(cellPreserved m k).trans (f.read k h)⟩
  intro r h;exact (keep r (by intro e;subst r;exact h (by decide))).trans (f.keep r h)

theorem FillState.put {o : Oracle} {s u : MachineState} {n steps p lane : Nat} {row : Nat→Digest}
    (f : FillState o s u n steps p lane row) (src : Nat) (which : digestRegister src) (small : lane<3)
    (room : n+11≤Code.check.count) (code : Matches .check n (depositCode src)) :
    FillState o s (deposit u src) (n+11) (steps+11) p lane (insertCell row lane (readBuffer s src 32)) := by
  have d:=depositRun u n src lane which small f.pc room code f.digit
  have old : readBuffer u src 32=readBuffer s src 32:=f.frame.read (by rcases which with rfl|rfl|rfl <;> decide)
    (Or.inl (by rcases which with rfl|rfl|rfl <;> decide))
  refine ⟨f.run.trans (ofRuns o d.run),d.next,(d.keep _ (by decide) (by decide) (by decide)).trans f.index,
    (d.keep _ (by decide) (by decide) (by decide)).trans f.digit,?_,?_,?_⟩
  · intro r h
    exact (d.keep r (by intro e;subst r;exact h (by decide)) (by intro e;subst r;exact h (by decide))
      (by intro e;subst r;exact h (by decide))).trans (f.keep r h)
  · exact f.frame.combined d.moved.frame (by omega)
  · intro k hk;rw [cellWrite small d.moved k hk,old,f.read k hk];rfl
end CommitGolfCandidate.S4.Machine
