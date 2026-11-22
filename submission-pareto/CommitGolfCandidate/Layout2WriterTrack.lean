import CommitGolfCandidate.Layout2WriterModel
namespace CommitGolfCandidate.Layout2Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Phase
set_option maxRecDepth 8000
set_option maxHeartbeats 1400000

def Free (r : Reg) := r≠.x6 ∧ r≠.x7 ∧ r≠.x10 ∧ r≠.x11 ∧ r≠.x28 ∧ r≠.x31
instance (r : Reg) : Decidable (Free r) := by unfold Free;infer_instance

private theorem reg_free (t : T) (r : Reg) (h : Free r) : t.reg≠r := by
  rcases h with ⟨a,b,c,d,e,f⟩
  cases t <;> first | exact a.symm | exact b.symm | exact c.symm | exact d.symm | exact e.symm | exact f.symm
private theorem reg_inj (t u : T) (h : t≠u) : t.reg≠u.reg := by cases t <;> cases u <;> simp_all [T.reg]

def wordAt (s : MachineState) (pos B l22 : Nat) (c : Word) (j : Nat) : Option V→Word
  | none => s.getMem (addr (B+8*j))
  | some v => denote s pos l22 c v

/-- The symbolic registers and sparse output describe the state after a writer prefix.
Every source word stays below the aligned output block. -/
structure Track (s m : MachineState) (p pos B l22 : Nat) (c : Word) (v : Model) : Prop where
  reg : ∀ t : T, m.getReg t.reg=denote s pos l22 c (v.reg t)
  fixed : ∀ r, Free r → m.getReg r=s.getReg r
  block : ∀ j, 8*j+8≤stride p → m.getMem (addr (B+8*j))=wordAt s pos B l22 c j (v.out j)
  frame : ∀ q : Word, q.toNat<B ∨ B+stride p≤q.toNat → m.getMem q=s.getMem q

theorem entry_track {s p pos B l22 c} (e : PhaseEntry s p pos B l22 c) : Track s s p pos B l22 c initial := by
  refine ⟨?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
  intro t
  cases t with
  | n => exact e.posReg
  | ptr => exact e.salt
  | c => exact e.carry
  | _ => rfl

theorem Track.readAs {s m p pos B l22 c v} (h : Track s m p pos B l22 c v) (t : T) {x : V}
    (eq : v.reg t=x) : m.getReg t.reg=denote s pos l22 c x := eq ▸ h.reg t

theorem Track.assign {s m p pos B l22 c v} (h : Track s m p pos B l22 c v) (t : T) (x : V) (physical newPC : Word)
    (same : physical=denote s pos l22 c x) :
    Track s ((m.setReg t.reg physical).setPC newPC) p pos B l22 c (changeReg v t x) := by
  have mem : ((m.setReg t.reg physical).setPC newPC).mem=m.mem := by cases t <;> rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro u
    by_cases e : u=t
    · subst u;simpa [changeReg,MachineState.getReg_setReg_eq (show t.reg≠.x0 by cases t <;> decide)] using same
    · simp [changeReg,e,MachineState.getReg_setReg_ne m _ _ physical (reg_inj t u (Ne.symm e)),h.reg]
  · intro r free;simp [MachineState.getReg_setReg_ne m _ _ physical (reg_free t r free),h.fixed r free]
  · intro j bound;simpa only [MachineState.getMem,mem,changeReg] using h.block j bound
  · intro q bound;simpa only [MachineState.getMem,mem] using h.frame q bound

theorem Track.store {s m p pos B l22 c v} (e : PhaseEntry s p pos B l22 c) (h : Track s m p pos B l22 c v)
    (j : Nat) (x : V) (physical newPC : Word) (same : physical=denote s pos l22 c x) (inside : 8*j+8≤stride p) :
    Track s ((m.setMem (addr (B+8*j)) physical).setPC newPC) p pos B l22 c (changeMem v j x) := by
  have room:=e.room.2;have ram : MEMORY_BYTES<2^64 := by decide
  have fit : B+8*j<2^64 := by omega
  refine ⟨h.reg,h.fixed,?_,?_⟩
  · intro i ib
    change (m.setMem _ physical).getMem (addr (B+8*i))=wordAt _ _ _ _ _ i (if i=j then some x else v.out i)
    by_cases eq : i=j
    · subst i;simpa only [MachineState.getMem_setMem_eq,if_pos rfl,ite_true,wordAt] using same
    · have neq : addr (B+8*i)≠addr (B+8*j) := by
        intro g
        have r:=congrArg BitVec.toNat g
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,Nat.mod_eq_of_lt (show B+8*i<2^64 by omega)] at r
        omega
      rw [MachineState.getMem_setMem_ne neq,if_neg eq];exact h.block i ib
  · intro q away
    change (m.setMem _ physical).getMem q=_
    rw [MachineState.getMem_setMem_ne]
    · exact h.frame q away
    · intro eq;rw [eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] at away;omega

theorem Track.source_word {s m p pos B l22 c v} (e : PhaseEntry s p pos B l22 c) (h : Track s m p pos B l22 c v)
    (f j : Nat) (inside : 8*j+8≤width f) :
    m.getMem (addr (fieldBase l22 pos f+8*j))=denote s pos l22 c (.data (start f+8*j)) := by
  have room:=e.room.2;have geo:=field_geometry e f;have ram : MEMORY_BYTES<2^64:=by decide
  exact (h.frame _ (Or.inl (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show fieldBase l22 pos f+8*j<2^64 by omega)];omega))).trans
    (input_word e f j inside).symm

theorem Track.pointer_word {s m p pos B l22 c v} (e : PhaseEntry s p pos B l22 c) (h : Track s m p pos B l22 c v) :
    m.getMem (addr (group pos+128))=addr l22 := by
  have bound:=e.index;have lo:=e.room.1;unfold recordBase0 at lo
  have below : group pos+128<B := by unfold group slotBase;omega
  have fit : group pos+128<2^64 := by unfold group slotBase;omega
  have ptr := e.pointer
  rw [show slotBase+1024*(pos/4)+712=group pos+128 by unfold group;omega] at ptr
  exact (h.frame _ (Or.inl (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit] using below))).trans ptr

end CommitGolfCandidate.Layout2Writer
