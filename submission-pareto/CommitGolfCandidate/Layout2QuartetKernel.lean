import CommitGolfCandidate.Layout2QuartetCodec
import CommitGolfCandidate.Layout2Blocks
import CommitGolfCandidate.Layout2Memory
import CommitGolfCandidate.Layout2WriterSources

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 900000
set_option maxRecDepth 9000

abbrev Cell := Fin 23
def key (B : Nat) (d : Cell) : Word := addr (B+16+8*d.val)
def temp (b : Bool) : Reg := if b then .x29 else .x28

inductive Row where
  | load (b : Bool) (d : Cell)
  | store (b : Bool) (d : Cell)
deriving DecidableEq

def instruction : Row → Instr
  | .load b d => .LD (temp b) .x8 (BitVec.ofNat 12 (16+8*d.val))
  | .store b d => .SD .x8 (temp b) (BitVec.ofNat 12 (16+8*d.val))

inductive Ref where
  | cell (d : Cell)
  | old (b : Bool)
deriving DecidableEq

structure Symbolic where
  regs : Bool → Ref
  cells : Cell → Ref

def startModel : Symbolic := ⟨.old,.cell⟩
def advance (v : Symbolic) : Row → Symbolic
  | .load b d => { v with regs := fun c=>if c=b then v.cells d else v.regs c }
  | .store b d => { v with cells := fun j=>if j=d then v.regs b else v.cells j }

def value (s : MachineState) (B : Nat) : Ref → Word
  | .cell d => s.getMem (key B d)
  | .old b => s.getReg (temp b)

structure Tracks (s m : MachineState) (B : Nat) (v : Symbolic) : Prop where
  regs : ∀ b, m.getReg (temp b)=value s B (v.regs b)
  fixed : ∀ r : Reg, r≠.x28 → r≠.x29 → m.getReg r=s.getReg r
  cells : ∀ d, m.getMem (key B d)=value s B (v.cells d)
  frame : ∀ a : Word, (∀ d, a≠key B d) → m.getMem a=s.getMem a

theorem initial (s B) : Tracks s s B startModel :=
  ⟨fun _=>rfl,fun _ _ _=>rfl,fun _=>rfl,fun _ _=>rfl⟩

private theorem key_inj (B : Nat) (room : B+200≤MEMORY_BYTES) {d j : Cell} :
    key B d=key B j → d=j := by
  intro same
  have h:=congrArg BitVec.toNat same
  have lim : MEMORY_BYTES<2^64 := by decide
  have di:=d.isLt;have ji:=j.isLt
  simp only [key,addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show B+16+8*d.val<2^64 by omega),
    Nat.mod_eq_of_lt (show B+16+8*j.val<2^64 by omega)] at h
  apply Fin.ext;omega

private theorem imm : ∀ d : Cell, signExtend12 (BitVec.ofNat 12 (16+8*d.val))=addr (16+8*d.val) := by decide +kernel

theorem next_state {s m B v} (track : Tracks s m B v) (base : s.getReg .x8=addr B)
    (aligned : B%8=0) (room : B+200≤MEMORY_BYTES) (r : Row) :
    memoryArgumentsValid m (instruction r)=true ∧
      Tracks s (execInstrBr m (instruction r)) B (advance v r) := by
  have address (d : Cell) : m.getReg .x8+signExtend12 (BitVec.ofNat 12 (16+8*d.val))=key B d := by
    rw [track.fixed .x8 (by decide) (by decide),base,imm,←BitVec.ofNat_add]
    unfold key;congr 1;omega
  have valid (d : Cell) : accessValid (key B d) 8=true := by
    apply Layout2Writer.access8 <;> have h:=d.isLt <;> omega
  cases r with
  | load b d =>
    refine ⟨?_,?_⟩
    · change accessValid _ 8=true;rw [address,valid]
    · simp only [instruction,execInstrBr,address]
      refine ⟨?_,?_,?_,?_⟩
      · intro c
        by_cases e : c=b
        · subst c
          simpa [advance,MachineState.getReg_setReg_eq (show temp b≠.x0 by cases b <;> decide)] using track.cells d
        · have ne : temp b≠temp c := by cases b <;> cases c <;> simp_all [temp]
          simpa [advance,e,MachineState.getReg_setReg_ne m _ _ _ ne] using track.regs c
      · intro r f g
        have ne : temp b≠r := by cases b <;> first | exact f.symm | exact g.symm
        simpa [MachineState.getReg_setReg_ne m _ _ _ ne] using track.fixed r f g
      · intro j;cases b <;> exact track.cells j
      · intro a outside;cases b <;> exact track.frame a outside
  | store b d =>
    refine ⟨?_,?_⟩
    · change accessValid _ 8=true;rw [address,valid]
    · simp only [instruction,execInstrBr,address]
      refine ⟨track.regs,track.fixed,?_,?_⟩
      · intro j
        change (m.setMem _ _).getMem _=value s B (if j=d then v.regs b else v.cells j)
        by_cases e : j=d
        · subst j;simpa only [ite_true,MachineState.getMem_setMem_eq] using track.regs b
        · rw [if_neg e,MachineState.getMem_setMem_ne (fun h=>e (key_inj B room h))];exact track.cells j
      · intro a away
        change (m.setMem _ _).getMem a=_
        rw [MachineState.getMem_setMem_ne (away d)];exact track.frame a away

def RowsAt (I : Image) (w : Nat) (rs : List Row) :=
  ∀ i : Fin rs.length, (I.code[w+i.val]?).bind decodeInstruction=some (.base (instruction rs[i]))

theorem run_rows_kernel {s B I} (base : s.getReg .x8=addr B) (aligned : B%8=0) (room : B+200≤MEMORY_BYTES)
    (rs : List Row) (w : Nat) (m : MachineState) (v : Symbolic) (track : Tracks s m B v)
    (here : m.pc=pc w) (limit : w+rs.length<2^40) (code : RowsAt I w rs) :
    ∃ t, Runs I m t rs.length rs.length ∧ t.pc=pc (w+rs.length) ∧ Tracks s t B (rs.foldl advance v) := by
  induction rs generalizing w m v with
  | nil => exact ⟨m,runs_zero I m,here,track⟩
  | cons r rs ih =>
    obtain ⟨ok,next⟩:=next_state track base aligned room r
    have fetch:=wide_image_fetch I m w (instruction r) (by omega) here (by simpa using code ⟨0,by simp⟩)
    have step : ordinaryStep m (.base (instruction r))=some (execInstrBr m (instruction r)) := by
      cases r <;> simp only [instruction] at ok ⊢ <;> simp only [ordinaryStep,ok,ite_true]
    have one : Runs I m (execInstrBr m (instruction r)) 1 1 := by
      intro fuel;rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetch step]
      cases r <;> rfl
    have pc1 : (execInstrBr m (instruction r)).pc=pc (w+1) := by
      have e : (execInstrBr m (instruction r)).pc=m.pc+4 := by cases r <;> rfl
      rw [e,here,pc_next]
    have tail : RowsAt I (w+1) rs := by
      intro i;simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using code ⟨i.val+1,by simpa using i.isLt⟩
    obtain ⟨t,ran,pcT,frame⟩:=ih (w+1) _ _ next pc1 (by simp only [List.length_cons] at limit;omega) tail
    refine ⟨t,by simpa only [List.length_cons,Nat.add_comm 1] using one.thenDo ran,?_,frame⟩
    simpa only [List.length_cons,show w+1+rs.length=w+(rs.length+1) by omega] using pcT

end CommitGolfCandidate.Layout2.Quartet
