import CommitGolfCandidate.LateCheckObs
import CommitGolfCandidate.LateOpenWrites

namespace CommitGolfCandidate.Late.Check.Micro
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (wordAt W AddrOK Copied)

inductive Site where | middle | salt deriving DecidableEq
def Site.start : Site → Nat | .middle=>390 | .salt=>421
def Site.count : Site → Nat | .middle=>8 | .salt=>3
def Site.source : Site → Reg | .middle=>.x8 | .salt=>.x25
def Site.sOff : Site → Nat | .middle=>96 | .salt=>0
def Site.dOff : Site → Nat | .middle=>32 | .salt=>0

def Site.ld (p : Site) (j : Nat) := Instr.LD .x6 p.source (BitVec.ofNat 12 (p.sOff+8*j))
def Site.sd (p : Site) (j : Nat) := Instr.SD .x12 .x6 (BitVec.ofNat 12 (p.dOff+8*j))
def move (p : Site) (s : MachineState) (j : Nat) := execInstrBr (execInstrBr s (p.ld j)) (p.sd j)
def copies (p : Site) (s : MachineState) : Nat → MachineState
  | 0=>s | j+1=>move p (copies p s j) j

private theorem encoding (p : Site) (j : Fin 8) (hj : j.val<p.count) :
    decodeInstruction (checkWord (p.start+2*j.val))=some (.base (p.ld j.val)) ∧
    decodeInstruction (checkWord (p.start+2*j.val+1))=some (.base (p.sd j.val)) := by
  cases p <;> fin_cases j <;> first | exact ⟨rfl,rfl⟩ | contradiction

theorem move_keep (p : Site) (s : MachineState) (j : Nat) (r : Reg) (ne : Reg.x6≠r) :
    (move p s j).getReg r=s.getReg r := by
  have setReg (q : MachineState) (a v : Word) : (q.setMem a v).getReg r=q.getReg r := by cases r <;> rfl
  simp only [move,Site.sd,Site.ld,execInstrBr,MachineState.getReg_setPC,setReg,MachineState.getReg_setReg_ne _ _ _ _ ne]

private theorem offset (p : Site) (j : Fin 8) :
    signExtend12 (BitVec.ofNat 12 (p.sOff+8*j.val))=W p.sOff+W (8*j.val) ∧
    signExtend12 (BitVec.ofNat 12 (p.dOff+8*j.val))=W p.dOff+W (8*j.val) := by
  cases p <;> fin_cases j <;> exact ⟨rfl,rfl⟩

structure Pointers (p : Site) (s : MachineState) (src dst : Nat) : Prop where
  src : s.getReg p.source+W p.sOff=W src
  dst : s.getReg .x12+W p.dOff=W dst

private theorem bvaddr (p : Site) (s : MachineState) (j : Fin 8) (src dst : Nat) (reg : Pointers p s src dst) :
    s.getReg p.source+signExtend12 (BitVec.ofNat 12 (p.sOff+8*j.val))=W (src+8*j.val) ∧
    s.getReg .x12+signExtend12 (BitVec.ofNat 12 (p.dOff+8*j.val))=W (dst+8*j.val) := by
  obtain ⟨a,b⟩:=offset p j
  rw [a,b,←BitVec.add_assoc,←BitVec.add_assoc,reg.src,reg.dst]
  exact ⟨(BitVec.ofNat_add _ _).symm,(BitVec.ofNat_add _ _).symm⟩

theorem move_pc (p : Site) (s : MachineState) (j : Nat) : (move p s j).pc=s.pc+8 := by
  change s.pc+4+4=_;rw [BitVec.add_assoc];rfl

theorem copies_keep (p : Site) (s : MachineState) (n : Nat) (r : Reg) (ne : Reg.x6≠r) :
    (copies p s n).getReg r=s.getReg r := by
  induction n with
  | zero=>rfl
  | succ n ih=>exact (move_keep p _ _ _ ne).trans ih

theorem copies_ptr (p : Site) (s : MachineState) (src dst n : Nat) (ptr : Pointers p s src dst) :
    Pointers p (copies p s n) src dst := by
  constructor
  · rw [copies_keep p s n _ (by cases p <;> decide)];exact ptr.src
  · rw [copies_keep p s n _ (by decide)];exact ptr.dst

private theorem move_run (p : Site) (s : MachineState) (j : Fin 8) (hj : j.val<p.count)
    (pc : s.pc=pcAt (p.start+2*j.val)) (src dst : Nat) (ptr : Pointers p s src dst)
    (sa : AddrOK src (8*(j.val+1))) (da : AddrOK dst (8*(j.val+1))) :
    Runs s (move p s j) 2 2 := by
  obtain ⟨x,y⟩:=encoding p j hj
  obtain ⟨sp,dp⟩:=bvaddr p s j src dst ptr
  have j8:=j.isLt
  have range : p.start+2*j.val+1<433 := by cases p <;> simp only [Site.count,Site.start] at * <;> omega
  let t:=execInstrBr s (p.ld j)
  have pc' : t.pc=pcAt (p.start+2*j.val+1) := by change s.pc+4=_;rw [pc,pc_succ]
  have ok : memoryArgumentsValid s (p.ld j)=true := by
    change accessValid (_+_) 8=true;rw [sp];exact Open.access_at _ (by have :=sa.2;omega) (by have :=sa.1;omega)
  have ok' : memoryArgumentsValid t (p.sd j)=true := by
    change accessValid (s.getReg .x12+_) 8=true;rw [dp];exact Open.access_at _ (by have :=da.2;omega) (by have :=da.1;omega)
  have a : Runs s t 1 1 := one _ (by omega) _ x _ _ pc (by change (if memoryArgumentsValid s (p.ld j) then some (execInstrBr s (p.ld j)) else none)=_;rw [if_pos ok])
  have b : Runs t (move p s j) 1 1 := one _ range _ y _ _ pc' (by change (if memoryArgumentsValid t (p.sd j) then some (execInstrBr t (p.sd j)) else none)=_;rw [if_pos ok'] <;> rfl)
  exact a.trans b

theorem copies_run (p : Site) (s : MachineState) (n src dst : Nat) (pc : s.pc=pcAt p.start)
    (len : n≤p.count) (ptr : Pointers p s src dst) (sa : AddrOK src (8*n)) (da : AddrOK dst (8*n)) :
    Runs s (copies p s n) (2*n) (2*n) ∧ (copies p s n).pc=pcAt (p.start+2*n) := by
  induction n with
  | zero=> exact ⟨Runs.refl s,pc⟩
  | succ n ih=>
    have bound : n<8 := by cases p <;> simp only [Site.count] at len <;> omega
    obtain ⟨prev,pos⟩:=ih (by omega) ⟨sa.1,by have :=sa.2;omega⟩ ⟨da.1,by have :=da.2;omega⟩
    have next:=move_run p _ ⟨n,bound⟩ (show n<p.count by omega) pos src dst (copies_ptr p s src dst n ptr) sa da
    constructor
    · rw [copies,Nat.mul_succ];exact prev.trans next
    · rw [copies,move_pc,pos,show p.start+2*(n+1)=(p.start+2*n+1)+1 by omega,pc_succ,pc_succ];rw [BitVec.add_assoc];rfl

private theorem moved (p : Site) (s : MachineState) (j : Fin 8) (src dst a : Nat) (ptr : Pointers p s src dst)
    (ha : a<2^64) (hd : dst+8*j.val<2^64) :
    wordAt (move p s j) a=if a=dst+8*j.val then wordAt s (src+8*j.val) else wordAt s a := by
  obtain ⟨sp,dp⟩:=bvaddr p s j src dst ptr
  change (if W a == s.getReg .x12+signExtend12 (BitVec.ofNat 12 (p.dOff+8*j.val)) then
    s.getMem (s.getReg p.source+signExtend12 (BitVec.ofNat 12 (p.sOff+8*j.val))) else s.getMem (W a))=_
  rw [dp,sp]
  by_cases eqn : a=dst+8*j.val
  · subst a;simp [wordAt,W]
  · have ne : W a≠W (dst+8*j.val) := by
      intro eq;have z:=congrArg BitVec.toNat eq
      simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hd] at z;contradiction
    rw [if_neg (fun h=>ne (beq_iff_eq.mp h)),if_neg eqn];rfl

theorem copies_effect (p : Site) (s : MachineState) (src dst n : Nat) (small : n≤p.count)
    (ptr : Pointers p s src dst) (sa : AddrOK src (8*n)) (da : AddrOK dst (8*n)) (sep : dst+8*n≤src) :
    Copied s (copies p s n) src dst n := by
  induction n with
  | zero=>exact ⟨fun _ _ _ _=>rfl,fun j hj=>by omega⟩
  | succ n ih=>
    have bound : n<8 := by cases p <;> simp only [Site.count] at small <;> omega
    have sb:=sa.2;have db:=da.2
    have prev:=ih (by omega) ⟨sa.1,by omega⟩ ⟨da.1,by omega⟩ (by omega)
    have effect (a : Nat) (ha : a<MEMORY_BYTES) :
        wordAt (move p (copies p s n) n) a =
          if a=dst+8*n then wordAt (copies p s n) (src+8*n) else wordAt (copies p s n) a := moved p (copies p s n) ⟨n,bound⟩ src dst a
      (copies_ptr p s src dst n ptr) (by unfold MEMORY_BYTES at ha;omega) (by unfold MEMORY_BYTES at db;omega)
    constructor
    · intro a ha al out;rw [copies,effect _ ha,if_neg (by omega)];exact prev.outside a ha al (by omega)
    · intro j hj;rw [copies,effect _ (by omega)]
      by_cases e : j=n
      · subst j;rw [if_pos rfl];exact prev.outside _ (by omega) (by have :=sa.1;omega) (Or.inr (by omega))
      · rw [if_neg (by omega)];exact prev.words j (by omega)

theorem copied_read {s t : MachineState} {src dst n : Nat} (copy : Copied s t src dst n)
    (al : src%8=0) (dl : dst%8=0) : readBuffer t dst (8*n)=readBuffer s src (8*n) := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl
  intro k hk;exact congrArg (fun v : Byte=>v.toNat*2^(8*k)) (copy.data al dl k (Finset.mem_range.mp hk))

end CommitGolfCandidate.Late.Check.Micro
