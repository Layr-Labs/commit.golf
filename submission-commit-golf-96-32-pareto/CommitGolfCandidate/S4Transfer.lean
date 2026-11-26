import CommitGolfCandidate.S4WideMove
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ)

inductive Width | byte | unsignedByte | half | word | dword deriving DecidableEq
def Width.size : Width→Nat | .byte | .unsignedByte=>1 | .half=>2 | .word=>4 | .dword=>8
def Width.ld (w : Width) (r : Reg) (i : BitVec 12) :=
  match w with
  | .unsignedByte=>Instr.LBU .x6 r i | .byte=>Instr.LB .x6 r i | .half=>Instr.LH .x6 r i
  | .word=>Instr.LW .x6 r i | .dword=>Instr.LD .x6 r i
def Width.st (w : Width) (r : Reg) (i : BitVec 12) :=
  match w with
  | .unsignedByte | .byte=>Instr.SB r .x6 i | .half=>Instr.SH r .x6 i | .word=>Instr.SW r .x6 i | .dword=>Instr.SD r .x6 i
def Width.copy (w : Width) (s : MachineState) (src dst : Nat) :=
  match w with
  | .byte | .unsignedByte=>copyByte s src dst | .half=>copyHalf s src dst | .word=>copyWord s src dst | .dword=>copyDword s src dst

def Safe (a n : Nat) := a+n≤MEMORY_BYTES ∧ a%n=0
theorem Safe.valid {a n : Nat} (ok : Safe a n) : accessValid (W a) n=true := by
  have sr:=ok.1;unfold MEMORY_BYTES at sr
  simp only [accessValid,rangeValid,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<2^64),ok.1,ok.2,decide_true,Bool.true_and]
theorem Width.moved (w : Width) (s : MachineState) (a b : Nat) (src : Safe a w.size) (dst : Safe b w.size) :
    Moved s (w.copy s a b) a b w.size := by
  have bs:=src.1;have bd:=dst.1;unfold MEMORY_BYTES at bs bd
  cases w with
  | byte | unsignedByte=>exact movedByte _ _ _ (by omega)
  | half=>exact movedHalf _ _ _ (by simpa only [Width.size] using bs.trans (by decide)) (by simpa only [Width.size] using bd.trans (by decide)) src.2 dst.2
  | word=>exact movedWord _ _ _ (bd.trans (by decide)) src.2 dst.2
  | dword=>exact movedDword _ _ _ (bd.trans (by decide)) src.2 dst.2

def transfer (w : Width) (sr dr : Reg) (si di : BitVec 12) (s : MachineState) :=
  execInstrBr (execInstrBr s (w.ld sr si)) (w.st dr di)

theorem transferPC (w : Width) (sr dr : Reg) (si di : BitVec 12) (s : MachineState) (n : Nat) (pc : s.pc=pcAt n) :
    (transfer w sr dr si di s).pc=pcAt (n+2) := by
  cases w <;> change s.pc+4+4=_ <;> rw [pc,←pc_succ,←pc_succ]

private theorem storeRegs (s : MachineState) (a : Word) (v : Word) (r : Reg) : (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl
theorem transferRegs (w : Width) (sr dr : Reg) (si di : BitVec 12) (s : MachineState) (r : Reg) (ne : Reg.x6≠r) :
    (transfer w sr dr si di s).getReg r=s.getReg r := by
  cases w <;> simp only [transfer,Width.ld,Width.st,execInstrBr,MachineState.getReg_setPC,MachineState.setByte,
    MachineState.setHalfword,MachineState.setWord32,storeRegs,MachineState.getReg_setReg_ne _ _ _ _ ne]

private theorem narrowSigned {n : Nat} (w : BitVec n) (hn : n≤64) : (w.signExtend 64).setWidth n=w := by
  ext i hi;simp [BitVec.getElem_signExtend,show i<64 by omega,hi]

theorem transferMem (w : Width) (sr dr : Reg) (si di : BitVec 12) (s : MachineState) (a b : Nat)
    (ne : Reg.x6≠dr) (src : s.getReg sr+signExtend12 si=W a) (dst : s.getReg dr+signExtend12 di=W b) :
    (transfer w sr dr si di s).mem=(w.copy s a b).mem := by
  cases w <;> simp only [transfer,Width.ld,Width.st,Width.copy,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ ne,MachineState.getReg_setReg_eq (by decide : Reg.x6≠.x0),src,dst,
    copyByte,copyHalf,copyWord,copyDword,byte] <;> simp [narrowSigned] <;> rfl

theorem transferRun (c : Code) (w : Width) (sr dr : Reg) (si di : BitVec 12) (s : MachineState) (n a b : Nat)
    (ne : Reg.x6≠dr) (pc : s.pc=pcAt n) (limit : n+2≤c.count)
    (enc1 : decodeInstruction (c.word n)=some (.base (w.ld sr si)))
    (enc2 : decodeInstruction (c.word (n+1))=some (.base (w.st dr di)))
    (src : s.getReg sr+signExtend12 si=W a) (dst : s.getReg dr+signExtend12 di=W b)
    (sa : Safe a w.size) (da : Safe b w.size) : Runs c s (transfer w sr dr si di s) 2 2 := by
  let t:=execInstrBr s (w.ld sr si)
  have sstep : ordinaryStep s (.base (w.ld sr si))=some t := by
    have safe : memoryArgumentsValid s (w.ld sr si)=true:=by cases w <;> change accessValid (s.getReg sr+signExtend12 si) _=true <;> rw [src] <;> exact sa.valid
    cases w <;> simp only [Width.ld] at safe <;> simp only [Width.ld,ordinaryStep,if_pos safe] <;> rfl
  have keep : t.getReg dr=s.getReg dr:=by cases w <;> simp only [t,Width.ld,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ ne]
  have dstep : ordinaryStep t (.base (w.st dr di))=some (transfer w sr dr si di s) := by
    have safe : memoryArgumentsValid t (w.st dr di)=true:=by
      have e : t.getReg dr+signExtend12 di=W b:=by rw [keep,dst]
      cases w <;> change accessValid (t.getReg dr+signExtend12 di) _=true <;> rw [e] <;> exact da.valid
    cases w <;> simp only [Width.st] at safe <;> simp only [Width.st,ordinaryStep,if_pos safe] <;> rfl
  have next : t.pc=pcAt (n+1):=by cases w <;> change s.pc+4=_ <;> rw [pc,pc_succ]
  have l:=one (by omega) pc _ enc1 sstep
  have r:=one (by omega) next _ enc2 dstep
  have la : instructionCycles (.base (w.ld sr si))=1:=by cases w <;> rfl
  have rb : instructionCycles (.base (w.st dr di))=1:=by cases w <;> rfl
  rw [la] at l;rw [rb] at r;exact l.trans r
end CommitGolfCandidate.S4.Machine
