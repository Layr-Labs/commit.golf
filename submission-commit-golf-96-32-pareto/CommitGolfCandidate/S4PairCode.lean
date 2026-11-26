import CommitGolfCandidate.S4UpperHeader
import CommitGolfCandidate.S4UpperCode
import CommitGolfCandidate.S4BatchCheckRecords
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def pairSetup := [.addi .x1 .x0 768]++li2 .x29 2048++li2 .x30 16384++[.addi .x19 .x0 171]
def pairFlags := [Sym.Calc.lbu .x3 .x1 0,.lbu .x4 .x1 1,.bor .x7 .x3 .x4]
def pairAdv := [Sym.Calc.addi .x1 .x1 2,.addi .x29 .x29 64,.addi .x30 .x30 32,.addi .x19 .x19 4095]
def selectPart (right : Bool) := if right then 4474 else 4462
def selectReg (right : Bool) := if right then Reg.x4 else .x3
def selectOffset (right : Bool) := if right then 32 else 0
def choosePtr (right : Bool) := Instr.ADDI .x15 .x29 (BitVec.ofNat 12 (selectOffset right))
def storeChild (right : Bool) := doubleCopies .x15 .x14 0 (selectOffset right) 4
structure PairSites : Prop where
  enter : (Fragment.arithmetic pairSetup).valid .check 4385 4393
  slot : Matches .check 4393 (loadCode 352 30)
  flags : (Fragment.arithmetic pairFlags).valid .check 4456 4459
  touched : conditional .check 4459 4461 .x7 .x0 false
  empty : directs .check 4460 4495
  rowPtr : stands .check 4461 (ptrCode .x14 512)
  left : Matches .check 4462 [choosePtr false]
  right : Matches .check 4474 [choosePtr true]
  choices : ∀ r : Bool,conditional .check (selectPart r+1) (selectPart r+3) (selectReg r) .x0 true ∧
    directs .check (selectPart r+2) (selectPart r+4) ∧ stands .check (selectPart r+3) (ptrCode .x15 352) ∧
    listed .check (selectPart r+4) (storeChild r)
  zero : Matches .check 4486 (zeroOps 4)
  hash : Matches .check 4490 (tableHashCode true)
  touchedEnd : directs .check 4494 4504
  unusedPtr : stands .check 4495 (ptrCode .x14 352)
  unused : Matches .check 4496 (doubleCopies .x14 .x30 0 0 4)
  advance : (Fragment.arithmetic pairAdv).valid .check 4504 4508
  finish : conditional .check 4508 4510 .x19 .x0 true
  more : directs .check 4509 4393

set_option maxRecDepth 7000 in
set_option maxHeartbeats 2000000 in
theorem pairSites : PairSites := by
  refine ⟨by decide,matchesListed (by decide),by decide,by decide,by decide,by decide,matchesListed (by decide),
    matchesListed (by decide),by decide,matchesListed (by decide),matchesListed (by decide),by decide,by decide,
    matchesListed (by decide),by decide,by decide,by decide⟩

def wireSlot (j : Nat) := proofBase+65280+30*j
def pairPC (j : Nat) := if j<171 then 4393 else 4510
structure PairCursor (H : Compression) (x : CheckInput) (s : MachineState) (j : Nat) extends Env x s : Prop where
  pc : s.pc=Late.pcAt (pairPC j)
  proof : s.getReg .x18=W (wireSlot j)
  flagsPtr : s.getReg .x1=W (flagAddr (2*j))
  children : s.getReg .x29=W (capAddr (2*j))
  dest : s.getReg .x30=W (upperAddr j)
  remaining : s.getReg .x19=W (171-j)
  seen : Seen H (readView x) 128 s
  closed : ∀ p<j,readBuffer s (upperAddr p) 32=batchCap .packed H (readView x) p

theorem pairEnter (o : Oracle) (x : CheckInput) (s : MachineState) (batch : x.positions.card=128)
    (pc : s.pc=Late.pcAt 4385) (env : Env x s) (cur : Cursor x s 128) (seen : Seen o.compression (readView x) 128 s) :
    ∃ t,CheckRuns o s t 8 0 ∧ PairCursor o.compression x t 0 := by
  let t:=Sym.evaluated pairSetup s
  obtain ⟨run,regs,mem,endPC⟩:=evalMath .check pairSetup 4385 4393 s pc pairSites.enter
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : pairSetup.all (fun c=>c.dst != .x0)=true) c h))
    (fun _ h=>by cases h)
  have keep (r : Reg) (ok : r∉[Reg.x1,.x19,.x29,.x30]):t.getReg r=s.getReg r:=outsideCalc pairSetup s t regs _ (by decide) r ok
  have safe : ∀ r : Reg,envReg r → r∉[Reg.x1,.x19,.x29,.x30]:=by intro r;cases r <;> decide
  have ptr : s.getReg .x18=W (wireSlot 0):=by
    have p:=cur.proof;rw [decide_eq_true (show x.positions.card=BATCH from batch)] at p;exact p
  exact ⟨t,ofRuns o run,⟨env.move (fun r h=>keep r (safe r h)) (env.data.regs mem),endPC,
    (keep _ (by decide)).trans ptr,(regs _).trans rfl,(regs _).trans rfl,(regs _).trans rfl,(regs _).trans rfl,
    seen.sameMem mem,fun _ h=>False.elim (by omega)⟩⟩
end CommitGolfCandidate.S4.Machine
