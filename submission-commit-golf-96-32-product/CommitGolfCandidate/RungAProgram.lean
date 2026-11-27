import CommitGolfCandidate.S4BranchRun
import CommitGolfCandidate.RungATypes
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open R4b (NRegs Agree number)
open S4.Machine (W indexBase proofBase valueBase)
open Late (nodeAddress rowAddress levelCount)
def zeroRegs : NRegs
  | .x0 | .x1 | .x3 | .x4 | .x26 | .x30 | .x31=>some 0
  | .x2=>some 68719460304 | .x14=>some valueBase | .x15=>some proofBase | .x17=>some 17179869184
  | _=>none
def abi (k : Nat) : NRegs := fun reg=> match reg with
  | .x10=>some 4096 | .x11=>some 4294971392 | .x12=>some tdAddress | .x13=>some indexBase | .x16=>some k
  | .x2=>some 68719460304 | .x14=>some valueBase | .x15=>some proofBase | .x17=>some 17179869184 | _=>some 0
def baseRegs (k r : Nat) : NRegs := fun reg=>match reg with
  | .x5=>some 0 | .x8=>some tdAddress | .x9=>some (indexBase+8*r) | .x11=>some 96 | .x13=>some 0
  | .x16=>some k | .x18=>some (k-r) | .x23=>some 24 | .x24=>some Late.rowBase | .x25=>some 184 | .x27=>some 16777216
  | _=>zeroRegs reg
def finishRegs (k : Nat) : NRegs := fun reg=>match reg with
  | .x8=>some tdAddress | .x9=>some (indexBase+8*k) | .x16=>some k | _=>zeroRegs reg
def stageRegs (k r g h : Nat) : NRegs := fun reg=>match reg with
  | .x19=>some (24*g) | .x20=>some (if h=0 then Late.rowBase+184*(12*g)+1024 else rowAddress (h-1) (baseIndex g h))
  | .x21=>some (nodeAddress h (baseIndex g h)) | .x22=>if h=0 then none else some (baseIndex g h)
  | .x6=>if h=0 then none else some (levelCount h) | _=>baseRegs k r reg
def loaded (k r i : Nat) : NRegs := fun reg=>if reg=.x19 then some i else baseRegs k r reg
def beforeHead (k r i h : Nat) := if h=0 then loaded k r i else stageRegs k r (i/24) (h-1)
def Includes (small big : NRegs) := ∀ reg n,small reg=some n → big reg=some n
theorem Agree.weaken {a b : NRegs} {s : MachineState} (h : R4b.Agree b s) (sub : Includes a b) : R4b.Agree a s :=
  fun r n eq=>h r n (sub r n eq)
def initOps : List Op := [.pos .x8 .x12 0,
  .pos .x9 .x13 0,
  .pos .x18 .x16 0]
theorem initSite : Site 17856 initOps 3 3 := by decide +kernel
def constantsOps : List Op := [.pos .x5 .x0 0,
  .pos .x11 .x0 96,
  .pos .x13 .x0 0,
  .hi .x24 352,
  .pos .x24 .x24 1,
  .shl .x24 .x24 12,
  .pos .x24 .x24 32,
  .pos .x25 .x0 184,
  .pos .x23 .x0 24,
  .hi .x27 4096]
theorem constantsSite : Site 17860 constantsOps 10 10 := by decide +kernel
def leafHeadOps : List Op := [.div .x19 .x19 .x23,
  .mul .x19 .x19 .x23,
  .shr .x6 .x19 1,
  .mul .x6 .x6 .x25,
  .add .x20 .x24 .x6,
  .pos .x20 .x20 1024,
  .shl .x6 .x19 5,
  .add .x21 .x8 .x6]
theorem leafHeadSite : Site 17871 leafHeadOps 8 17 := by decide +kernel
def oneHeadOps : List Op := [.pos .x6 .x0 3,
  .div .x22 .x19 .x6,
  .hi .x6 1365,
  .pos .x6 .x6 1366,
  .pos .x7 .x0 0,
  .add .x7 .x8 .x7,
  .pos .x28 .x0 96,
  .mul .x28 .x22 .x28,
  .add .x20 .x7 .x28,
  .hi .x7 131072,
  .pos .x7 .x7 64,
  .add .x7 .x8 .x7,
  .shr .x28 .x22 1,
  .pos .x29 .x0 96,
  .mul .x28 .x28 .x29,
  .add .x21 .x7 .x28]
theorem oneHeadSite : Site 18023 oneHeadOps 16 25 := by decide +kernel
def twoHeadOps : List Op := [.shr .x22 .x22 1,
  .hi .x6 683,
  .neg .x6 .x6 1365,
  .hi .x7 131072,
  .pos .x7 .x7 64,
  .add .x7 .x8 .x7,
  .pos .x28 .x0 96,
  .mul .x28 .x22 .x28,
  .add .x20 .x7 .x28,
  .hi .x7 196608,
  .pos .x7 .x7 96,
  .add .x7 .x8 .x7,
  .shr .x28 .x22 1,
  .pos .x29 .x0 96,
  .mul .x28 .x28 .x29,
  .add .x21 .x7 .x28]
theorem twoHeadSite : Site 18087 twoHeadOps 16 22 := by decide +kernel
def threeHeadOps : List Op := [.shr .x22 .x22 1,
  .hi .x6 341,
  .pos .x6 .x6 1366,
  .hi .x7 196608,
  .pos .x7 .x7 96,
  .add .x7 .x8 .x7,
  .pos .x28 .x0 96,
  .mul .x28 .x22 .x28,
  .add .x20 .x7 .x28,
  .hi .x7 229376,
  .pos .x7 .x7 160,
  .add .x7 .x8 .x7,
  .shr .x28 .x22 1,
  .pos .x29 .x0 96,
  .mul .x28 .x28 .x29,
  .add .x21 .x7 .x28]
theorem threeHeadSite : Site 18131 threeHeadOps 16 22 := by decide +kernel
def updateOps : List Op := [.pos .x9 .x9 8,
  .neg .x18 .x18 1]
theorem updateSite : Site 18161 updateOps 2 2 := by decide +kernel
def restoreOps : List Op := [.pos .x12 .x8 0,
  .shl .x6 .x16 3,
  .sub .x13 .x9 .x6,
  .pos .x5 .x0 0,
  .pos .x7 .x0 0,
  .pos .x8 .x0 0,
  .pos .x9 .x0 0,
  .pos .x18 .x0 0,
  .pos .x19 .x0 0,
  .pos .x20 .x0 0,
  .pos .x21 .x0 0,
  .pos .x22 .x0 0,
  .pos .x24 .x0 0,
  .pos .x25 .x0 0,
  .pos .x23 .x0 0,
  .pos .x27 .x0 0,
  .pos .x28 .x0 0,
  .pos .x29 .x0 0,
  .hi .x10 1,
  .hi .x11 256,
  .pos .x11 .x11 1,
  .shl .x11 .x11 12,
  .pos .x6 .x0 128]
theorem restoreSite : Site 18165 restoreOps 23 23 := by decide +kernel

def headOps (h : Nat) := if h=0 then leafHeadOps else if h=1 then oneHeadOps else if h=2 then twoHeadOps else threeHeadOps
def headPC (h : Nat) := if h=0 then 17871 else if h=1 then 18023 else if h=2 then 18087 else 18131
def headSteps (h : Nat) := if h=0 then 8 else 16
def headCycles (h : Nat) := if h=0 then 17 else if h=1 then 25 else 22
def firstCell (h : Nat) := headPC h+headSteps h
def cellPC (h j : Nat) := firstCell h+(if 2≤h then 7 else 6)*j
def testReg (h : Nat) := if h=0 then Reg.x6 else .x7
def limReg (h : Nat) := if h=0 then Reg.x27 else .x6
def testOps (h n : Nat) : List Op := [.pos (testReg h) (if h=0 then .x19 else .x22) n]
def originOff (n : Nat) := 184*(n/2)+88*(n%2)
def pointers (h n : Nat) : List Op :=
  [if h=0 then (if originOff n<1024 then .neg .x10 .x20 (1024-originOff n) else .pos .x10 .x20 (originOff n-1024))
    else .pos .x10 .x20 (96*n),
   .pos .x12 .x21 (if h=0 then 32*n else 96*(n/2)+32*(n%2))]
def CellROM (h n : Nat) : Prop :=
  let p:=cellPC h n
  Site p (testOps h n) 1 1 ∧ S4.Machine.stands .opening (p+1) (.BLTU (testReg h) (limReg h) 8) ∧
    S4.Machine.directs .opening (p+2) (cellPC h (n+1)) ∧ Site (p+3) (pointers h n) 2 2 ∧ hashSite (p+5) h ∧
    p+5+hashLength h=cellPC h (n+1)
instance (h n : Nat):Decidable (CellROM h n):=inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
set_option maxRecDepth 6000 in
theorem cellSite : ∀ h : Fin 4,∀ n : Fin 24,n.val<sizeAt h → CellROM h n:=by decide +kernel
theorem allHead : ∀ h : Fin 4, Site (headPC h) (headOps h) (headSteps h) (headCycles h):=by decide +kernel
theorem lastCell : ∀ h : Fin 4,cellPC h (sizeAt h)=(if h.val<3 then headPC (h+1:Nat) else 18161):=by decide
end CommitGolfCandidate.RungA
