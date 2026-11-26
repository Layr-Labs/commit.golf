import CommitGolfCandidate.ReconstructedCheckLeafImage
import CommitGolfCandidate.ReconstructedCheckParentRun
import CommitGolfCandidate.ReconstructedCheckOracleMemory

namespace CommitGolfCandidate.Reconstruction.CheckLeafPlan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckParentRun CheckOracleMemory CheckProgram
set_option maxHeartbeats 6000000
set_option maxRecDepth 26000

def table : Tables where
  allowed := fun a=>decide (a.offset.toNat%8=0) && match a.region with
    | 1=>decide (a.offset.toNat<2400)
    | 2=>decide (a.offset.toNat<256)
    | _=>false
  initial := fun a=> if a=loc 1 16 then some 3633 else none

def start : State where
  pc:=CommitBlocks.addr 197
  regs:=fun r=>match r with
    | .x8=>ptr 1 2400
    | .x6 | .x17=>ptr 1 72
    | .x7=>ptr 1 328
    | .x13=>ptr 2 0
    | _=>.reg r
  writes:=[]

def arg (q : Nat) := loc 1 (if q=0 then 72 else 128)

def dst (q : Nat) := loc 1 (if q=0 then 40 else 2088)

def modelCall (q : Nat) (m : State) : State :=
  {m with pc:=m.pc+4,writes:=install (dst q) q m.writes 25}

def positionWord := Term.bin .add (.bin .add (.lit 3633) (.bin .shl (.reg .x16) (.lit 8))) (.lit 519)

def operand (q i : Nat) : Term :=
  if q=0 then .old (loc 2 (8*i))
  else if i=0 then positionWord else if i=1 then .reg .x14 else if i=2 then .reg .x15
  else if i<14 then .answer 0 (11+i) else .old (loc 2 (8*(i+7)))

def callTest (q : Nat) (m : State) : Prop :=
  m.get .x5=.lit 0 ∧ m.get .x10=.ptr (arg q) ∧ m.get .x11=.lit 200 ∧ m.get .x12=.ptr (dst q) ∧
    m.get .x13=.lit 1 ∧ ∀ i : Fin 25, look table (atIndex (arg q) i) m.writes=operand q i
deriving instance Decidable for callTest

def digestWord (i : Nat) : Term :=
  if i=3 then .bin .shr (.bin .shl (.answer 1 3) (.lit 16)) (.lit 16) else .answer 1 i

def finalTest (m : State) : Prop :=
  m.get .x12=digestWord 0 ∧ m.get .x13=digestWord 1 ∧ m.get .x14=digestWord 2 ∧ m.get .x11=digestWord 3 ∧
    (∀ a∈m.writes,a.1.region=1) ∧ m.get .x8=ptr 1 2400 ∧ m.get .x2=.reg .x2 ∧ m.get .x1=.reg .x1 ∧
    m.get .x6=ptr 1 72 ∧ m.get .x7=ptr 1 328
deriving instance Decidable for finalTest

def firstRun := run table CheckLeafImage.lookup (CommitBlocks.addr 213) 185 start
def first := firstRun.getD ⟨0,start⟩
def secondRun := run table CheckLeafImage.lookup (CommitBlocks.addr 231) 23 (modelCall 0 first.state)
def second := secondRun.getD ⟨0,start⟩
def thirdRun := run table CheckLeafImage.lookup (CommitBlocks.addr 238) 10 (modelCall 1 second.state)
def third := thirdRun.getD ⟨0,start⟩

theorem firstReceipt : firstRun.isSome=true ∧ first.ticks=171 ∧ callTest 0 first.state := by decide +kernel
theorem secondReceipt : secondRun.isSome=true ∧ second.ticks=17 ∧ callTest 1 second.state := by decide +kernel
theorem thirdReceipt : thirdRun.isSome=true ∧ third.ticks=6 ∧ finalTest third.state := by decide +kernel

end CommitGolfCandidate.Reconstruction.CheckLeafPlan
