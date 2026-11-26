import CommitGolfCandidate.ReconstructedCheckHeaderPlan

namespace CommitGolfCandidate.Reconstruction.CheckLowerPlan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckParentRun CheckCursorImage
set_option maxRecDepth 26000
set_option maxHeartbeats 6000000

def table (width : Nat) : Tables where
  allowed:=fun a=>decide ((a.region=3 ∧ a.offset.toNat%8=0 ∧ a.offset.toNat<40) ∨
    ((a.region=5 ∨ a.region=6) ∧ a.offset=0))
  initial:=fun a=>if a=loc 5 0 then some (BitVec.ofNat 64 width) else if a=loc 6 0 then some 0xffffffff else none

def start (r : Nat) : State where
  pc:=CommitBlocks.addr 280
  regs:=fun reg=>match reg with
    | .x24=>ptr 1 r
    | .x19=>ptr 4 0
    | .x9=>ptr 5 0
    | .x8=>ptr 6 2368
    | _=>.reg reg
  writes:=[]

def run (r w : Nat) := CheckCursorOps.run (table w) (decode 280 lowerCode) (CommitBlocks.addr 350) 76 (start r)
def done (r w : Nat) := (run r w).getD ⟨0,start r⟩

def middle (r j : Nat) : Term :=
  if r=0 then CheckHeaderPlan.word j else
    .bin .bitOr (CheckHeaderPlan.shift true (CheckHeaderPlan.shift true (CheckHeaderPlan.word (j+1)) 1) (63-r))
      (CheckHeaderPlan.shift false (CheckHeaderPlan.word j) r)

def top (r w : Nat) : Term := .bin .bitAnd (CheckHeaderPlan.field (r+192) (w-192))
  (.lit (BitVec.ofNat 64 (2^(w-192)-1)))

def keep : List Reg := [.x1,.x2,.x3,.x4,.x8,.x9,.x11,.x12,.x13,.x14,.x18,.x19,.x20,.x21,.x22,.x23,.x25,.x26,.x27,.x31]

def control (r w : Nat) : Prop := let m:=(done r w).state
  m.get .x7=.lit 11 ∧ m.get .x28=.bin .add (.reg .x26) (.lit (-8)) ∧
    ∀ v ∈ keep,m.get v=(start r).get v
deriving instance Decidable for control

def receipt (r w : Nat) := let m:=(done r w).state
  (run r w).isSome && decide (m.get .x10=CheckHeaderPlan.field r 64 ∧ m.get .x16=middle r 1 ∧
    m.get .x17=middle r 2 ∧ m.get .x6=top r w ∧ m.get .x5=.lit (BitVec.ofNat 64 (w-192)) ∧
    m.get .x15=.lit (BitVec.ofNat 64 w) ∧ m.get .x24=ptr 1 (r+192) ∧ m.writes=[] ∧ (done r w).ticks≤70) && decide (control r w)

def lowWidth (d : Nat) := sameSize.lows[d]?.getD 0

end CommitGolfCandidate.Reconstruction.CheckLowerPlan
