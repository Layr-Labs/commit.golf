import CommitGolfCandidate.Stage3cMachineTag
import CommitGolfCandidate.Stage3cGates
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option Elab.async false

def segmentWords (d : Height) :=3*calls d+6
def segmentPC (d : Height) (lane : Fin 2) :=mainPC d+segmentWords d*lane.val
def fromLane (lane : Fin 2) :=96*lane.val
def toLane (lane : Fin 2) :=32*lane.val
def chainStagePC (start j : Nat) :=start+5+3*(j-1)
def maskPC (d : Height) (lane : Fin 2) :=segmentPC d lane+3*calls d+3
def exitPairPC (d : Height) :=mainPC d+2*segmentWords d

def FirstSites (d : Height) (lane : Fin 2) : Prop :=
  let n:=segmentPC d lane
  n+4<11543 ∧ decoded n=some (.base (.SD .x21 .x29 (BitVec.ofNat 12 (fromLane lane+64)))) ∧
    decoded (n+1)=some (.base (.ADDI .x10 .x21 (BitVec.ofNat 12 (fromLane lane)))) ∧
    decoded (n+2)=some (.base (.ADDI .x12 .x24 0)) ∧ decoded (n+3)=some (.base .ECALL) ∧
    decoded (n+4)=some (.base (.ADDI .x10 .x24 0))
instance (d lane) : Decidable (FirstSites d lane) := by unfold FirstSites;infer_instance

def LaterSites (d : Height) (lane : Fin 2) (j : Nat) : Prop :=
  let n:=chainStagePC (segmentPC d lane) j
  n+3<11543 ∧ decoded n=some (.base (.ADDI .x6 .x29 (BitVec.ofNat 12 j))) ∧ decoded (n+1)=some (.base (.SD .x24 .x6 64)) ∧
  if j+1=calls d then decoded (n+2)=some (.base (.ADDI .x12 .x22 (BitVec.ofNat 12 (toLane lane)))) ∧ decoded (n+3)=some (.base .ECALL)
  else decoded (n+2)=some (.base .ECALL)
instance (d lane j) : Decidable (LaterSites d lane j) := by unfold LaterSites;infer_instance

theorem chainsites : ∀ d : Height,chained d → ∀ i : Fin 2, FirstSites d i ∧
    ∀ j : Fin 16, 0<j.val → j.val<calls d → LaterSites d i j.val := by decide +kernel

def MaskSites (n : Nat) : Prop :=
  n+2<11543 ∧ decoded n=some (.base (.LHU .x31 .x12 28)) ∧
    decoded (n+1)=some (.base (.AND .x31 .x31 .x30)) ∧ decoded (n+2)=some (.base (.SW .x12 .x31 28))
instance (n : Nat) : Decidable (MaskSites n) := by unfold MaskSites;infer_instance

theorem mask_sites : ∀ d : Height,chained d → ∀ i : Fin 2, MaskSites (maskPC d i) := by decide +kernel

theorem chain_shape : ∀ d : Height,chained d →
    2≤calls d ∧ calls d≤16 ∧ 224≤wireWidth d ∧ wireWidth d≤240 ∧
    count d%2=0 ∧ 0<count d ∧ tiles d=count d/2 ∧
    exitPairPC d+4=passEnd d := by decide +kernel

theorem pair_updates : ∀ d : Height,chained d →
    let n:=exitPairPC d
    n+2<11543 ∧ decoded n=some (.base (.ADDI .x21 .x21 192)) ∧
      decoded (n+1)=some (.base (.ADDI .x22 .x22 96)) ∧ decoded (n+2)=some (.base (.ADDI .x20 .x20 4095)) := by decide +kernel

theorem small_signed : ∀ j : Fin 128, signExtend12 (BitVec.ofNat 12 j.val) = BitVec.ofNat 64 j.val := by decide +kernel

end CommitGolfCandidate.Chained.BinaryMachine
