import CommitGolfCandidate.PairReject
import CommitGolfCandidate.PairRowRegs
import CommitGolfCandidate.PairRowLogic
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
attribute [local irreducible] execute Late.Check.Normal.checkEvaluation readBuffer storedAt lowerHash

theorem freshRuntime (o : Oracle) (s : MachineState) (pc : s.pc=5120) (u : Fin 256)
    (idx : s.getReg .x20=BitVec.ofNat 64 u.val) (flagZ : (bucketState s).getReg .x7=0)
    (safe : safeSteps storeOps (tested s)) : Runs o s (copied s) 26 0 := by
  unfold tested at safe
  exact pureBlockRuns (s:=s) (t:=copied s) (n:=26) (cyc:=26)
    (fun fuel=>firstWrite s pc u idx flagZ safe fuel false)
theorem seenRuntime (o : Oracle) (s : MachineState) (pc : s.pc=5120) (u : Fin 256)
    (idx : s.getReg .x20=BitVec.ofNat 64 u.val) (flagNZ : (bucketState s).getReg .x7≠0)
    (a : ∀ j<4,accessValid ((tested s).getReg .x21+BitVec.ofNat 64 (8*j)) 8)
    (b : ∀ j<4,accessValid ((tested s).getReg .x23+BitVec.ofNat 64 (8*j)) 8)
    (w : equalWords (tested s)) : Runs o s (compared s) 29 0 := by
  unfold equalWords at w
  unfold tested at a b w
  exact pureBlockRuns (s:=s) (t:=compared s) (n:=29) (cyc:=29)
    (fun fuel=>duplicateWrite s pc u idx flagNZ a b w fuel false)
end CommitGolfCandidate.PairCap.Batch
