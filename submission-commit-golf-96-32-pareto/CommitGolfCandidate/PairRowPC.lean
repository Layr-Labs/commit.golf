import CommitGolfCandidate.PairRowCounter
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 40000

theorem latchLocation (m : MachineState) (mpc : m.pc=5364) (n : Nat) (hn : n<128) (rem : m.getReg .x27=BitVec.ofNat 64 (128-n)) :
    (nextEdge m).pc=if n+1=128 then 5376 else 5024 := by
  have values := latchValues m
  have dec := remainingDec m n hn rem
  have test : ∀ i : Fin 128, (BitVec.ofNat 64 (128-(i.val+1)) != 0#64)=decide (i.val+1 ≠ 128) := by decide
  have atPC := tailPC m mpc
  unfold nextEdge
  simp only [execInstrBr,show (recordNextState m).getReg .x0=0#64 from rfl,values.1,dec,
    test ⟨n,hn⟩,decide_eq_true_eq,atPC]
  by_cases e : n+1=128
  · simp only [e,not_true_eq_false,↓reduceIte];rfl
  · simp only [if_pos e,if_neg e];rfl

end CommitGolfCandidate.PairCap.Batch
