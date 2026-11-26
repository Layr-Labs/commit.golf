import CommitGolfCandidate.PairRowPC
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 40000

attribute [local irreducible] nextEdge storeState top_checkRootWordsState

theorem foldFinish (b : Bool) (s : MachineState) : finishRow b s=nextEdge (postBody b s) := by cases b <;> simp only [finishRow,postBody,copied,compared,cmpDone,tested,Bool.false_eq_true,if_false,if_true]

end CommitGolfCandidate.PairCap.Batch
