import CommitGolfCandidate.S5ZeroInput

namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
def wordTape (ws : List PairCoins) (i : Index) : Salt :=
  pairSalts (ws[i.val/2]?.getD 0) (i.val.testBit 0)

theorem sampled_contents (m : Message) (h : Compression) (ws : List PairCoins)
    (len : ws.length = pairCount) :
    LeafContents h m (wordTape ws) 0 (applyPairs 0 (prepared m) ws) := by
  let s:=prepared m
  have a : AtPair s 0:=ready m
  have en : 0+ws.length≤pairCount := by omega
  have frame (q : MachineState) : (initializeOps.foldl execInstrBr q).mem=q.mem := rfl
  have mem:=frame (startState m)
  constructor
  · intro j hj; omega
  · intro j _
    have hi := j.isLt; change j.val < 16777216 at hi
    have endMsg : msgAddr j+256 ≤ 4294971392 := by unfold msgAddr; omega
    exact (apply_preserves_buffer ws 0 s a en _ 256 (by omega)
      (by intro p _ _; left; unfold pairAddress rowBase; omega)).trans
      ((read_congr_mem s _ _ _ mem).trans (initial_entry m j))
  · intro j _
    have hi := j.isLt; change j.val < 16777216 at hi
    have small : padAddr j+8 ≤ MEMORY_BYTES := by
      unfold padAddr rowAddr rowBase MEMORY_BYTES; split <;> omega
    have lo : 4294971392 ≤ padAddr j := by unfold padAddr rowAddr rowBase; split <;> omega
    exact (apply_preserves_buffer ws 0 s a en _ 8 (by change _ ≤ 2^36 at small; omega)
      (by intro p _ _; unfold padAddr pairAddress rowAddr rowBase; split <;> omega)).trans
      ((read_congr_mem s _ _ _ mem).trans (initial_empty m _ 8 lo small))
  · intro j
    have hi := j.isLt; change j.val < 16777216 at hi
    have l : ws.length = 8388608 := len
    simpa only [Nat.sub_zero, wordTape] using apply_reads_salt ws 0 s a en j.val (by omega) (by omega)

end CommitGolfCandidate.S5Machine
