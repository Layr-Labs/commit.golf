import CommitGolfCandidate.Stage3cRngDraws
import CommitGolfCandidate.Stage3cMemory
import CommitGolfCandidate.Stage3cChainBlock

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] writeBits

private theorem add_mem (q : MachineState) (dst src : Reg) (imm : BitVec 12) :
    (execInstrBr q (.ADDI dst src imm)).mem = q.mem := by cases dst <;> rfl



theorem next_memory (p : Nat) (s : MachineState) (w : PairCoins) :
    (nextPair p s w).mem = (writeBits s (s.getReg .x10) w).mem := by
  let r := randomStep s w
  have step : r.mem = (writeBits s (s.getReg .x10) w).mem := add_mem _ .x10 .x10 184
  by_cases e : p%2048 = 2047
  · change (if p%2048 = 2047 then latchState r p else r).mem = _
    rw [if_pos e]
    exact (add_mem r .x20 .x20 4095).trans step
  · simpa only [nextPair, if_neg e] using step

theorem read_next (p : Nat) (s : MachineState) (w : PairCoins) (r n : Nat) (a : AtPair s p) :
    readBuffer (nextPair p s w) r n =
      readBuffer (writeBits s (BitVec.ofNat 64 (pairAddress p)) w) r n :=
  read_congr_mem _ _ _ _ ((next_memory p s w).trans
    (congrArg (fun addr => (writeBits s addr w).mem) a.dest))

end CommitGolfCandidate.Chained.BinaryMachine
