import CommitGolfCandidate.TruncBCursor
import CommitGolfCandidate.TruncBBranches
import CommitGolfCandidate.TruncBAccess
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 40000

attribute [local irreducible] pairLatch pairNextState
theorem nextPair {H : Compression} {input : CheckInput} {p : Nat} (small : p<128)
    {s t : MachineState} (inv : PairInvariant H input p s) (eff : PairEffect H input p s t) :
    PairInvariant H input (p+1) (pairLatch t) := by
  have ctl := latchControl t eff.pc p small ((eff.keep .x27 (by decide)).trans inv.remaining)
  have mem := latchMemory t
  have quiet : AreaQuiet s (pairLatch t) p := fun a b c d => (byteMem mem a).trans (eff.quiet a b c d)
  exact nextFrame small inv
    (latchCursor (s:=s) (t:=t) (v:=pairNextState t) (u:=pairLatch t) inv eff.keep ctl (advanceRegs t))
    quiet ((memDigest (s:=t) (t:=pairLatch t) mem (outSlot p)).trans eff.result)
end CommitGolfCandidate.Trunc.Batch
