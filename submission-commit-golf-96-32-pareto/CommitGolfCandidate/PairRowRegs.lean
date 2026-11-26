import CommitGolfCandidate.PairRowLatch
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 250000

attribute [local irreducible] postBody finishRow nextEdge rowHash

theorem postRegs (o : Oracle) (input : CheckInput) (n : Nat) (hn : n<128) (s : MachineState)
    (h : HashedFrame o input n s) (fresh : Bool)
    (flagged : fresh = decide ((bucketState s).getReg .x7=0))
    (agree : fresh=false → ∀ j<4, (tested s).getMem ((tested s).getReg .x21+BitVec.ofNat 64 (8*j)) =
                              (tested s).getMem ((tested s).getReg .x23+BitVec.ofNat 64 (8*j))) :
    NextRegs (n+1) (finishRow fresh s) := by
  let m := postBody fresh s
  have mpc : m.pc=5364 := bodyPC s fresh h.pc _ h.index flagged agree
  have keep := bodyKeeps fresh s
  have rem : m.getReg .x27=BitVec.ofNat 64 (128-n) := (keep .x27 (by decide)).trans h.remaining
  have ip : m.getReg .x24+8#64=BitVec.ofNat 64 (6442455072+8*(n+1)) := by
    have ipEq : m.getReg .x24=s.getReg .x24 := keep .x24 (by decide)
    rw [ipEq,h.ip,show 6442455072+8*(n+1)=(6442455072+8*n)+8 by omega]
    exact (BitVec.ofNat_add _ 8).symm
  rw [foldFinish]
  exact ⟨latchLocation m mpc n hn rem,(latchIp m).trans ip,
    (latchKept m .x8 (by decide)).trans ((keep .x8 (by decide)).trans h.vp),
    (latchKept m .x25 (by decide)).trans ((keep .x25 (by decide)).trans h.pp),
    (latchRem m).trans (remainingDec m n hn rem),
    (latchKept m .x21 (by decide)).trans ((keep .x21 (by decide)).trans h.scratch),
    (latchKept m .x30 (by decide)).trans ((keep .x30 (by decide)).trans h.depth),
    (latchKept m .x19 (by decide)).trans ((keep .x19 (by decide)).trans h.slots),
    (latchKept m .x26 (by decide)).trans ((keep .x26 (by decide)).trans h.root)⟩
end CommitGolfCandidate.PairCap.Batch
