import CommitGolfCandidate.PairAdvanceFacts
import CommitGolfCandidate.PairBranches
import CommitGolfCandidate.PairAccess
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 40000

structure PairCursor (n : Nat) (s : MachineState) : Prop where
  pc : s.pc=if n=128 then 7348 else 6892
  slots : s.getReg .x19=BitVec.ofNat 64 (inSlot n)
  marks : s.getReg .x22=BitVec.ofNat 64 (flag (2*n))
  source : s.getReg .x23=BitVec.ofNat 64 (sourceRow n)
  dest : s.getReg .x24=BitVec.ofNat 64 (outSlot n)
  root : s.getReg .x26=4294971392
  remaining : s.getReg .x27=BitVec.ofNat 64 (128-n)

theorem nextFrame {H : Compression} {input : CheckInput} {p : Nat} (small : p<128)
    {s u : MachineState} (inv : PairInvariant H input p s) (cursor : PairCursor (p+1) u)
    (quiet : AreaQuiet s u p) (result : digestAt u (outSlot p)=parentAt H input p) :
    PairInvariant H input (p+1) u := by
  refine ⟨by omega,cursor.pc,cursor.slots,cursor.marks,cursor.source,cursor.dest,cursor.root,cursor.remaining,?_,?_,?_,?_,?_,?_⟩
  · exact (areaDigest quiet (a:=4294971392) (by decide) (rootSpan p small).1 (rootSpan p small).2).trans inv.rootDigest
  · intro v hv
    have ab : p<(leftId v).val/2 := by change p<2*v.val/2;omega
    exact (oldCellAfter p small quiet (leftId v) ab).trans (inv.left v (by omega))
  · intro v hv
    have ab : p<(rightId v).val/2 := by change p<(2*v.val+1)/2;omega
    exact (oldCellAfter p small quiet (rightId v) ab).trans (inv.right v (by omega))
  · intro v hv
    obtain ⟨b,c,d⟩:=gapSpan p small v (by omega)
    exact (areaDigest quiet b c d).trans (inv.gap v (by omega))
  · intro v hv
    obtain ⟨b,c,d⟩:=proofSpan p small v
    rw [areaRead 30 quiet b c d];exact inv.ins v (by omega)
  · intro v hv
    by_cases eqn : v.val=p
    · rw [eqn,capTable,if_pos small];exact result
    · have lt : v.val<p := by omega
      obtain ⟨b,c,d⟩:=priorSpan p small v lt
      exact (areaDigest quiet b c d).trans (inv.outs v lt)
end CommitGolfCandidate.PairCap.Batch
