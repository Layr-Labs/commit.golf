import CommitGolfCandidate.ReconstructedCheckCapScanStart
import CommitGolfCandidate.ReconstructedCheckCapScanLoop
import CommitGolfCandidate.ReconstructedCapSchedule

namespace CommitGolfCandidate.Reconstruction.CheckCapScan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks
open CheckCapScanData (W flag scratch Frame)
open HonestCapPlan (pairs)
open HonestSizeRows (Rows)
open TwoPermutationPrototype.RV64 (memoryView)
set_option maxRecDepth 15000
set_option maxHeartbeats 1400000

def written := CheckCapScanPair.changed ++ CheckCapScanStart.shifts.map Prod.fst ++ CheckCapScanStart.setup.map Prod.fst

structure Exit (s t : MachineState) (f : Nat→Bool) (d : Nat) : Prop where
  pc : t.pc=addr 460
  count : t.getReg .x12=W (CapSchedule.pending f d).length
  startIdx : t.getReg .x25=W (2^d)
  endIdx : t.getReg .x20=W (2^(d+1))
  parentId : t.getReg .x10=W (pairs d)
  firstId : t.getReg .x11=W (2^d)
  firstParent : t.getReg .x19=flag (pairs d)
  flags : Rows f d (pairs d) t
  ids : CheckCapSlots.Contains (memoryView t) scratch (CapSchedule.pending f d)
  frame : Frame s t
  registers : ∀ r∉written,t.getReg r=s.getReg r

/-- Each occupied pair propagates its parent flag and records its missing sibling in increasing heap order. -/
theorem run (o : Oracle) (s : MachineState) (f : Nat→Bool) (d : Nat) (pos : 0<d) (max : d≤9)
    (pc : s.pc=addr 425) (unit : s.getReg .x18=1) (two : s.getReg .x22=2) (depth : s.getReg .x9=W d)
    (scratchPtr : s.getReg .x29=W scratch) (rows : Rows f d 0 s) :
    ∃ n≤17+18*pairs d,∃ t,Segment o n s t [] ∧ Exit s t f d := by
  let u:=CheckCapScanStart.result s
  obtain ⟨start,upos,umem,regs,keep⟩:=CheckCapScanStart.positive o s d pos max pc unit two depth
  have narrow : pairs d≤256:=by
    change 2^(d-1)≤2^8;exact Nat.pow_le_pow_right (by decide) (by omega)
  have nonempty : 0<pairs d:=Nat.two_pow_pos _
  have rowsU : Rows f d 0 u:=HonestSizeRows.carry rows narrow
    (fun k _ => CheckCapScanFlags.copiedByte s u umem _)
  have base : CheckCapScanLoop.Inv f d 0 u:=by
    refine ⟨by simpa only [CheckCapScanLoop.here,ite_eq_left nonempty] using upos,
      regs.index,regs.count,regs.lo,regs.hi,regs.parent,regs.endIdx,
      (keep _ (by decide)).trans unit,(keep _ (by decide)).trans scratchPtr,rowsU,?_⟩
    intro j;exact j.elim0
  obtain ⟨n,size,t,loop,done,frame,carried⟩:=CheckCapScanLoop.through o f d pos narrow u base (pairs d) (by omega)
  refine ⟨17+n,by omega,t,compose start loop,?_,?_,(carried _ (by decide)).trans regs.beginIdx,done.top,
    (carried _ (by decide)).trans regs.parentId,(carried _ (by decide)).trans regs.firstId,
    (carried _ (by decide)).trans regs.firstParent,done.rows,done.slots,?_,?_⟩
  · simpa only [CheckCapScanLoop.here,Nat.lt_irrefl,ite_false] using done.pc
  · unfold CapSchedule.pending;rw [CapOrder.prefix_length];exact done.count
  · intro a af ar;exact (frame a af ar).trans (congrFun umem a)
  · intro q fresh
    simp only [written,List.mem_append,not_or] at fresh
    exact (carried q fresh.1.1).trans (keep q (by simpa only [List.mem_append,not_or] using And.intro fresh.1.2 fresh.2))

end CommitGolfCandidate.Reconstruction.CheckCapScan
