import CommitGolfCandidate.ReconstructedCheckCapFrames

namespace CommitGolfCandidate.Reconstruction.CheckCapLevelRead
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CommitBlocks CheckCapLevel
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W cap fp scratch flag)
open HonestCapPlan (pairs)
set_option maxRecDepth 18000
set_option maxHeartbeats 1400000

structure Post (f : Nat→Bool) (stream d c : Nat) (s t : MachineState) (m : Memory) : Prop where
  pc : t.pc=addr (if (parsed f d stream c m).valid then 598 else 672)
  static : CheckParentControl.Context t (W (parsed f d stream c m).cursor)
  depth : t.getReg .x9=W d
  firstParent : t.getReg .x10=W (pairs d)
  firstChild : t.getReg .x11=W (2^d)
  marks : t.getReg .x19=flag (pairs d)
  limit : t.getReg .x20=W (2^(d+1))
  head : t.getReg .x25=W (2^d)
  radix : t.getReg .x21=211
  magic : t.getReg .x26=W CheckGroupRadix.magic
  proof : t.getReg .x27=W CheckCapLowMemory.proofBase
  table : Data t stream
  rows : HonestSizeRows.Rows f d (pairs d) t
  cells : ∀ id,id<1024→node t id=view (parsed f d stream c m).data id
  frame : Frame s t
  base : Bases m s

theorem limit (f : Nat→Bool) (d : Nat) : (CapSchedule.pending f d).length≤pairs d := by
  rw [CapSchedule.pending,CapOrder.prefix_length];exact HonestDepthPair.size f d (pairs d)

theorem deps (f : Nat→Bool) (d : Nat) (pos : 0<d) (max : d≤9) (id : Nat) (member : id∈CapSchedule.pending f d) : id<1024 := by
  have k:=CapOrder.id_cell f d pos max id member
  have t : 2^(d+1)≤2^10:=Nat.pow_le_pow_right (by decide) (by omega)
  exact lt_of_lt_of_le k.2.2 t

theorem load_bound (f : Nat→Bool) (d : Nat) (max : d≤9) (w : Nat) (range : w=224 ∨ w=240) :
    w*(CapSchedule.pending f d).length+31*CheckGroupPlan.groups (CapSchedule.pending f d)≤70000 := by
  have pop:=limit f d
  have h : pairs d≤2^8:=Nat.pow_le_pow_right (by decide) (by omega)
  change pairs d≤256 at h
  unfold CheckGroupPlan.groups
  rcases range with rfl|rfl <;> omega

theorem run (o : Oracle) (f : Nat→Bool) (stream d c : Nat) (s : MachineState)
    (pos : 0<d) (max : d≤9) (room : c+70000*d≤70000000000) (start : Boundary f stream d c s) :
    ∃ n t m,n≤46+128*pairs d ∧ Segment o n s t [] ∧ Post f stream d c s t m := by
  let xs:=CapSchedule.pending f d
  let w:=Encoding.lows d
  let cur:=start.ready.static
  have startPC : s.pc=addr 425:=by simpa only [ite_eq_right (by omega : d≠0)] using start.ready.pc
  obtain ⟨k,scanTime,u,scan,exit⟩:=CheckCapScan.run o s f d pos max startPC start.ready.one start.ready.two start.ready.depth
    cur.scratch (start.rows pos)
  have keepU (r : Reg) (hr : r∉CheckCapScan.written) : u.getReg r=s.getReg r:=exit.registers r hr
  have frameU:=CheckCapFrames.scan exit.frame
  have dataU:=CheckCapFrames.data frameU start.data
  have input : CheckCapLow.Start u d c xs:=⟨exit.pc,(keepU _ (by decide)).trans cur.bits,
    (keepU _ (by decide)).trans start.ready.depth,(keepU _ (by decide)).trans cur.fp,(keepU _ (by decide)).trans start.proof,
    exit.count,(keepU _ (by decide)).trans cur.heap,(keepU _ (by decide)).trans cur.one⟩
  have size : pairs d≤256:=Nat.pow_le_pow_right (by decide : 0<2) (by omega : d-1≤8)
  have len : xs.length≤pairs d:=limit f d
  have width:=CheckCapRepair.width d pos max
  have bits:=load_bound f d max w width
  have small : c+70000≤70000000000:=by omega
  obtain ⟨n,parseTime,t,parse,atPc,bit,scratchReg,mem,keep⟩:=CheckCapPrepare.run o u xs d c w stream
    (by omega) max (by dsimp [xs];omega) width input exit.ids (deps f d pos max) dataU.proof (dataU.widths d pos max)
    dataU.mask ((keepU _ (by decide)).trans cur.scratch) ((keepU _ (by decide)).trans start.magic)
    ((keepU _ (by decide)).trans start.radix)
  have frameT:=CheckCapFrames.parsed (deps f d pos max) mem
  have frame : Frame u t:=fun q hq v=>frameT q hq v.1
  refine ⟨k+n,t,memoryView u,by omega,compose scan parse,atPc,⟨(keep _ (by decide)).trans input.limit,
    (keep _ (by decide)).trans ((keepU _ (by decide)).trans cur.sp),(keep _ (by decide)).trans input.frame,
    (keep _ (by decide)).trans input.heap,bit,scratchReg⟩,(keep _ (by decide)).trans input.depth,
    (keep _ (by decide)).trans exit.parentId,(keep _ (by decide)).trans exit.firstId,(keep _ (by decide)).trans exit.firstParent,
    (keep _ (by decide)).trans exit.endIdx,(keep _ (by decide)).trans exit.startIdx,
    (keep _ (by decide)).trans ((keepU _ (by decide)).trans start.radix),
    (keep _ (by decide)).trans ((keepU _ (by decide)).trans start.magic),(keep _ (by decide)).trans input.source,
    CheckCapFrames.data frame dataU,HonestSizeRows.carry exit.flags size (fun i hi=>(CheckCapFrames.parsed_flag frameT i hi).symm),
    fun id hi=>(CheckCapPhysical.physical t id).trans (CheckCapPhysical.agrees hi mem),
    CheckCapFrames.trans frameU frame,CheckCapFrames.bases exit.frame⟩

end CommitGolfCandidate.Reconstruction.CheckCapLevelRead
