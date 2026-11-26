import CommitGolfCandidate.R4Header
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt rowAddress nodeAddress fillLevel layerHash)

def blocks (d : Width) := nodes d/groupSize d
def tailSize (d : Width) := nodes d%groupSize d
def branchPC (d : Width) := bodyPC d + groupSize d*laneWidth d
def branchImm (d : Width) := BitVec.ofInt 13 (-((4*(groupSize d*laneWidth d) : Nat) : Int))
def closedPC (d : Width) := bank d true
def endSize (d : Width) := (header d).length

structure Frame (o : Oracle) (base : MachineState) (d : Width) (p : Nat) (s : MachineState) extends Pointers d p s : Prop where
  limit : 0<bulkCount d → s.getReg .x19=Z (rowAddress d (bulkCount d))
  memory : s.mem=(fillLevel (layerHash o.compression d) d p base).mem

private theorem numbers (d : Width) : groupSize d%2=0 ∧ 0<groupSize d ∧
    blocks d*groupSize d+tailSize d=nodes d ∧ closedPC d+tailSize d*laneWidth d=endPC d ∧
    rowAddress d (bulkCount d)<2^64 ∧ (0<blocks d →
    LongSite (branchPC d) (bodyPC d) ∧ branchPC d+3=closedPC d) := by
  revert d;decide +kernel

theorem bankCount (d : Width) : bulkCount d+tailSize d=nodes d := (numbers d).2.2.1
private theorem writeCongr (o : Oracle) (d : Width) (p : Nat) (s t : MachineState) (eqm : s.mem=t.mem) :
    (Late.writeParent (layerHash o.compression d) s d p).mem=(Late.writeParent (layerHash o.compression d) t d p).mem := by
  unfold Late.writeParent Late.compressAt Late.store
  rw [readBuffer_of_mem_eq eqm]
  exact write_bits_memory_congr _ _ _ _ eqm

theorem bankRun (o : Oracle) (base s : MachineState) (d : Width) (tail : Bool) (p k : Nat)
    (even : p%2=0) (bound : k≤bankSize d tail) (room : p+k≤nodes d)
    (pc : s.pc=pcAt (bank d tail)) (frame : Frame o base d p s) :
    ∃ t,MRun o s (k*laneWidth d) t (k*(laneWidth d+7)) k ∧ t.pc=pcAt (lane d tail k) ∧ Frame o base d (p+k) t := by
  induction k with
  | zero=>exact ⟨s,by simp only [Nat.zero_mul];exact DetRun.refl o (submission.image .commit) s,by simpa [lane] using pc,frame⟩
  | succ k ih=>
    obtain ⟨u,run,ip,f⟩:=ih (by omega) (by omega)
    have align : destInc k=destInc (p+k):=by unfold destInc;rw [Nat.add_mod,even,Nat.zero_add,Nat.mod_mod]
    have enc:=laneCode (laneListed d k tail (by omega))
    rw [align] at enc
    obtain ⟨t,last,next,ptr,limit,mem⟩:=laneRun o u _ _ d (by omega) f.toPointers ip enc
    refine ⟨t,by simpa only [Nat.succ_mul] using run.trans last,?_,⟨ptr,fun yes=>limit.trans (f.limit yes),
      mem.trans (writeCongr _ _ _ _ _ f.memory)⟩⟩
    exact next.trans (congrArg pcAt (by simp [lane,Nat.succ_mul,Nat.add_assoc]))

private theorem afterBlock (o : Oracle) (base s : MachineState) (d : Width) (q : Nat) (lt : q<blocks d)
    (f : Frame o base d ((q+1)*groupSize d) s) (pc : s.pc=pcAt (branchPC d)) :
    ∃ t,MRun o s 2 t 2 0 ∧ (t.pc=pcAt (if q+1<blocks d then bodyPC d else closedPC d)) ∧ Frame o base d ((q+1)*groupSize d) t := by
  have geom:=numbers d
  have bulk : 0<bulkCount d:=Nat.mul_pos (by omega : 0<blocks d) geom.2.1
  obtain ⟨enc,falls⟩:=geom.2.2.2.2.2 (by omega)
  have cmp : (s.getReg .x10 != s.getReg .x19)=decide (q+1<blocks d):=by
    rw [f.src,f.limit bulk]
    have lim:=geom.2.2.2.2.1
    have le:=Nat.mul_le_mul_right (groupSize d) (by omega : q+1≤blocks d)
    change (q+1)*groupSize d≤bulkCount d at le
    have smaller : rowAddress d ((q+1)*groupSize d)<2^64:=by unfold rowAddress at *;omega
    by_cases yes : q+1<blocks d
    · have less:=Nat.mul_lt_mul_of_pos_right yes geom.2.1
      change (q+1)*groupSize d<bulkCount d at less
      have diff : Z (rowAddress d ((q+1)*groupSize d))≠Z (rowAddress d (bulkCount d)):=by
        intro h;have h':=congrArg BitVec.toNat h
        simp only [Z,BitVec.toNat_ofNat,Nat.mod_eq_of_lt smaller,Nat.mod_eq_of_lt lim] at h'
        unfold rowAddress at h';omega
      simp [yes,diff]
    · have eq : q+1=blocks d:=by omega
      simp [eq,bulkCount,blocks]
  let t := latchResult s (bodyPC d) (branchPC d+3)
  refine ⟨t,longRun o s _ _ enc pc,?_,⟨⟨⟨f.mode,f.kind,f.width,f.root⟩,f.src,f.dst,f.mask⟩,f.limit,f.memory⟩⟩
  change lpc (if s.getReg .x10 != s.getReg .x19 then bodyPC d else branchPC d+3)=_
  rw [cmp,falls]
  by_cases yes : q+1<blocks d <;> simp [yes,lpc,Late.pcAt]

def blockSteps (d : Width) := groupSize d*laneWidth d+2
def blockCycles (d : Width) := groupSize d*(laneWidth d+7)+2
theorem bulkRun (o : Oracle) (base s : MachineState) (d : Width) (q : Nat) (hq : q≤blocks d)
    (pc : s.pc=pcAt (bodyPC d)) (f : Frame o base d 0 s) :
    ∃ t,MRun o s (q*blockSteps d) t (q*blockCycles d) (q*groupSize d) ∧
      t.pc=pcAt (if q<blocks d then bodyPC d else closedPC d) ∧ Frame o base d (q*groupSize d) t := by
  induction q with
  | zero=>
    have init : (if 0<blocks d then bodyPC d else closedPC d)=bodyPC d:=by
      by_cases yes:0<blocks d
      · simp [yes]
      · have z : bulkCount d=0:=by change blocks d*groupSize d=0;rw [show blocks d=0 by omega,Nat.zero_mul]
        simp [yes,closedPC,bank,z]
    simp only [Nat.zero_mul,init];exact ⟨s,DetRun.refl o (submission.image .commit) s,pc,f⟩
  | succ q ih=>
    have lt : q<blocks d:=by omega
    obtain ⟨u,run,ip,frame⟩:=ih lt.le
    rw [if_pos lt] at ip
    have pos : 0<bulkCount d:=Nat.mul_pos (by omega : 0<blocks d) (numbers d).2.1
    have even : (q*groupSize d)%2=0:=by rw [Nat.mul_mod,(numbers d).1,Nat.mul_zero,Nat.zero_mod]
    have space := Nat.mul_le_mul_right (groupSize d) hq
    have avail : q*groupSize d+groupSize d≤nodes d:=by rw [Nat.succ_mul] at space;have:=bankCount d;change _≤bulkCount d at space;omega
    obtain ⟨v,body,edge,full⟩:=bankRun o base u d false (q*groupSize d) (groupSize d) even (by simp [bankSize,pos]) avail
      (by simpa [bank] using ip) frame
    rw [←Nat.succ_mul] at full
    obtain ⟨t,latch,next,done⟩:=afterBlock o base v d q lt full (by simpa [lane,bank,branchPC] using edge)
    refine ⟨t,?_,next,done⟩
    simpa only [Nat.succ_mul,blockSteps,blockCycles,Nat.add_assoc,Nat.add_zero] using (run.trans body).trans latch

end CommitGolfCandidate.R4
