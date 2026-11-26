import CommitGolfCandidate.ReconstructedCheckCapLowLoop

namespace CommitGolfCandidate.Reconstruction.CheckCapLow
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapLowMemory
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W cap fp scratch)
set_option maxRecDepth 17000
set_option maxHeartbeats 1300000

def keep : List Reg := [.x0,.x1,.x2,.x3,.x4,.x8,.x9,.x10,.x11,.x12,.x18,.x19,.x20,.x21,.x22,.x23,.x25,.x26,.x27]

structure Start (s : MachineState) (d c : Nat) (xs : List Nat) : Prop where
  pc : s.pc=addr 460
  cursor : s.getReg .x24=W c
  depth : s.getReg .x9=W d
  frame : s.getReg .x8=W fp
  source : s.getReg .x27=W proofBase
  total : s.getReg .x12=W xs.length
  heap : s.getReg .x23=W cap
  limit : s.getReg .x1=65

theorem start (o : Oracle) (s : MachineState) (xs : List Nat) (d c : Nat)
    (input : Start s d c xs) (small : xs.length≤512) :
    Segment o 1 s (s.setPC (addr (if xs=[] then 598 else 461))) [] := by
  have cmp:=CheckBranch.event o s 460 598 .eq .x12 .x0 552 (by decide) input.pc rfl (by decide)
  change Segment o 1 s (s.setPC (if s.getReg .x12==0#64 then addr 598 else addr 461)) [] at cmp
  rw [input.total] at cmp
  by_cases h : xs=[]
  · subst xs;exact cmp
  · have diff : W xs.length≠0#64:=by
      intro eq;have k:=congrArg BitVec.toNat eq;have pos:=List.length_pos_iff.mpr h
      change xs.length%2^64=0 at k;omega
    simp only [beq_eq_false_iff_ne.mpr diff,Bool.false_eq_true,ite_false] at cmp
    rw [ite_eq_right h];exact cmp

theorem positive (o : Oracle) (s : MachineState) (xs : List Nat) (d c w stream : Nat)
    (non : xs≠[]) (small : xs.length≤512) (depth : d≤9) (room : c+w*xs.length≤70000000000)
    (range : w=224 ∨ w=240) (input : Start s d c xs) (slots : CheckCapSlots.Contains (memoryView s) scratch xs)
    (valid : ∀ id∈xs,id<1024) (proof : Proof (memoryView s) stream)
    (table : memoryView s (CheckCapLowSetup.widthCell d)=W w) (mask : memoryView s CheckCapLowSetup.maskCell=0xffffffff) :
    ∃ n≤24+65*xs.length,∃ t,Segment o n s t [] ∧ t.pc=addr 549 ∧ t.getReg .x24=W (c+w*xs.length) ∧
      LeafMemory.Agrees (memoryView t) (fill stream w xs c (memoryView s)) ∧ (∀ q∈keep,t.getReg q=s.getReg q) := by
  have cmp:=start o s xs d c input small
  rw [ite_eq_right non] at cmp
  let s₁:=s.setPC (addr 461)
  obtain ⟨u,begin,upos,head,maskReg,size,ptr,stop,mem,stable⟩:=CheckCapLowSetup.run o s₁ ⟨d,by omega⟩
    ⟨xs.length,by omega⟩ w range rfl input.depth input.frame input.total table mask
  have get (q : Reg) (fresh : q∉CheckCapLowSetup.changed) : u.getReg q=s.getReg q:=stable q fresh
  have ctx : CheckCapLowItem.Context u proofBase c w 0 xs.length:=
    ⟨upos,(get _ (by decide)).trans input.cursor,ptr,stop,(get _ (by decide)).trans input.source,
      head,maskReg,size,(get _ (by decide)).trans input.limit,(get _ (by decide)).trans input.heap⟩
  have eq : LeafMemory.Agrees (memoryView u) (memoryView s):=mem
  have frame:=frame_of_agrees eq
  have access:=slots_frame xs small frame slots
  obtain ⟨n,time,t,body,pos,out,data,carried⟩:=CheckCapLowLoop.loop o xs u stream c w 0 xs.length non
    (Nat.zero_add _) small room range ctx (fun i=>by simpa using access i) valid (proof_frame frame proof)
  have same:=fill_agrees eq stream w c xs
  refine ⟨1+23+n,by omega,t,compose (compose cmp begin) body,pos,out,fun q hq=>(data q hq).trans (same q hq),?_⟩
  intro q member
  have ks : q∈CheckCapLowItem.keep ∧ q∉CheckCapLowSetup.changed := by
    cases q <;> first | decide | exact False.elim (by simpa [keep] using member)
  exact (carried q ks.1).trans (get q ks.2)

end CommitGolfCandidate.Reconstruction.CheckCapLow
