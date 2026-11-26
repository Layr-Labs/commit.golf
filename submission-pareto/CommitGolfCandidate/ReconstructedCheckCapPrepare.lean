import CommitGolfCandidate.ReconstructedCheckCapLow
import CommitGolfCandidate.ReconstructedCheckCapRepair

namespace CommitGolfCandidate.Reconstruction.CheckCapPrepare
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckCapLowMemory
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W fp scratch cap)
set_option maxRecDepth 17000
set_option maxHeartbeats 1400000

def keep : List Reg := [.x0,.x1,.x2,.x3,.x4,.x8,.x9,.x10,.x11,.x12,.x18,.x19,.x20,.x21,.x22,.x23,.x25,.x26,.x27]

theorem run (o : Oracle) (s : MachineState) (xs : List Nat) (d c w stream : Nat)
    (small : xs.length≤512) (depth : d≤9) (room : c+w*xs.length+31*CheckGroupPlan.groups xs≤70000000000)
    (range : w=224 ∨ w=240) (input : CheckCapLow.Start s d c xs) (slots : CheckCapSlots.Contains (memoryView s) scratch xs)
    (valid : ∀ id∈xs,id<1024) (proof : Proof (memoryView s) stream)
    (table : memoryView s (CheckCapLowSetup.widthCell d)=W w) (mask : memoryView s CheckCapLowSetup.maskCell=0xffffffff)
    (scratchReg : s.getReg .x29=W scratch) (magic : s.getReg .x26=W CheckGroupRadix.magic) (radix : s.getReg .x21=211) :
    let out:=CheckCapRepair.result d w (memoryView s) xs stream c
    ∃ n≤29+110*xs.length,∃ t,Segment o n s t [] ∧ t.pc=addr (if out.valid then 598 else 672) ∧
      t.getReg .x24=W out.cursor ∧ t.getReg .x29=W scratch ∧ LeafMemory.Agrees (memoryView t) out.data ∧
      ∀ q∈keep,t.getReg q=s.getReg q := by
  dsimp only
  by_cases empty : xs=[]
  · subst xs
    rw [CheckCapRepair.nil_result]
    have j:=CheckCapLow.start o s [] d c input (by decide)
    exact ⟨1,by decide,_,j,rfl,input.cursor,scratchReg,fun _ _=>rfl,fun _ _=>rfl⟩
  · obtain ⟨n,time,u,body,pos,cur,low,saved⟩:=CheckCapLow.positive o s xs d c w stream empty small depth
      (by omega) range input slots valid proof table mask
    let m:=fill stream w xs c (memoryView s)
    let h:=c+w*xs.length
    have eq : LeafMemory.Agrees (memoryView u) m:=low
    have untouched:=trans (fill_frame (memoryView s) xs stream c w valid) (frame_of_agrees low)
    have tape:=proof_frame untouched proof
    have inputs : CheckGroupFrame.Sources u proofBase stream h xs:=by
      intro i hi;exact source u stream (h+31*i) (by unfold h;omega) tape
    obtain ⟨k,t,time',full,endAt,stop,rest,mem,kt⟩:=CheckCapHeaders.run o u xs d fp proofBase stream h empty small depth pos
      ((saved _ (by decide)).trans input.depth) ((saved _ (by decide)).trans input.frame) (by decide)
      ((saved _ (by decide)).trans input.total) cur ((saved _ (by decide)).trans input.source)
      (fun _=>inputs) (by decide) (slots_frame xs small untouched slots) (by decide)
      (by change 68719473368+4*xs.length≤68719476736;omega) (by decide) valid ((saved _ (by decide)).trans input.heap)
      ((saved _ (by decide)).trans radix) ((saved _ (by decide)).trans magic)
    have agree:=CheckCapRepair.result_congr d (memoryView u) m xs stream h eq
    rw [agree.success] at endAt
    rw [agree.position] at stop
    refine ⟨n+k,by omega,t,compose body full,endAt,stop,rest,fun i hi=>(mem i hi).trans (agree.data i hi),?_⟩
    intro q member
    have regs : q∉CheckCapHeaders.changed ∧ q∈CheckCapLow.keep := by
      cases q <;> first | decide | exact False.elim (by simpa [keep] using member)
    exact (kt q regs.1).trans (saved q regs.2)

end CommitGolfCandidate.Reconstruction.CheckCapPrepare
