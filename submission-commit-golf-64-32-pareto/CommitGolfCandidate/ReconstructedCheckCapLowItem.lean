import CommitGolfCandidate.ReconstructedCheckCapLowRead
import CommitGolfCandidate.ReconstructedCheckCapLowStore

namespace CommitGolfCandidate.Reconstruction.CheckCapLowItem
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W scratch cap)
open CheckCapLowStore (copy cell)
set_option maxRecDepth 15500
set_option maxHeartbeats 1700000

def reader (proof c : Nat) : CheckStream.Reader:=⟨proof,c/64,0,0⟩
def keep : List Reg := [.x0,.x1,.x2,.x3,.x4,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x25,.x26,.x27]
def data (m : Memory) (id stream c w : Nat) :=
  copy m (cell id) (W (HonestStream.get stream c 64)) (W (HonestStream.get stream (c+64) 64))
    (W (HonestStream.get stream (c+128) 64)) (W (HonestStream.get stream (c+192) (w-192)))
def dest (j total : Nat) := if j+1=total then 549 else 495

structure Context (s : MachineState) (proof c w j total : Nat) : Prop where
  pc : s.pc=addr 495
  cursor : s.getReg .x24=W c
  ptr : s.getReg .x16=CheckCapSlots.address scratch j
  endPtr : s.getReg .x17=CheckCapSlots.address scratch total
  proofReg : s.getReg .x27=W proof
  head : s.getReg .x13=W (w-192)
  mask : s.getReg .x14=W (2^(w-192)-1)
  width : s.getReg .x15=W w
  limit : s.getReg .x1=65
  table : s.getReg .x23=W cap

theorem run (o : Oracle) (s : MachineState) (proof c w j total stream : Nat) (id : Fin 1024)
    (good : CheckStream.Placed (reader proof c)) (source : CheckStream.Source s (reader proof c) stream)
    (range : w=224 ∨ w=240) (input : Context s proof c w j total) (index : j<total) (small : total≤512)
    (value : CheckCapSlots.read (memoryView s) scratch j=BitVec.ofNat 32 id.val) :
    ∃ n≤65,∃ t,Segment o n s t [] ∧ t.pc=addr (dest j total) ∧ t.getReg .x24=W (c+w) ∧
      t.getReg .x16=CheckCapSlots.address scratch (j+1) ∧
      LeafMemory.Agrees (memoryView t) (data (memoryView s) id.val stream c w) ∧
      ∀ q∈keep,t.getReg q=s.getReg q := by
  let g:=reader proof c
  let r : Fin 64:=⟨c%64,by omega⟩
  have cursor : 64*g.block+r.val=c:=by change 64*(c/64)+c%64=c;omega
  obtain ⟨n,bound,t,sg,pc,x,y,z,high,mem,regs⟩:=CheckCapLowRead.positive o s g r stream w good source range
    input.pc (cursor ▸ input.cursor) input.proofReg input.head input.mask input.limit
  rw [cursor] at x y z high
  have load:=CheckCapLowStore.load o t id j (by omega) pc ((regs _ (by decide)).trans input.ptr) (by
    change extractWord32 (t.getMem _) _=_
    rw [mem];exact value)
  let u:=(t.setReg .x6 (W id.val)).setPC (addr 485)
  let m:=CheckRecordHeader.model u
  obtain ⟨v,store,pos,count,ptr,endCursor,carry⟩:=CheckCapLowStore.stored u m id (CheckRecordHeader.fits u)
    rfl ((regs _ (by decide)).trans input.table) rfl o
  have atEnd : v.getReg .x17=CheckCapSlots.address scratch total:= (carry _ (by decide)).trans ((regs _ (by decide)).trans input.endPtr)
  have index' : v.getReg .x16=CheckCapSlots.address scratch (j+1):=by
    rw [ptr];change t.getReg .x16+W 4=_
    rw [regs _ (by decide),input.ptr]
    unfold CheckCapSlots.address;rw [←BitVec.ofNat_add];congr 1
  have moved : v.getReg .x24=W (c+w):=by
    rw [endCursor];change t.getReg .x24+t.getReg .x15=_
    rw [regs _ (by decide),regs _ (by decide),input.cursor,input.width];exact (BitVec.ofNat_add ..).symm
  have branch:=CheckBranch.event o v 494 549 .eq .x16 .x17 220 (by decide) pos rfl (by decide)
  change Segment o 1 v (v.setPC (if v.getReg .x16==v.getReg .x17 then addr 549 else addr 495)) [] at branch
  rw [index',atEnd] at branch
  have same : CheckCapSlots.address scratch (j+1)=CheckCapSlots.address scratch total ↔ j+1=total := by
    constructor
    · intro h;have q:=congrArg BitVec.toNat h
      change (68719473368+4*(j+1))%2^64=(68719473368+4*total)%2^64 at q;omega
    · rintro h;rw [h]
  have aim : (if CheckCapSlots.address scratch (j+1)==CheckCapSlots.address scratch total then addr 549 else addr 495)=addr (dest j total) := by
    by_cases full : j+1=total
    · simp [dest,full]
    · simp [dest,full,beq_eq_false_iff_ne.mpr (fun e=>full (same.mp e))]
  rw [aim] at branch
  refine ⟨n+1+9+1,by omega,_,compose (compose (compose sg load) store) branch,rfl,moved,index',?_,?_⟩
  · intro q hq
    have eq:=count q hq
    have old : m.mem=memoryView s := funext (fun a=>mem (wordAddress a))
    rw [old] at eq
    change memoryView v q=_
    rw [eq]
    unfold data
    have lift {v : Word} {n : Nat} (h : v.toNat=n) : v=W n := by rw [←h];simp
    change copy (memoryView s) _ (t.getReg .x5) (t.getReg .x7) (t.getReg .x28) (t.getReg .x29 &&& t.getReg .x14) q=_
    rw [lift x,lift y,lift z,lift high]
  · intro q h
    have allowed : q∈CheckCapLowRead.saved ∧ q∉[Reg.x6,.x29,.x16,.x24] ∧ q≠.x6 := by
      cases q <;> first | decide | exact False.elim (by simpa [keep] using h)
    change v.getReg q=_
    rw [carry q allowed.2.1]
    change u.getReg q=_
    rw [show u.getReg q=t.getReg q from by simp [u,TwoPermutationPrototype.Opening.getReg_setReg,Ne.symm allowed.2.2]]
    exact regs q allowed.1

end CommitGolfCandidate.Reconstruction.CheckCapLowItem
