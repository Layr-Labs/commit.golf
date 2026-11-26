import CommitGolfCandidate.ReconstructedCheckCapLowStore
import CommitGolfCandidate.ReconstructedEncoding

namespace CommitGolfCandidate.Reconstruction.CheckCapLowSetup
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps CheckRecorded CommitBlocks
open TwoPermutationPrototype.RV64
open CheckCapScanData (W fp scratch)
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
attribute [local irreducible] execute ArtifactEncoding.decode

def widthCell (d : Nat) := 262145+d
abbrev maskCell : Nat := 8589934170

def ops (d : Nat) : List Op := [.reg .x13 (.slli .x9 3),.reg .x14 (.lui 512),.reg .x14 (.addi .x14 8),
  .reg .x13 (.add .x14 .x13),.ld .x14 .x13 0 (widthCell d),.reg .x13 (.lui 1),.reg .x13 (.sub .x8 .x13),
  .ld .x15 .x13 1728 maskCell,.reg .x13 (.add .x15 .x14),.reg .x13 (.addi .x13 3905),.reg .x13 (.and .x13 .x15),
  .reg .x16 (.addi .x0 256),.reg .x14 (.subw .x16 .x14),.reg .x14 (.and .x14 .x15),
  .reg .x15 (.addi .x0 4095),.reg .x14 (.srl .x15 .x14),.reg .x15 (.addi .x13 192),
  .reg .x16 (.slli .x12 32),.reg .x17 (.srli .x16 30),.reg .x16 (.addi .x8 2048),
  .reg .x16 (.addi .x16 3784),.reg .x17 (.add .x16 .x17)]

private theorem words (d : Nat) : CheckStraight.Listed 461 ((ops d).map Op.instr) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,trivial⟩

private theorem depthAddr (d : Fin 10) : 2097160#64+(W d.val <<< (3:Nat))=wordAddress (widthCell d.val) :=
  (by decide : ∀ j : Fin 10, 2097160#64+(W j.val <<< (3:Nat))=wordAddress (widthCell j.val)) d

private theorem valid (m : Model) (d : Fin 10) (dep : m.reg .x9=W d.val) (frame : m.reg .x8=W fp) :
    Checked m (ops d.val) := by
  simp only [ops,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨⟨by unfold widthCell;have h:=d.isLt;omega,?_⟩,⟨by decide,?_⟩⟩
  · change (2097160#64+(m.reg .x9 <<< (3:Nat)))+0#64=_
    rw [dep,BitVec.add_zero,depthAddr]
  · change (m.reg .x8-4096#64)+1728#64=_
    rw [frame];rfl

def headWord (w : Word) := ((0xffffffff#64+w)+signExtend12 3905) &&& 0xffffffff#64
def maskWord (w : Word) := 0xffffffffffffffff#64 >>>
  ((((256#32-w.truncate 32).signExtend 64 &&& 0xffffffff#64).toNat)%64)
private theorem width_values (w : Nat) (h : w=224 ∨ w=240) :
    headWord (W w)=W (w-192) ∧ maskWord (W w)=W (2^(w-192)-1) ∧ headWord (W w)+192=W w := by
  rcases h with rfl|rfl <;> decide

private theorem offset (j : Fin 513) : ((W j.val <<< (32:Nat)) >>> (30:Nat))=W (4*j.val) :=
  (by decide +kernel : ∀ v : Fin 513,((W v.val <<< (32:Nat)) >>> (30:Nat))=W (4*v.val)) j

def changed : List Reg := [.x13,.x14,.x15,.x16,.x17]

def output (m : Model) (d : Nat) := (ops d).foldl (fun n e=>e.apply n) m

private theorem outputs (m : Model) (d : Fin 10) (count : Fin 513) (w : Nat)
    (range : w=224 ∨ w=240) (frame : m.reg .x8=W fp) (pending : m.reg .x12=W count.val)
    (zero : m.reg .x0=0) (width : m.mem (widthCell d.val)=W w) (mask : m.mem maskCell=0xffffffff) :
    let n:=output m d.val
    n.reg .x13=W (w-192) ∧ n.reg .x14=W (2^(w-192)-1) ∧ n.reg .x15=W w ∧
    n.reg .x16=W scratch ∧ n.reg .x17=CheckCapSlots.address scratch count.val ∧
    n.mem=m.mem ∧ ∀ q∉changed,n.reg q=m.reg q := by
  obtain ⟨hh,mm,ww⟩:=width_values w range
  refine ⟨?_,?_,?_,?_,?_,rfl,?_⟩
  · change ((m.mem maskCell+m.mem (widthCell d.val))+signExtend12 3905) &&& m.mem maskCell=_
    rw [width,mask];exact hh
  · change (m.reg .x0+signExtend12 4095) >>> ((((((m.reg .x0+signExtend12 256).truncate 32-(m.mem (widthCell d.val)).truncate 32).signExtend 64) &&& m.mem maskCell).toNat)%64)=_
    rw [width,mask,zero];exact mm
  · change ((((m.mem maskCell+m.mem (widthCell d.val))+signExtend12 3905) &&& m.mem maskCell)+192)=_
    rw [width,mask];exact ww
  · change (m.reg .x8+signExtend12 2048)+signExtend12 3784=_;rw [frame];rfl
  · change ((m.reg .x8+signExtend12 2048)+signExtend12 3784)+((m.reg .x12 <<< (32:Nat)) >>> (30:Nat))=_
    rw [frame,pending,offset];change W scratch+W (4*count.val)=W (scratch+4*count.val);exact (BitVec.ofNat_add ..).symm
  · intro q fresh
    simp only [changed,List.mem_cons,List.not_mem_nil,or_false,not_or] at fresh
    unfold output
    simp [ops,Op.apply,Model.set,Ne.symm fresh.1,Ne.symm fresh.2.1,Ne.symm fresh.2.2.1,
      Ne.symm fresh.2.2.2.1,Ne.symm fresh.2.2.2.2]

theorem run (o : Oracle) (s : MachineState) (d : Fin 10) (count : Fin 513) (w : Nat) (range : w=224 ∨ w=240)
    (pc : s.pc=addr 461) (dep : s.getReg .x9=W d.val) (frame : s.getReg .x8=W fp)
    (pending : s.getReg .x12=W count.val) (width : memoryView s (widthCell d.val)=W w)
    (mask : memoryView s maskCell=0xffffffff) :
    ∃ t,Segment o 23 s t [] ∧ t.pc=addr 495 ∧
      t.getReg .x13=W (w-192) ∧ t.getReg .x14=W (2^(w-192)-1) ∧ t.getReg .x15=W w ∧
      t.getReg .x16=CheckCapSlots.address scratch 0 ∧ t.getReg .x17=CheckCapSlots.address scratch count.val ∧
      LeafMemory.Agrees (memoryView t) (memoryView s) ∧ ∀ q∉changed,t.getReg q=s.getReg q := by
  let m:=CheckRecordHeader.model s
  obtain ⟨u,sg,pos,h⟩:=CheckStraight.block o m (ops d.val) 461 (by change 461+22≤796;decide)
    (words _) (valid m d dep frame) s pc (CheckRecordHeader.fits s)
  have j:=CheckBranch.jump o u 483 495 48 (by decide) pos rfl (by decide)
  have ty : Fits u (output m d.val):=h
  have outs:=outputs m d count w range frame pending rfl width mask
  obtain ⟨head,mask',size,ids,stop,mem,keep⟩:=outs
  refine ⟨u.setPC (addr 495),?_,rfl,(ty.registers _).trans head,(ty.registers _).trans mask',(ty.registers _).trans size,
    (ty.registers _).trans ids,(ty.registers _).trans stop,fun q hq=>(ty.memory q hq).trans (congrFun mem q),
    fun q fr=>(ty.registers _).trans (keep q fr)⟩
  simpa only [show (ops d.val).length=22 from rfl,List.nil_append] using compose sg j

end CommitGolfCandidate.Reconstruction.CheckCapLowSetup
