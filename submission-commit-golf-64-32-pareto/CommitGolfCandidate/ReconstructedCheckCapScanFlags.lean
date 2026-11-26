import CommitGolfCandidate.ReconstructedCheckCapArith
import CommitGolfCandidate.ReconstructedCapScanMemory

namespace CommitGolfCandidate.Reconstruction.CheckCapScanFlags
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks
open HonestFlagState (code)
abbrev W := BitVec.ofNat 64
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] execute ArtifactEncoding.decode

theorem copiedByte (s t : MachineState) (mem : t.mem=s.mem) (q : Word) : t.getByte q=s.getByte q :=
  congrArg (fun m : Word→Word => extractByte (m (alignToDword q)) (byteOffset q)) mem

theorem extCode (b : Bool) : (code b).zeroExtend 64=W b.toNat := by cases b <;> rfl

def combine (s : MachineState) (l r : Bool) : MachineState :=
  (((s.setReg .x17 (W l.toNat)).setReg .x5 (W r.toNat)).setReg .x6 (W (l||r).toNat)).setPC (addr 450)

theorem load (o : Oracle) (s : MachineState) (l r : Bool) (pc : s.pc=addr 447)
    (left : s.getByte (s.getReg .x14)=code l) (right : s.getByte (s.getReg .x13)=code r)
    (goodL : accessValid (s.getReg .x14) 1=true) (goodR : accessValid (s.getReg .x13) 1=true) :
    Segment o 3 s (combine s l r) [] := by
  have a:=CheckMemoryOps.loadB o s 447 .x17 .x14 _ (by decide) pc rfl goodL
  rw [left,extCode] at a
  let t:=(s.setReg .x17 (W l.toNat)).setPC (addr 448)
  have b:=CheckMemoryOps.loadB o t 448 .x5 .x13 (s.getReg .x13) (by decide) rfl rfl goodR
  have read : t.getByte (s.getReg .x13)=code r := (copiedByte s t rfl _).trans right
  rw [read,extCode] at b
  let u:=(t.setReg .x5 (W r.toNat)).setPC (addr 449)
  have val : u.getReg .x5 ||| u.getReg .x17=W (l||r).toNat := by
    change W r.toNat ||| W l.toNat=_;cases l <;> cases r <;> rfl
  have third : Segment o 1 u (combine s l r) [] := by
    apply plain o _ _ _ (CheckMemoryOps.parsed (n:=449) (ins:=.base (.OR .x6 .x5 .x17)) (by decide) u rfl)
    change some ((u.setReg .x6 (u.getReg .x5 ||| u.getReg .x17)).setPC (u.pc+4))=_
    rw [val];rfl
  exact compose (compose a b) third

def marked (s : MachineState) (l r : Bool) (dst : Word) :=
  if l||r then (combine s l r).setByte dst 1 else combine s l r

theorem positive (o : Oracle) (s : MachineState) (l r : Bool) (pc : s.pc=addr 447)
    (left : s.getByte (s.getReg .x14)=code l) (right : s.getByte (s.getReg .x13)=code r)
    (goodL : accessValid (s.getReg .x14) 1=true) (goodR : accessValid (s.getReg .x13) 1=true)
    (dst : Word) (destination : s.getReg .x15=dst) (goodD : accessValid dst 1=true)
    (one : s.getReg .x18=1) :
    Segment o (4+(l||r).toNat) s ((marked s l r dst).setPC (addr 452)) [] := by
  let u:=combine s l r
  have stem:=load o s l r pc left right goodL goodR
  have branch:=CheckBranch.event o u 450 452 .eq .x6 .x0 8 (by decide) rfl rfl (by decide)
  change Segment o 1 u (u.setPC (if (W (l||r).toNat==0#64) then addr 452 else addr 451)) [] at branch
  cases h : l||r with
  | false=>
    rw [h] at branch
    change Segment o 1 u (u.setPC (addr 452)) [] at branch
    rw [marked,h,ite_eq_right (by decide : false≠true)]
    exact compose stem branch
  | true=>
    rw [h] at branch
    let v:=u.setPC (addr 451)
    have unit : (v.getReg .x18).truncate 8=1 := by change (s.getReg .x18).truncate 8=1;rw [one];rfl
    have write:=CheckMemoryOps.storeB o v 451 .x15 .x18 dst 1 (by decide) rfl destination unit goodD
    change Segment o 1 u v [] at branch
    rw [marked,h,ite_eq_left rfl]
    have same : (v.setByte dst 1).setPC (addr (451+1))=(u.setByte dst 1).setPC (addr 452) := rfl
    rw [same] at write
    exact compose (compose stem branch) write

theorem registers (s : MachineState) (l r : Bool) (dst : Word) (q : Reg) :
    (marked s l r dst).getReg q=(combine s l r).getReg q := by
  unfold marked;split <;> rfl

theorem memory (s : MachineState) (l r : Bool) (dst : Word) :
    (marked s l r dst).mem=(CapScanMemory.marked s dst (l||r)).mem := by
  cases h : l||r <;> simp only [marked,CapScanMemory.marked,h,Bool.false_eq_true,ite_false,ite_true] <;> rfl

theorem keep (s : MachineState) (l r : Bool) (dst : Word) (q : Reg) (fresh : q∉[Reg.x17,.x5,.x6]) :
    (marked s l r dst).getReg q=s.getReg q := by
  rw [registers]
  simp only [combine,MachineState.getReg_setPC,TwoPermutationPrototype.Opening.getReg_setReg]
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at fresh
  split_ifs <;> simp_all

end CommitGolfCandidate.Reconstruction.CheckCapScanFlags
