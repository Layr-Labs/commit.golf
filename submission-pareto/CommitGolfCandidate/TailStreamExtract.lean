import CommitGolfCandidate.TailStreamExec

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
set_option maxRecDepth 8192
attribute [local simp] Opening.getReg_setReg set_byte_read

structure EntryRegs (k L base H : Nat) (s : MachineState) : Prop where
  x5 : s.getReg .x5=1
  x10 : s.getReg .x10=0
  x11 : s.getReg .x11=BitVec.ofNat 64 L
  x16 : s.getReg .x16=BitVec.ofNat 64 k
  x20 : s.getReg .x20=BitVec.ofNat 64 base
  x27 : s.getReg .x27=BitVec.ofNat 64 H

theorem EntryRegs.keep {k L base H : Nat} {s : MachineState} (regs : EntryRegs k L base H s)
    (ts : List Nat)
    (h : ([.x5,.x10,.x11,.x16,.x20,.x27] : List Reg).all
      (fun r => !writesAny ts r)=true) : EntryRegs k L base H (run s ts) := by
  simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨h5,h10,h11,h16,h20,h27⟩ := h
  exact ⟨(run_keeps _ ts s h5).trans regs.x5,(run_keeps _ ts s h10).trans regs.x10,
    (run_keeps _ ts s h11).trans regs.x11,(run_keeps _ ts s h16).trans regs.x16,
    (run_keeps _ ts s h20).trans regs.x20,(run_keeps _ ts s h27).trans regs.x27⟩

structure Extract (k L base H : Nat) (Q : Proof) (s0 : MachineState) (r : Nat) (s : MachineState) : Prop where
  regs : EntryRegs k L base H s
  pc : s.pc=pcOf 2
  x22 : s.getReg .x22=BitVec.ofNat 64 r
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+480*r+44)
  bound : r≤k
  mem : ∀ a : Word, s.getByte a=
    if H≤a.toNat ∧ a.toNat<H+r then Q.getD (480*(a.toNat-H)+44) 0 else s0.getByte a

def extractPath : List Nat := [2,3,4,5,6,7,8]

@[simp] theorem extract_jump : pcOf 8+signExtend21 2097128#21=pcOf 2 := by decide
@[simp] theorem extract_branch : pcOf 2+signExtend13 28#13=pcOf 9 := by decide
@[simp] theorem se12_44 : signExtend12 44#12=44#64 := by decide
@[simp] theorem se12_480 : signExtend12 480#12=480#64 := by decide

variable {image : Image} [CodeImage image]

set_option maxHeartbeats 1000000 in
theorem extract_iter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (r : Nat)
    (inv : Extract k L base H Q s0 r s) (records : 480*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34) (hr : r<k)
    (source : ∀ p<L, s0.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0) :
    ∃ t, Extract k L base H Q s0 (r+1) t ∧ Runs image s t 7 7 := by
  have regs := inv.regs
  have ne : BitVec.ofNat 64 r≠BitVec.ofNat 64 k := by
    rw [Ne,w_inj _ _ (by omega) (by omega)];omega
  have load : s.getByte (BitVec.ofNat 64 (base+480*r+44))=Q.getD (480*r+44) 0 := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
    simpa only [Nat.add_assoc] using source (480*r+44) (by omega)
  have ok : PathOK s extractPath := by
    simp (disch := omega) [PathOK,extractPath,execInstrBr,inv.pc,inv.x22,inv.x26,regs.x16,regs.x27,
      ne,ordinaryInstr,memoryArgumentsValid,memAccess,w_add,pcOf]
    constructor <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  have pc : (run s extractPath).pc=pcOf 2 := by
    simp [run,extractPath,execInstrBr,inv.pc,inv.x22,regs.x16,ne,pcOf] <;> decide
  have next : (run s extractPath).getReg .x22=BitVec.ofNat 64 (r+1) := by
    simp [run,extractPath,execInstrBr,inv.x22,regs.x16,ne,w_add]
  have cursor : (run s extractPath).getReg .x26=BitVec.ofNat 64 (base+480*(r+1)+44) := by
    simp [run,extractPath,execInstrBr,inv.x22,inv.x26,regs.x16,ne,w_add]
    congr 1 <;> omega
  have store : ∀ a, (run s extractPath).getByte a=
      if a=BitVec.ofNat 64 (H+r) then Q.getD (480*r+44) 0 else s.getByte a := by
    intro a
    simp [run,extractPath,execInstrBr,inv.x22,inv.x26,regs.x16,regs.x27,ne,w_add,load,setWidth_byte]
  refine ⟨_,⟨regs.keep extractPath (by decide),pc,next,cursor,by omega,?_⟩,
    (runs_path (image := image) _ s ok).cast rfl (by decide)⟩
  exact extend_region _ _ H r (fun j => Q.getD (480*j+44) 0) s0.getByte _ (by omega) inv.mem store rfl

end TwoPermutationPrototype.PackedOpening.TailStream
