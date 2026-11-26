import CommitGolfCandidate.HeadStreamEmit

namespace TwoPermutationPrototype.PackedOpening.HeadStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack ProofCodec
open CommitGolfCandidate.ProofCodec.HeadStreamThree
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def partialByte (k : Nat) (Q : Proof) (r p : Nat) : Byte :=
  if p<480*r ∧ p%480=44 then HeadStreamZero.convertedByte k Q p
  else Q.getD (compactSource k p) 0

@[simp] theorem partial_zero (k : Nat) (Q : Proof) (p : Nat) :
    partialByte k Q 0 p=Q.getD (compactSource k p) 0 := by simp [partialByte]

theorem partial_full (k : Nat) (Q : Proof) (p : Nat) :
    partialByte k Q k p=HeadStreamZero.convertedByte k Q p := by
  unfold partialByte HeadStreamZero.convertedByte
  split_ifs <;> rfl

theorem partial_step (k r p : Nat) (Q : Proof) :
    (if p=480*r+44 then HeadStreamZero.convertedByte k Q p else partialByte k Q r p)=
      partialByte k Q (r+1) p := by
  unfold partialByte
  by_cases hit : p=480*r+44
  · rw [if_pos hit,if_pos (by omega)]
  · rw [if_neg hit]
    have same : (p<480*r ∧ p%480=44) ↔ (p<480*(r+1) ∧ p%480=44) := by omega
    simp only [same]

structure Heads (k L base H : Nat) (Q : Proof) (s0 : MachineState) (r : Nat) (s : MachineState) : Prop where
  regs : Regs k L base H s
  pc : s.pc=pcOf 170
  x22 : s.getReg .x22=BitVec.ofNat 64 r
  x26 : s.getReg .x26=BitVec.ofNat 64 (base+480*r+44)
  bound : r≤k
  mem : ∀ a : Word, s.getByte a=
    if base≤a.toNat ∧ a.toNat<base+(L-k) then partialByte k Q r (a.toNat-base) else s0.getByte a

def headPath : List Nat := [170,171,172,173,174,175,176,177,178,179,180,181]

@[simp] theorem merge_jump : 10560#64+signExtend21 2097108#21=10516#64 := by decide
@[simp] theorem se12_44 : signExtend12 44#12=44#64 := by decide

theorem head_iter (k L base H : Nat) (Q : Proof) (s0 s : MachineState) (r : Nat)
    (inv : Heads k L base H Q s0 r s) (len : Q.length=L) (records : 481*k≤L)
    (small : L+7≤2^33) (gap : base+2^33≤H) (room : base+2^34≤2^36)
    (hroom : H+k+8≤base+2^34) (hr : r<k)
    (headers : ∀ j<k, (s0.getByte (BitVec.ofNat 64 (H+j))).toNat%8=head k Q j) :
    ∃ t, Heads k L base H Q s0 (r+1) t ∧ Runs s t 12 12 := by
  have regs := inv.regs
  have ne : BitVec.ofNat 64 r≠BitVec.ofNat 64 k := by
    rw [Ne,w_inj _ _ (by omega) (by omega)];omega
  have header : s.getByte (BitVec.ofNat 64 (H+r))=s0.getByte (BitVec.ofNat 64 (H+r)) := by
    rw [inv.mem,toNat_w _ (by omega),if_neg (by omega)]
  have low : s.getByte (BitVec.ofNat 64 (base+480*r+44))=Q.getD (481*r+44) 0 := by
    rw [inv.mem,toNat_w _ (by omega),if_pos (by omega),show base+480*r+44-base=480*r+44 by omega,
      partialByte,if_neg (by omega),compact_record_source k _ (by omega)]
    simp only [show (480*r+44)/480=r by omega,show (480*r+44)%480=44 by omega]
    rfl
  have high : (s0.getByte (BitVec.ofNat 64 (H+r))).toNat%4=(Q.getD (481*r+45) 0).toNat%4 := by
    have h := headers r hr
    rw [head,if_pos hr] at h
    omega
  have value :
      ProofCodec.HeadStreamZero.merge (Q.getD (481*r+44) 0) (s0.getByte (BitVec.ofNat 64 (H+r)))=
        ProofCodec.HeadStreamZero.convertedByte k Q (480*r+44) := by
    rw [HeadStreamZero.converted_tail k Q r hr]
    unfold HeadStreamZero.merge
    rw [high]
  have ok : PathOK s headPath := by
    simp (disch := omega) [PathOK,headPath,execInstrBr,inv.pc,inv.x22,inv.x26,regs.x16,regs.x27,
      ne,ordinaryInstr,memoryArgumentsValid,memAccess,w_add,pcOf]
    repeat' constructor
    all_goals apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  have pc : (run s headPath).pc=pcOf 170 := by
    simp [run,headPath,execInstrBr,inv.pc,inv.x22,regs.x16,ne,pcOf]
  have next : (run s headPath).getReg .x22=BitVec.ofNat 64 (r+1) := by
    simp [run,headPath,execInstrBr,inv.x22,regs.x16,ne,w_add]
  have cursor : (run s headPath).getReg .x26=BitVec.ofNat 64 (base+480*(r+1)+44) := by
    simp [run,headPath,execInstrBr,inv.x22,inv.x26,regs.x16,ne,w_add]
    congr 1 <;> omega
  have common : Regs k L base H (run s headPath) := regs.keep headPath (by decide)
  have store : ∀ a,(run s headPath).getByte a=
      if a=BitVec.ofNat 64 (base+480*r+44) then
        HeadStreamZero.convertedByte k Q (480*r+44) else s.getByte a := by
    intro a
    simpa [run,headPath,execInstrBr,inv.x22,inv.x26,regs.x16,regs.x27,ne,w_add,
      byte_and3,byte_and63,header,low,merged_word,merged_byte] using
      congrArg (fun v : Byte => if a=BitVec.ofNat 64 (base+480*r+44) then v else s.getByte a) value
  refine ⟨_,⟨common,pc,next,cursor,by omega,?_⟩,(runs_path headPath s ok).cast rfl (by decide)⟩
  intro a
  rw [store,inv.mem]
  have hit : a=BitVec.ofNat 64 (base+480*r+44) ↔ a.toNat=base+480*r+44 := by
    constructor
    · intro h;rw [h,toNat_w _ (by omega)]
    · intro h;apply BitVec.eq_of_toNat_eq;rw [h,toNat_w _ (by omega)]
  by_cases inside : base≤a.toNat ∧ a.toNat<base+(L-k)
  · simp only [if_pos inside]
    have point : a.toNat=base+480*r+44 ↔ a.toNat-base=480*r+44 := by omega
    simp only [hit,point]
    have step := partial_step k r (a.toNat-base) Q
    split_ifs with h
    · simpa only [h,ite_true] using step
    · simpa only [if_neg h] using step
  · have absent : a≠BitVec.ofNat 64 (base+480*r+44) := by
      intro h
      have := hit.mp h
      omega
    simp only [if_neg inside,if_neg absent]

end TwoPermutationPrototype.PackedOpening.HeadStream
