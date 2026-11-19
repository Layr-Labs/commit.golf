import CommitGolfCandidate.TailStreamExtract

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Pack
open CommitGolfCandidate.ProofCodec.HeadStreamSeven
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

def fillZero (s : MachineState) (addr n : Nat) : MachineState :=
  (List.range n).foldl (fun s r => s.setByte (BitVec.ofNat 64 (addr+r)) 0) s

theorem fillZero_succ (s : MachineState) (addr n : Nat) :
    fillZero s addr (n+1)=(fillZero s addr n).setByte (BitVec.ofNat 64 (addr+n)) 0 := by
  simp [fillZero,List.range_succ,List.foldl_append]

theorem fillZero_bytes (s : MachineState) (addr n : Nat) (fit : addr+n<2^64) :
    ∀ a, (fillZero s addr n).getByte a=
      if addr≤a.toNat ∧ a.toNat<addr+n then 0 else s.getByte a := by
  induction n with
  | zero => simp [fillZero]
  | succ n ih =>
    exact extend_region _ _ addr n (fun _ => 0) s.getByte 0 (by omega) (ih (by omega))
      (fun a => by rw [fillZero_succ,set_byte_read]) rfl

def initial : List Nat := [9,10,11,12,13,14,15,16,17,18,19,20,21,22]

@[simp] theorem se12_6 : signExtend12 6#12=6#64 := by decide
@[simp] theorem se12_7 : signExtend12 7#12=7#64 := by decide
@[simp] theorem se12_5 : signExtend12 5#12=5#64 := by decide

variable {image : Image} [CodeImage image]

set_option maxHeartbeats 1000000 in
theorem initial_registers (k L base H : Nat) (Q : Proof) (s : MachineState)
    (pc : s.pc=pcOf 9) (x5 : s.getReg .x5=1) (x10 : s.getReg .x10=0)
    (x11 : s.getReg .x11=BitVec.ofNat 64 L) (x16 : s.getReg .x16=BitVec.ofNat 64 k)
    (x20 : s.getReg .x20=BitVec.ofNat 64 base) (x27 : s.getReg .x27=BitVec.ofNat 64 H)
    (records : 480*k≤L) (small : L+7≤2^33) (room : base+2^34≤2^36)
    (gap : base+2^33≤H) (hroom : H+k+8≤base+2^34) :
    Compact k L base H Q (run s initial) 0 (run s initial) ∧ Runs image s (run s initial) 14 14 ∧
      (∀ a, (run s initial).getByte a=(fillZero s (H+k) 7).getByte a) := by
  have ok : PathOK s initial := by
    simp (disch := omega) [PathOK,initial,execInstrBr,pc,x27,x16,ordinaryInstr,
      memoryArgumentsValid,memAccess,w_add]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> apply accessValid_of <;> rw [toNat_w _ (by omega)] <;> omega
  refine ⟨⟨?_,?_,?_,?_,by omega,?_⟩,(runs_path (image := image) _ s ok).cast rfl (by decide),?_⟩
  · constructor <;> simp (disch := omega) [run,initial,execInstrBr,x5,x10,x11,x16,x20,x27,
      w_add,w_sub,w_shr]
  · simp [run,initial,execInstrBr,pc]
  · simp [run,initial,execInstrBr]
  · simp (disch := omega) [run,initial,execInstrBr,x20,x11,x16,w_add,w_sub]
  · intro a
    simp
  · intro a
    simp [run,initial,execInstrBr,x27,x16,w_add,fillZero,List.range_succ,List.foldl_append]

theorem initial_memory (k L base H : Nat) (Q : Proof) (s t : MachineState)
    (bytes : ∀ a, t.getByte a=(fillZero s (H+k) 7).getByte a)
    (records : 480*k≤L) (small : L+7≤2^33) (room : base+2^34≤2^36)
    (gap : base+2^33≤H) (hroom : H+k+8≤base+2^34)
    (source : ∀ p<L, s.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0)
    (headers : ∀ r<k, (s.getByte (BitVec.ofNat 64 (H+r))).toNat%128=head k Q r) :
    (∀ p<L, t.getByte (BitVec.ofNat 64 (base+p))=Q.getD p 0) ∧
      (∀ r<k, (t.getByte (BitVec.ofNat 64 (H+r))).toNat%128=head k Q r) ∧
      (∀ a, ¬(base≤a.toNat ∧ a.toNat<base+2^34) → t.getByte a=s.getByte a) := by
  have frame := fillZero_bytes s (H+k) 7 (by omega)
  refine ⟨?_,?_,?_⟩
  · intro p hp
    rw [bytes,frame,toNat_w _ (by omega),if_neg (by omega)]
    exact source p hp
  · intro r hr
    rw [bytes,frame,toNat_w _ (by omega),if_neg (by omega)]
    exact headers r hr
  · intro a outside
    rw [bytes,frame,if_neg (by omega)]

end TwoPermutationPrototype.PackedOpening.TailStream
