import CommitGolfCandidate.TruncBatchHeader
import CommitGolfCandidate.TruncDecoderInput
import CommitGolfCandidate.TruncBProgress
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 9000
set_option maxHeartbeats 140000

private theorem pcMem (s : MachineState) (pc : Word) : (s.setPC pc).mem=s.mem := rfl
private theorem dispatchMem (s : MachineState) : (Trunc.dispatched s).mem=s.mem := rfl

theorem decodedFrame (s : MachineState) : Wire.Frame true s (afterDecode s) 0 := by
  let g:=afterGate (Trunc.dispatched s)
  let z:=g.setPC (loc 437)
  have f : Wire.Frame true z (afterDecode s) 0 := (Wire.phases true z rfl).2
  have init : z.mem=s.mem := (pcMem g (loc 437)).trans ((gateMem (Trunc.dispatched s)).trans (dispatchMem s))
  have same (a : Nat) : Wire.byte z a=Wire.byte s a := by simp only [Wire.byte,MachineState.getByte,MachineState.getMem,init]
  intro a ha
  simpa only [Wire.wanted,same] using f a ha

private theorem lowZero (input : CheckInput) (a : Nat) (low : a<32768) :
    Wire.byte (Trunc.submission.initialState .check input) a=0 := by
  unfold Wire.byte
  rw [initial_input_byte Trunc.submission .check input a (by omega)]
  have b0 : ¬ Trunc.submission.layout.commitment ≤ a := by change ¬ 4294971392 ≤ a; omega
  have b1 : ¬ Trunc.submission.layout.indices ≤ a := by change ¬ 7650414624 ≤ a; omega
  have b2 : ¬ Trunc.submission.layout.values ≤ a := by change ¬ 7784632352 ≤ a; omega
  have b3 : ¬ Trunc.submission.layout.proof ≤ a := by change ¬ 12079599648 ≤ a; omega
  have b4 : ¬ dataBase (Trunc.submission.image .check) ≤ a := by change ¬ 68719476736 ≤ a; omega
  simp [inputByte,Submission.inputBuffers,fixedBuffer,positionsBuffer,valuesBuffer,b0,b1,b2,b3,b4]

attribute [local irreducible] expandedFirst afterDecode readBuffer in
theorem startInvariant (o : Oracle) (i : CheckInput) (b : i.positions.card=BATCH) (len : i.proof.length=69120) :
    RecordInvariant o.compression (wideInput i) 0 (expandedFirst (Trunc.submission.initialState .check i)) := by
  let s:=Trunc.submission.initialState .check i
  have mode : s.getReg .x16=128 := by change BitVec.ofNat 64 i.positions.card=128;rw [b];rfl
  obtain ⟨pc,rem,idx,val,proof,root,slots,scratch,depth,mem⟩:=expandedRegs s mode
  have bytes:=Wire.decodedBytes i b len s (expandedFirst s) rfl (Wire.frameMem (decodedFrame s) mem)
  refine ⟨by decide,idx,val,proof,rem,scratch,depth,slots,root,pc,?_,?_,?_,?_⟩
  · intro u
    have h : flag u.val<32768 := by unfold flag;have :=u.isLt;omega
    have zero : (expandedFirst s).getByte (BitVec.ofNat 64 (flag u.val))=0 :=
      (bytes _ (by omega)).trans (lowZero _ _ h)
    change storedAt (expandedFirst s) u=none
    unfold storedAt;rw [if_pos zero]
  · intro r hr;omega
  · intro w _ al _;exact Wire.decodedWords bytes w al
  · intro p
    have data:=read_serialized_slice (expandedFirst s) (0 : BitVec 256) (16384+96*p.val+64) 0 32 (by
      intro j hj
      have low : 16384+96*p.val+64+j<32768 := by have:=p.isLt;omega
      have v:=(bytes _ (by omega : 16384+96*p.val+64+j<2^64)).trans (lowZero _ _ low)
      change (expandedFirst s).getByte _=(0#256).extractLsb' (8*(0+j)) 8
      rw [BitVec.extractLsb'_zero];exact v)
    simpa using data
end CommitGolfCandidate.Trunc.Batch
