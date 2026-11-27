import CommitGolfCandidate.Stage3cBatchFrame
import CommitGolfCandidate.Stage3cOpenOutput
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Writer (PackedPrefix)
open Reader (window)
def byteOf (v j : Nat) : Byte:=BitVec.ofNat 8 (v/2^(8*j))

theorem packed_byte {s : MachineState} {n v : Nat} (c : PackedPrefix s proofBase n v) (j : Nat) (bound : j<8*(n/64)) :
    byteAt s (proofBase+j)=byteOf v j := by
  have base : proofBase%8=0:=by decide
  have ix : 8*((proofBase+j)/8)=proofBase+8*(j/8):=by omega
  have rem : (proofBase+j)%8=j%8:=by omega
  rw [byte_word,ix,rem]
  apply BitVec.eq_of_toNat_eq
  change (((wordAt s (proofBase+8*(j/8))) >>> ((j%8)*8)).truncate 8).toNat=_
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,byteOf,BitVec.toNat_ofNat]
  rw [Nat.mul_comm (j%8) 8]
  rw [c.words _ (by omega),Reader.window_high _ _ _ _ (by omega)]
  rw [Reader.window_low _ _ _ _ (by omega)]
  change window v (64*(j/8)+8*(j%8)) 8=window v (8*j) 8
  rw [show 64*(j/8)+8*(j%8)=8*j by omega]

theorem byte_mem {s t : MachineState} (mem : t.mem=s.mem) (a : Nat) : byteAt t a=byteAt s a := by
  simp only [byteAt,MachineState.getByte,MachineState.getMem,mem]


/-- The batch proof is 542,720 bits, a multiple of 64: the byte loop is skipped and the
partial-byte store is skipped, so the flush is three tests and the exit. -/
def flushTest : PathCode := [(354,.ADDI .x6 .x0 8),(355,.BLTU .x24 .x6 24),(361,.BEQ .x24 .x0 12)]

theorem flush_test (s : MachineState) (pc : s.pc=pcAt 354) (bits : s.getReg .x24=W 0) :
    pathReady s flushTest ∧ (pathEnd s flushTest).pc=pcAt 364 ∧ (pathEnd s flushTest).mem=s.mem ∧
      ∀ q,q≠.x6 → (pathEnd s flushTest).getReg q=s.getReg q := by
  let u:=execInstrBr s (.ADDI .x6 .x0 8)
  have ip : u.pc=pcAt 355:=by change s.pc+4=_;rw [pc];rfl
  have ureg (q : Reg) (h : q≠.x6) : u.getReg q=s.getReg q :=
    MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm)
  have u24 : u.getReg .x24=W 0:=(ureg .x24 (by decide)).trans bits
  have u6 : u.getReg .x6=8#64:=rfl
  let v:=u.setPC (u.pc+signExtend13 24)
  have uv : execInstrBr u (.BLTU .x24 .x6 24)=v := by
    change (if BitVec.ult (u.getReg .x24) (u.getReg .x6) then u.setPC (u.pc+signExtend13 24) else u.setPC (u.pc+4))=_
    rw [u24,u6];rfl
  have vp : v.pc=pcAt 361:=by change u.pc+signExtend13 24=_;rw [ip];rfl
  have v24 : v.getReg .x24=W 0:=MachineState.getReg_setPC.trans u24
  let w:=v.setPC (v.pc+signExtend13 12)
  have vw : execInstrBr v (.BEQ .x24 .x0 12)=w := by
    change (if v.getReg .x24 == v.getReg .x0 then v.setPC (v.pc+signExtend13 12) else v.setPC (v.pc+4))=_
    rw [v24];rfl
  have wp : w.pc=pcAt 364:=by change v.pc+signExtend13 12=_;rw [vp];rfl
  have fin : pathEnd s flushTest=w:=by
    change pathEnd (execInstrBr (execInstrBr u (.BLTU .x24 .x6 24)) (.BEQ .x24 .x0 12)) []=w
    rw [uv,vw];rfl
  refine ⟨⟨pc,rfl,rfl,ip,rfl,rfl,?_⟩,?_,?_,?_⟩
  · rw [uv];exact ⟨vp,rfl,rfl,trivial⟩
  · rw [fin];exact wp
  · rw [fin];rfl
  · intro q h;rw [fin];exact MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (ureg q h))

def batchLength : PathCode := [(364,.SUB .x11 .x19 .x18),(365,.ADDI .x5 .x0 1),(366,.ADDI .x10 .x0 0)]
def batchReported (s : MachineState) := pathEnd s batchLength

theorem batch_exit (s : MachineState) (pc : s.pc=pcAt 364) (len : Nat)
    (start : s.getReg .x18=W proofBase) (dest : s.getReg .x19=W (proofBase+len)) (fuel : Nat) :
    execute image (fuel+4) s true=pure ⟨.success,batchReported s,4,0⟩ ∧
      (batchReported s).getReg .x11=W len ∧ (batchReported s).mem=s.mem := by
  have ok : pathReady s batchLength ∧ (batchReported s).pc=pcAt 367 := by
    simp +decide [batchLength,batchReported,pathReady,pathEnd,execInstrBr,ordinaryStep,memoryArgumentsValid,memAccess,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,pc,pcAt]
  have run:=path_run .opening true s batchLength (by decide +kernel) ok.1 (fuel+1)
  have halt:=site (p:=.opening) (n:=367) (op:=.ECALL) (by decide) (by rfl) _ ok.2
  refine ⟨?_,?_,rfl⟩
  · rw [show fuel+4=(fuel+1)+batchLength.length by rfl,run]
    change (do let r←execute image (fuel+1) (batchReported s) true; pure (r.charge 3 0))=_
    rw [execute,halt,show (batchReported s).getReg .x5=1 by rfl,show (batchReported s).getReg .x10=0 by rfl];rfl
  · change s.getReg .x19-s.getReg .x18=_
    rw [start,dest];unfold W
    rw [BitVec.ofNat_add,BitVec.add_comm,BitVec.add_sub_cancel]

theorem flush_end (s : MachineState) (valid : Prop) (v : Nat) (cur : ProofCursor valid s 542720 v)
    (pc : s.pc=pcAt 354) (base : s.getReg .x18=W proofBase) (fuel : Nat) :
    ∃ t,execute image (fuel+7) s true=pure ⟨.success,t,7,0⟩ ∧ t.getReg .x11=W 67840 ∧
      ∀ good : valid,∀ j<67840,byteAt t (proofBase+j)=byteOf v j := by
  obtain ⟨ready,ip,mem,reg⟩:=flush_test s pc cur.count
  let u:=pathEnd s flushTest
  have run:=path_run .opening true s flushTest (by decide +kernel) ready (fuel+4)
  obtain ⟨halt,len,mem'⟩:=batch_exit u ip 67840 ((reg _ (by decide)).trans base) ((reg _ (by decide)).trans cur.ptr) fuel
  refine ⟨_,?_,len,fun _good j hj=>?_⟩
  · rw [show fuel+7=(fuel+4)+flushTest.length by rfl,run,halt];rfl
  · rw [byte_mem mem',byte_mem mem];exact packed_byte (cur.payload _good) j (by omega)
end CommitGolfCandidate.Chained.BinaryMachine.Open
