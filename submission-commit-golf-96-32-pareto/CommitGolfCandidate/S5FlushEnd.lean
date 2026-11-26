import CommitGolfCandidate.S5FlushStep
import CommitGolfCandidate.S5OpenOutput
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
def batchLength : PathCode := [(388,.SUB .x11 .x19 .x18),(389,.ADDI .x5 .x0 1),(390,.ADDI .x10 .x0 0)]
def batchReported (s : MachineState) := pathEnd s batchLength

theorem batch_exit (s : MachineState) (pc : s.pc=pcAt 388) (len : Nat)
    (start : s.getReg .x18=W proofBase) (dest : s.getReg .x19=W (proofBase+len)) (fuel : Nat) :
    execute image (fuel+4) s true=pure ⟨.success,batchReported s,4,0⟩ ∧
      (batchReported s).getReg .x11=W len ∧ (batchReported s).mem=s.mem := by
  have ok : pathReady s batchLength ∧ (batchReported s).pc=pcAt 391 := by
    simp +decide [batchLength,batchReported,pathReady,pathEnd,execInstrBr,ordinaryStep,memoryArgumentsValid,memAccess,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,pc,pcAt]
  have run:=path_run .opening true s batchLength (by decide +kernel) ok.1 (fuel+1)
  have halt:=site (p:=.opening) (n:=391) (op:=.ECALL) (by decide) (by rfl) _ ok.2
  refine ⟨?_,?_,rfl⟩
  · rw [show fuel+4=(fuel+1)+batchLength.length by rfl,run]
    change (do let r←execute image (fuel+1) (batchReported s) true; pure (r.charge 3 0))=_
    rw [execute,halt,show (batchReported s).getReg .x5=1 by rfl,show (batchReported s).getReg .x10=0 by rfl];rfl
  · change s.getReg .x19-s.getReg .x18=_
    rw [start,dest];unfold W
    rw [BitVec.ofNat_add,BitVec.add_comm,BitVec.add_sub_cancel]

theorem all_flush (s : MachineState) (valid : Prop) (v : Nat) (old : FlushState s valid v 0) :
    ∃ t,Runs s t 30 30 ∧ t.pc=pcAt 388 ∧ t.getReg .x18=W proofBase ∧ t.getReg .x19=W (proofBase+69396) ∧
      ∀ good : valid,∀ j<69396,byteAt t (proofBase+j)=byteOf v j := by
  obtain ⟨a,ra,ha⟩:=flush_step s valid v 0 (by decide) old
  obtain ⟨b,rb,hb⟩:=flush_step a valid v 1 (by decide) ha
  obtain ⟨c,rc,hc⟩:=flush_step b valid v 2 (by decide) hb
  obtain ⟨d,rd,hd⟩:=flush_step c valid v 3 (by decide) hc
  obtain ⟨test,ip,mem,reg⟩:=flush_guard d 2 (by decide) hd.pc hd.bits
  exact ⟨_,(((ra.trans rb).trans rc).trans rd).trans test,ip,(reg _ (by decide)).trans hd.base,
    (reg _ (by decide)).trans hd.dest,fun good j h=>(byte_mem mem _).trans (hd.bytes good j h)⟩

theorem flush_end (s : MachineState) (valid : Prop) (v : Nat) (old : FlushState s valid v 0) (fuel : Nat) :
    ∃ t,execute image (fuel+34) s true=pure ⟨.success,t,34,0⟩ ∧ t.getReg .x11=W 69396 ∧
      ∀ good : valid,∀ j<69396,byteAt t (proofBase+j)=byteOf v j := by
  obtain ⟨t,write,pc,base,ptr,bytes⟩:=all_flush s valid v old
  obtain ⟨halt,len,mem⟩:=batch_exit t pc 69396 base ptr fuel
  refine ⟨_,?_,len,fun good j hj=>(byte_mem mem _).trans (bytes good j hj)⟩
  rw [show fuel+34=(fuel+4)+30 by omega,write,halt,pure_bind];rfl
end CommitGolfCandidate.S5Machine.Open
