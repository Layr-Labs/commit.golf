import CommitGolfCandidate.HeadStreamCheckInsert

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamFive
open PackedOpening.Pack (ordinaryInstr w_add w_sub w_mul w_shl w_shr toNat_w ult_ofNat)
attribute [local simp] Opening.getReg_setReg set_byte_read
set_option maxRecDepth 8192

@[simp] theorem se12_498 : signExtend12 498#12=498#64 := by decide
@[simp] theorem se12_1920 : signExtend12 1920#12=1920#64 := by decide

def setupPath : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17]

set_option maxHeartbeats 1000000 in
theorem initialize_run (k N B : Nat) (s : MachineState)
    (pc : s.pc=pcOf 0) (x15 : s.getReg .x15=BitVec.ofNat 64 B)
    (x16 : s.getReg .x16=BitVec.ofNat 64 k) (x17 : s.getReg .x17=BitVec.ofNat 64 N)
    (kb : k≤2^24) (incoming : N≤8355061248) (capacity : N+3*k/8≤8355061248)
    (records : 481*k≤N+3*k/8) :
    Regs k (N+3*k/8) B (run s setupPath) ∧ (run s setupPath).pc=pcOf 18 ∧
      (run s setupPath).getReg .x22=0 ∧
      (∀ a,(run s setupPath).getByte a=s.getByte a) ∧
      Hop s (run s setupPath) 18 21 ∧ Reach s (run s setupPath) := by
  have high : ¬8355061248<N+3*k/8 := by omega
  have low : ¬N+3*k/8<k*481 := by omega
  have ok : PathOK s setupPath := by
    simp (disch := omega) [PathOK,setupPath,execInstrBr,pc,x15,x16,x17,ordinaryInstr,
      memoryArgumentsValid,memAccess,w_add,w_mul,w_shl,w_shr,w_sub,ult_ofNat,high,low,pcOf]
  refine ⟨?_,?_,?_,?_,(runs_path s setupPath ok).cast rfl (by decide),reach_path s setupPath ok⟩
  · constructor <;>
      simp (disch := omega) [run,setupPath,execInstrBr,x15,x16,x17,w_add,w_mul,w_shl,w_shr,
        w_sub,ult_ofNat,high,low]
  · simp (disch := omega) [run,setupPath,execInstrBr,pc,x16,x17,w_add,w_mul,w_shl,w_shr,
      w_sub,ult_ofNat,high,low,pcOf]
  · simp (disch := omega) [run,setupPath,execInstrBr,x16,x17,w_add,w_mul,w_shl,w_shr,
      w_sub,ult_ofNat,high,low]
  · intro a
    simp (disch := omega) [run,setupPath,execInstrBr,x16,x17,w_add,w_mul,w_shl,w_shr,
      w_sub,ult_ofNat,high,low]

end TwoPermutationPrototype.Packed.Checker.HeadRestore
