import CommitGolfCandidate.TailStreamCheckRun

namespace TwoPermutationPrototype.Packed.Checker.TailRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open PackedOpening.Pack (ordinaryInstr w_add w_mul w_shl w_shr ult_ofNat)
attribute [local simp] Opening.getReg_setReg
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def rejectHigh : List Nat := [0,1,2,3,4,5,6,7,8]
def rejectLow : List Nat := [0,1,2,3,4,5,6,7,8,9,10,11]
@[simp] theorem high_guard_target : 6632#64+signExtend13 7112#13=5552#64 := by decide
@[simp] theorem low_guard_target : 6644#64+signExtend13 7100#13=5552#64 := by decide

theorem reject_high (k N : Nat) (s : MachineState)
    (pc : s.pc=pcOf 0) (x16 : s.getReg .x16=BitVec.ofNat 64 k)
    (x17 : s.getReg .x17=BitVec.ofNat 64 N) (kb : k≤2^24) (incoming : N≤8355061248)
    (bad : 8355061248<N+k/8) :
    Hop s (run s rejectHigh) 9 9 ∧ (run s rejectHigh).pc=5552 := by
  have ok : PathOK s rejectHigh := by
    simp (disch := omega) [PathOK,rejectHigh,execInstrBr,pc,x16,x17,ordinaryInstr,
      memoryArgumentsValid,memAccess,w_add,w_mul,w_shl,w_shr,ult_ofNat,bad,pcOf]
  refine ⟨(runs_path s rejectHigh ok).cast rfl (by decide),?_⟩
  simp (disch := omega) [run,rejectHigh,execInstrBr,pc,x16,x17,w_add,w_shl,w_shr,ult_ofNat,bad,pcOf]

theorem reject_low (k N : Nat) (s : MachineState)
    (pc : s.pc=pcOf 0) (x16 : s.getReg .x16=BitVec.ofNat 64 k)
    (x17 : s.getReg .x17=BitVec.ofNat 64 N) (kb : k≤2^24) (incoming : N≤8355061248)
    (capacity : N+k/8≤8355061248) (bad : N+k/8<480*k) :
    Hop s (run s rejectLow) 12 15 ∧ (run s rejectLow).pc=5552 := by
  have high : ¬8355061248<N+k/8 := by omega
  have low : N+k/8<k*480 := by omega
  have ok : PathOK s rejectLow := by
    simp (disch := omega) [PathOK,rejectLow,execInstrBr,pc,x16,x17,ordinaryInstr,
      memoryArgumentsValid,memAccess,w_add,w_mul,w_shl,w_shr,ult_ofNat,high,low,pcOf]
  refine ⟨(runs_path s rejectLow ok).cast rfl (by decide),?_⟩
  simp (disch := omega) [run,rejectLow,execInstrBr,pc,x16,x17,w_add,w_mul,w_shl,w_shr,ult_ofNat,high,low,pcOf]


end TwoPermutationPrototype.Packed.Checker.TailRestore
