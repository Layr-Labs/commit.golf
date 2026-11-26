import CommitGolfCandidate.PairStore
import CommitGolfCandidate.ParentRefinement
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 300000

theorem fillRightMem (s : MachineState) :
    (fillRightState s).mem = (copyAt s (s.getReg .x19) (s.getReg .x23+32)).mem := by
  simp [fillRightState,fillRightOps,copyAt,opening_copy_expansion,execInstrBr,MachineState.setReg,
    MachineState.getReg,MachineState.setPC,MachineState.getMem,MachineState.setMem,signExtend12,BitVec.add_assoc]

theorem fillLeftMem (s : MachineState) :
    (fillLeftState s).mem = (copyAt s (s.getReg .x19) (s.getReg .x23)).mem := by
  simp [fillLeftState,fillLeftOps,copyAt,opening_copy_expansion,execInstrBr,MachineState.setReg,
    MachineState.getReg,MachineState.setPC,MachineState.getMem,MachineState.setMem,signExtend12]

theorem parentCopyMem (s : MachineState) :
    (useParentState s).mem = (copyAt s (s.getReg .x19) (s.getReg .x24)).mem := by
  simp [useParentState,useParentOps,copyAt,opening_copy_expansion,execInstrBr,MachineState.setReg,
    MachineState.getReg,MachineState.setPC,MachineState.getMem,MachineState.setMem,signExtend12]

theorem rowInput (s : MachineState) (a : Nat) (aligned : a%8=0) (gap : readBuffer s (a+64) 32=0) :
    readBuffer s a 96 = padInput (readBuffer s (a+32) 32 ++ readBuffer s a 32) := by
  rw [read_leaf_query s a,read_compression_halves s (a+32) (by omega),show a+32+32=a+64 by omega,gap]
  unfold padInput
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append,BitVec.toNat_append,BitVec.toNat_append,BitVec.toNat_append]
  simp

theorem hashRegisters (s : MachineState) (pc : s.pc = 5508) :
    let ready := hashSetupState s
    ready.pc=5528 ∧ ready.getReg .x5=0 ∧ ready.getReg .x11=96 ∧ ready.getReg .x13=0 ∧
    ready.getReg .x10=s.getReg .x23 ∧ ready.getReg .x12=s.getReg .x24 ∧ ready.mem=s.mem := by
  simp [hashSetupState,hashSetupOps,execInstrBr,pc,signExtend12,
    MachineState.getReg,MachineState.setPC,MachineState.setReg]

def hashed (s : MachineState) (answer : Digest) :=
  writeBits (hashSetupState s) (s.getReg .x24) answer

theorem hashRun (s : MachineState) (pc : s.pc = 5508)
    (sv : rangeValid (s.getReg .x23) 96 = true) (sa : (s.getReg .x23).toNat % 8=0)
    (dv : rangeValid (s.getReg .x24) 32 = true) (da : (s.getReg .x24).toNat % 8=0)
    (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (6+fuel) s coins =
      (do let answer ← (liftM (World.query (.inr (.inl (readBuffer s (s.getReg .x23).toNat 96)))) :
                         OracleComp World Digest)
          let next ← execute (submission.image .check) fuel (hashed s answer) coins
          return next.charge 13 1) := by
  let ready := hashSetupState s
  obtain ⟨endPC,r5,r11,r13,r10,r12,mem⟩ := hashRegisters s pc
  have ef : fetch (submission.image .check) ready = some (.base .ECALL) := by
    apply patchedFetch _ 358 _ (by decide) endPC; rfl
  have arg : oracleInput ready = some (.inl (readBuffer s (s.getReg .x23).toNat 96)) := by
    simp [ready,oracleInput,r13,r10,r11,r12,sa,da,sv,dv,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
      read_buffer_memory_congr _ _ mem]
    try rfl
  rw [show 6+fuel=5+(fuel+1) by omega,hashSetupRun s pc,execute,ef,if_pos r5,arg]
  simp only [writeOracleAnswer,r12,bind_assoc,pure_bind]
  apply congrArg (fun continuation => (liftM (World.query (.inr (.inl (readBuffer s (s.getReg .x23).toNat 96)))) :
      OracleComp World Digest) >>= continuation)
  funext answer
  simp [hashed,oracleCycles,COMPRESSION_CYCLES,Execution.charge,← Nat.add_assoc]
  congr

end CommitGolfCandidate.PairCap.Batch
