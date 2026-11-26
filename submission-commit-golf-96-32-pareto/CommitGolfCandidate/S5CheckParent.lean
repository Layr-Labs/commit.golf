import CommitGolfCandidate.S5Trace
import CommitGolfCandidate.S5Operations
import CommitGolfCandidate.S5PlainEffect
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def prepare : PathCode := [(173,.ADDI .x5 .x0 0),(174,.ADDI .x11 .x0 96),(175,.ADDI .x13 .x0 0),
  (176,.ADDI .x6 .x0 1),(177,.BNE .x30 .x6 12)]
def prepared (s : MachineState) := pathEnd s prepare

theorem prepare_parent (s : MachineState) (pc : s.pc=pcAt 173) (b : Bool) (mode : (s.getReg .x30 != 1)=b) :
    pathReady s prepare ∧ (prepared s).pc=pcAt (if b then 180 else 178) ∧ (prepared s).mem=s.mem ∧
    (prepared s).getReg .x5=0 ∧ (prepared s).getReg .x13=0 ∧ (prepared s).getReg .x11=96 ∧
    (prepared s).getReg .x10=s.getReg .x10 ∧ (prepared s).getReg .x12=s.getReg .x12 ∧ (prepared s).getReg .x31=s.getReg .x31 := by
  change (s.regs .x30 != 1#64)=b at mode
  cases b
  · have eq : s.regs .x30=1#64 := by simpa using mode
    simp +decide [prepared,prepare,pathReady,pathEnd,execInstrBr,ordinaryStep,memoryArgumentsValid,memAccess,pc,pcAt,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12,eq]
  · have ne : s.regs .x30≠1#64 := by simpa using mode
    simp +decide [prepared,prepare,pathReady,pathEnd,execInstrBr,ordinaryStep,memoryArgumentsValid,memAccess,pc,pcAt,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12,signExtend13,ne] <;> simp_all +decide

def readyMask (s : MachineState) (dst : Nat) (v : Output) :=
  execInstrBr (writeBits (prepared s) (BitVec.ofNat 64 dst) v) (.JAL .x0 128)

theorem plain_query (s : MachineState) (pc : s.pc=pcAt 173) (one : s.getReg .x30=1) (src dst : Nat)
    (rs : s.getReg .x10=BitVec.ofNat 64 src) (rd : s.getReg .x12=BitVec.ofNat 64 dst)
    (srcFit : src+96≤MEMORY_BYTES) (srcAl : src%8=0) (dstFit : dst+32≤MEMORY_BYTES) (dstAl : dst%8=0) (fuel : Nat) :
    execute (image .check) (fuel+7) s false =
      (do let v ← Late.hash (readBuffer s src 96)
          let out ← execute (image .check) fuel (readyMask s dst v) false
          return out.charge 14 1) := by
  obtain ⟨ok,ip,mem,sel,kind,len,from_,to_,_⟩:=prepare_parent s pc false (by rw [one];decide)
  have found:=site (p:=.check) (n:=178) (op:=.ECALL) (by decide) (by rfl) _ ip
  have call:=hash_run .check false (prepared s) (fuel+1) src dst found sel len kind (from_.trans rs) (to_.trans rd) srcFit srcAl dstFit dstAl
  have pre:=path_run .check false s prepare (by decide +kernel) ok (fuel+2)
  rw [show fuel+7=(fuel+2)+prepare.length by rfl,pre]
  change (do let r ← execute (image .check) ((fuel+1)+1) (prepared s) false; pure (r.charge 5 0))=_
  rw [call,read_congr_mem _ _ _ _ mem,bind_assoc]
  apply bind_congr
  intro v
  let u:=writeBits (prepared s) (BitVec.ofNat 64 dst) v
  have up : u.pc=pcAt 179 := by rw [show u.pc=(prepared s).pc+4 from rfl,ip];rfl
  have j:=site (p:=.check) (n:=179) (op:=.JAL .x0 128) (by decide) (by rfl) u up
  rw [execute_ordinary_step _ _ _ (readyMask s dst v) _ _ j rfl]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro out;congr 1 <;> simp [Execution.charge,instructionCycles,Nat.add_assoc] <;> omega
end CommitGolfCandidate.S5Machine.Check
