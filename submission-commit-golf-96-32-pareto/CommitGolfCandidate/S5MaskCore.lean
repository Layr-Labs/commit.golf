import CommitGolfCandidate.S5Runs
import CommitGolfCandidate.S5Operations
import CommitGolfCandidate.S5MaskStep
namespace CommitGolfCandidate.S5Machine
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
def maskLoad (s : MachineState) :=execInstrBr s (.LHU .x31 .x12 28)
def maskAnd (s : MachineState) :=execInstrBr (maskLoad s) (.AND .x31 .x31 .x30)
def maskOut (s : MachineState) :=execInstrBr (maskAnd s) (.SW .x12 .x31 28)

theorem mask_pc (s : MachineState) : (maskOut s).pc=s.pc+12 := by
  change s.pc+4+4+4=_;rw [BitVec.add_assoc,BitVec.add_assoc];rfl

theorem mask_mem (s : MachineState) (dst : Nat) (m : Word) (y : s.getReg .x12=BitVec.ofNat 64 dst)
    (sel : s.getReg .x30=m) : (maskOut s).mem=(maskedWord s dst m).mem := by
  have loc : s.getReg .x12+signExtend12 28=BitVec.ofNat 64 (dst+28) := by rw [y,BitVec.ofNat_add];rfl
  change (s.setWord32 (s.getReg .x12+signExtend12 28)
    (((s.getHalfword (s.getReg .x12+signExtend12 28)).zeroExtend 64 &&& s.getReg .x30).truncate 32)).mem=_
  rw [loc,sel];rfl


theorem mask_core_run (o : Oracle) (s : MachineState) (n dst : Nat)
    (pc : s.pc=pcAt n) (dest : s.getReg .x12=BitVec.ofNat 64 dst)
    (fit : dst+32≤MEMORY_BYTES) (al : dst%8=0) (lhu : Site .commit n (.LHU .x31 .x12 28))
    (and_ : Site .commit (n+1) (.AND .x31 .x31 .x30)) (sw : Site .commit (n+2) (.SW .x12 .x31 28)) :
    Runs .commit true o s (maskOut s) 3 3 0 := by
  have ip1 : (maskLoad s).pc=pcAt (n+1) := by change s.pc+4=_;rw [pc,pc_succ]
  have ip2 : (maskAnd s).pc=pcAt (n+2) := by change (maskLoad s).pc+4=_;rw [ip1,pc_succ]
  have addr : s.getReg .x12+signExtend12 28=BitVec.ofNat 64 (dst+28) := by rw [dest,BitVec.ofNat_add];rfl
  have inside : dst+28<2^64 := by change _≤2^36 at fit;omega
  have loadok : memoryArgumentsValid s (.LHU .x31 .x12 28)=true := by
    change accessValid (s.getReg .x12+signExtend12 28) 2=true
    rw [addr];exact access_ok _ _ (by omega) inside (by omega)
  have writeok : memoryArgumentsValid (maskAnd s) (.SW .x12 .x31 28)=true := by
    change accessValid (s.getReg .x12+signExtend12 28) 4=true
    rw [addr];exact access_ok _ _ (by omega) inside (by omega)
  have a:=runs_step (coins:=true) (o:=o) (lhu s pc)
    (show ordinaryStep s (.base (.LHU .x31 .x12 28))=some (maskLoad s) by simp only [ordinaryStep,loadok,↓reduceIte];rfl)
  have b:=runs_step (coins:=true) (o:=o) (and_ _ ip1)
    (show ordinaryStep (maskLoad s) (.base (.AND .x31 .x31 .x30))=some (maskAnd s) from rfl)
  have c:=runs_step (coins:=true) (o:=o) (sw _ ip2)
    (show ordinaryStep (maskAnd s) (.base (.SW .x12 .x31 28))=some (maskOut s) by simp only [ordinaryStep,writeok,↓reduceIte];rfl)
  exact runs_comp (runs_comp a b) c
end CommitGolfCandidate.S5Machine
