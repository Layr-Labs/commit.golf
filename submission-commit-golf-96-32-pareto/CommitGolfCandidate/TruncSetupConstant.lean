import CommitGolfCandidate.TruncFlow
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 65000

private def loadAt (s : MachineState) (v : Word) (i : Nat) := (s.setReg .x17 v).setPC (loc i)
private theorem overwrite (s : MachineState) (old v : Word) (i j : Nat) :
    ((loadAt s old i).setReg .x17 v).setPC (loc j)=loadAt s v j := by
  cases s
  simp only [loadAt,MachineState.setReg,MachineState.setPC,MachineState.mk.injEq,true_and,and_true]
  funext r;by_cases e : r=.x17 <;> simp [e]
private theorem valueAt (s : MachineState) (v : Word) (i : Nat) : (loadAt s v i).getReg .x17=v := by
  simp [loadAt,MachineState.getReg_setPC,MachineState.getReg_setReg_eq]

private theorem addConst (s : MachineState) (i j : Nat) (v z : Word) (off : BitVec 12) (bi : i<2048)
    (cd : ((submission.image .commit).code[i]?).bind decodeInstruction=some (.base (.ADDI .x17 .x17 off)))
    (inc : loc i+4=loc j) (eq : v+signExtend12 off=z) :
    Runs (submission.image .commit) (loadAt s v i) (loadAt s z j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  have pc : (loadAt s v i).pc=loc i := rfl
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,valueAt,inc,eq,overwrite,ite_true]

private theorem shiftConst (s : MachineState) (i j : Nat) (v z : Word) (bi : i<2048)
    (cd : ((submission.image .commit).code[i]?).bind decodeInstruction=some (.base (.SLLI .x17 .x17 11)))
    (inc : loc i+4=loc j) (eq : v<<<11=z) :
    Runs (submission.image .commit) (loadAt s v i) (loadAt s z j) 1 1 := by
  apply one i _ _ _ bi rfl cd _ rfl
  have pc : (loadAt s v i).pc=loc i := rfl
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,valueAt,inc,ite_true]
  change some (((loadAt s v i).setReg .x17 (v<<<11)).setPC (loc j))=_
  rw [eq,overwrite]

private theorem suffixCode (k : Nat) (op : Instr) (h : (commitSuffix[k]?).bind decodeInstruction=some (.base op)) :
    ((submission.image .commit).code[796+k]?).bind decodeInstruction=some (.base op) := by rw [suffixWord];exact h

theorem constantRun (s : MachineState) (pc : s.pc=loc 796) :
    Runs (submission.image .commit) s ((s.setReg .x17 (BitVec.ofNat 64 switchPtr)).setPC (loc 801)) 5 5 := by
  have a : Runs (submission.image .commit) s (loadAt s 1072 797) 1 1 := by
    apply one 796 _ _ (.ADDI .x17 .x0 1072) (by decide) pc (suffixCode 0 _ (by rfl)) _ rfl
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,ite_true,show s.getReg .x0=0#64 from rfl];rfl
  have b:=shiftConst s 797 798 1072 2195456 (by decide) (suffixCode 1 _ (by rfl)) (by decide) (by decide)
  have c:=addConst s 798 799 2195456 2195457 1 (by decide) (suffixCode 2 _ (by rfl)) (by decide) (by decide)
  have d:=shiftConst s 799 800 2195457 4496295936 (by decide) (suffixCode 3 _ (by rfl)) (by decide) (by decide)
  have e:=addConst s 800 801 4496295936 (BitVec.ofNat 64 switchPtr) 544 (by decide) (suffixCode 4 _ (by rfl)) (by decide) (by decide)
  exact chain (chain (chain (chain a b) c) d) e

end CommitGolfCandidate.Trunc
