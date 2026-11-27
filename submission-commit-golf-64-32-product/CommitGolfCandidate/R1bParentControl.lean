import CommitGolfCandidate.R1bParentRun

namespace TwoPermutationPrototype.RV64.R1bParents
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

private theorem codeAt (s : MachineState) (n : Nat) (op : Instr) (bound : n<262071)
    (pc : s.pc=ip n) (word : Manifest.decodeBase (packed_wideCodeWord n)=some op) :
    fetch packedWideCommitImage s=some (.base op) :=
  packed_wide_fetch_decoded s n bound pc op word

/-- Both latches test the output pointer, followed by a fixed jump on either branch. -/
private theorem latch (s : MachineState) (r : Reg) (branch jumpAt dest : Nat) (off : BitVec 21)
    (pc : s.pc=ip branch) (b : branch<262071) (j : jumpAt<262071)
    (test : Manifest.decodeBase (packed_wideCodeWord branch)=some (.BEQ .x12 r 8))
    (eq : ip jumpAt=if s.getReg .x12=s.getReg r then ip branch+8 else ip branch+4)
    (jump : Manifest.decodeBase (packed_wideCodeWord jumpAt)=some (.JAL .x0 off))
    (endPC : ip jumpAt+signExtend21 off=ip dest) (fuel : Nat) :
    execute packedWideCommitImage (2+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (s.setPC (ip dest)) true
          return out.charge 2 0) := by
  have branchStep : ordinaryStep s (.base (.BEQ .x12 r 8))=some (s.setPC (ip jumpAt)) := by
    by_cases same : s.getReg .x12=s.getReg r <;>
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,eq,same,signExtend13]
  have jumpStep : ordinaryStep (s.setPC (ip jumpAt)) (.base (.JAL .x0 off))=some (s.setPC (ip dest)) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,MachineState.setPC,endPC]
  rw [show 2+fuel=(fuel+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ (codeAt _ _ _ b pc test) branchStep,
    execute_ordinary_step _ _ _ _ _ _ (codeAt _ _ _ j rfl jump) jumpStep]
  simp [Execution.charge,instructionCycles,←Nat.add_assoc]

private theorem ptrEq {n m : Nat} (hn : n<8388608) (hm : m<8388608) :
    wordAddress (treeWord n)=wordAddress (treeWord m) ↔ n=m := by
  constructor
  · intro e
    have atWord := wordAddress_injective_of_bound (a:=treeWord n) (b:=treeWord m) (by unfold treeWord;omega)
      (by unfold treeWord;omega) e
    unfold treeWord at atWord;omega
  · rintro rfl;rfl

theorem dispatch (s : MachineState) (n fuel : Nat) (hn : 0<n) (bound : n≤8388607)
    (pc : s.pc=ip (site n+width n)) (regs : ParentRegs s (n-1))
    (stop : s.getReg .x18=wordAddress (treeWord 524287)) :
    execute packedWideCommitImage (controlSteps n+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (s.setPC (nodeIP (n-1))) true
          return out.charge (controlSteps n) 0) := by
  have noop (same : s.pc=nodeIP (n-1)) : s.setPC (nodeIP (n-1))=s := by rw [←same];cases s;rfl
  by_cases low : n<524288
  · by_cases edge : n%1024=1
    · have here : s.pc=ip 10269 := by rw [pc];unfold site width;rw [if_pos low,if_pos low,edge] <;> rfl
      have cmp : s.getReg .x12=s.getReg .x9 ↔ n=1 := by
        rw [regs.target,regs.heap,ptrEq (by omega) (by decide)];omega
      rw [controlSteps,if_pos low,if_pos edge]
      by_cases last : n=1
      · subst n
        exact latch s .x9 10269 10271 262060 1007156 here (by decide) (by decide) (by decide)
          (by rw [if_pos (cmp.mpr rfl)] <;> rfl) (by decide) (by decide) fuel
      · have next : nodeIP (n-1)=ip 4125 := by
          unfold nodeIP site;rw [if_neg (by omega),if_pos (by omega),show (n-1)%1024=0 by omega] <;> rfl
        rw [next]
        exact latch s .x9 10269 10270 4125 (BitVec.ofInt 21 (-24580)) here (by decide) (by decide)
          (by decide) (by rw [if_neg (mt cmp.mp last)] <;> rfl) (by decide) (by decide) fuel
    · have same : s.pc=nodeIP (n-1) := by
        rw [pc];unfold nodeIP;apply congrArg ip
        unfold site width;split_ifs <;> omega
      rw [controlSteps,if_pos low,if_neg edge,noop same]
      simp [Execution.charge]
  · by_cases edge : n%1024=0
    · have here : s.pc=ip 4122 := by rw [pc];unfold site width;rw [if_neg low,if_neg low,edge] <;> rfl
      have cmp : s.getReg .x12=s.getReg .x18 ↔ n=524288 := by
        rw [regs.target,stop,ptrEq (by omega) (by decide)];omega
      rw [controlSteps,if_neg low,if_pos edge]
      by_cases last : n=524288
      · subst n
        exact latch s .x18 4122 4124 4131 28 here (by decide) (by decide) (by decide)
          (by rw [if_pos (cmp.mpr rfl)] <;> rfl) (by decide) (by decide) fuel
      · have next : nodeIP (n-1)=ip 26 := by
          unfold nodeIP site;rw [if_neg (by omega),if_neg (by omega),show (n-1)%1024=1023 by omega] <;> rfl
        rw [next]
        exact latch s .x18 4122 4123 26 (BitVec.ofInt 21 (-16388)) here (by decide) (by decide)
          (by decide) (by rw [if_neg (mt cmp.mp last)] <;> rfl) (by decide) (by decide) fuel
    · have same : s.pc=nodeIP (n-1) := by
        rw [pc];unfold nodeIP;apply congrArg ip
        unfold site width;split_ifs <;> omega
      rw [controlSteps,if_neg low,if_neg edge,noop same]
      simp [Execution.charge]

end TwoPermutationPrototype.RV64.R1bParents
