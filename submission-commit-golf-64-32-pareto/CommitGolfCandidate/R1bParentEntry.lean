import CommitGolfCandidate.R1bParentExecution
namespace TwoPermutationPrototype.RV64.R1bParents
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

def setupOps : List Instr := [.LUI .x18 4096,.ADDI .x18 .x18 4064,.ADD .x18 .x9 .x18,.LUI .x6 4,.ADDI .x6 .x6 4095]
def setup (s : MachineState) (k : Nat) := (setupOps.take k).foldl execInstrBr s

theorem setupRun (s : MachineState) (pc : s.pc=4180) (fuel : Nat) :
    execute packedWideCommitImage (5+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (setup s 5) true;return out.charge 5 0) := by
  apply execute_unit_steps (states:=setup s)
  intro j hj
  have dec : ∀ k : Fin 5, Manifest.decodeBase (packed_wideCodeWord (21+k.val))=some (setupOps[k.val]?.getD .EBREAK) := by decide
  have here : (setup s j).pc=BitVec.ofNat 64 (4096+4*(21+j)) := by
    interval_cases j <;> simp [setup,setupOps,List.foldl,execInstrBr,MachineState.setPC,pc]
  refine ⟨.base (setupOps[j]?.getD .EBREAK),packed_wide_fetch_decoded (setup s j) (21+j) (by omega) here _ (dec ⟨j,hj⟩),?_,?_⟩
  · interval_cases j <;> rfl
  · interval_cases j <;> rfl

theorem setupReady (s : MachineState) (pc : s.pc=4180) (regs : ParentRegs s 8388607) :
    Ready (setup s 5) 8388607 := by
  refine ⟨⟨regs.source,regs.target,regs.selector,regs.size,regs.primitive,regs.heap⟩,?_,?_,?_⟩
  · change s.pc+4+4+4+4+4=_
    rw [pc] <;> rfl
  · change s.getReg .x9+(16777216#64+signExtend12 4064)=_
    rw [regs.heap] <;> decide
  · change 16384#64+signExtend12 4095=16383#64
    decide

end TwoPermutationPrototype.RV64.R1bParents
