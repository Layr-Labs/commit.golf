import CommitGolfCandidate.R1bParentSites
import CommitGolfCandidate.TwoPermutationPackedParentMask
namespace TwoPermutationPrototype.RV64.R1bParents
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
attribute [local irreducible] execute writeBits
def suffix : List Instr := narrowOps.tail
def suffixState (s : MachineState) (k : Nat) := (suffix.take k).foldl execInstrBr s
theorem narrowPtr (s : MachineState) (n : Nat) (v : BitVec 256) (r : ParentRegs s n) :
    (parentWritten s n v).getReg .x12+signExtend12 28=BitVec.ofNat 64 (8*treeWord n+28) := by
  rw [parentWritten,writeBits_register,r.target]
  change BitVec.ofNat 64 _ + BitVec.ofNat 64 28=_
  rw [←BitVec.ofNat_add]

theorem narrowed_mem (s : MachineState) (n : Nat) (v : BitVec 256) (bound : n<8388608)
    (r : ParentRegs s n) (mask : s.getReg .x6=16383) :
    (suffixState (parentWritten s n v) 5).mem=(parentWritten s n (RV64.pad238 v)).mem := by
  let raw := parentWritten s n v
  let a := 8*treeWord n
  have fit : a+32≤2^64 := by dsimp [a,treeWord];omega
  have half : raw.getHalfword (BitVec.ofNat 64 (a+28))=v.extractLsb' 224 16 :=
    loaded238 s a v (by dsimp [a];omega) fit
  have reg : raw.getReg .x6=16383 := (writeBits_register _ _ _ _).trans mask
  change (raw.setWord32 (raw.getReg .x12+signExtend12 28)
    (((raw.getHalfword (raw.getReg .x12+signExtend12 28)).zeroExtend 64 &&& raw.getReg .x6).truncate 32)).mem=_
  rw [show raw.getReg .x12+signExtend12 28=BitVec.ofNat 64 (a+28) from narrowPtr s n v r,half,reg]
  exact cleared238_memory s a v (by dsimp [a];omega) fit


private theorem word_keeps (z : MachineState) (a : Word) (w : BitVec 32) (r : Reg) :
    (z.setWord32 a w).getReg r=z.getReg r := by cases r <;> rfl

theorem suffixKeeps (z : MachineState) (r : Reg) (a : Reg.x10≠r) (b : Reg.x12≠r) (c : Reg.x7≠r) :
    (suffixState z 5).getReg r=z.getReg r := by
  simp only [suffixState,suffix,narrowOps,List.tail_cons,List.take,List.foldl,execInstrBr,MachineState.getReg_setPC,word_keeps,
    MachineState.getReg_setReg_ne _ _ _ _ a,MachineState.getReg_setReg_ne _ _ _ _ b,
    MachineState.getReg_setReg_ne _ _ _ _ c]

private theorem source (z : MachineState) :
    (suffixState z 5).getReg .x10=z.getReg .x10+signExtend12 4032 := rfl
private theorem target (z : MachineState) :
    (suffixState z 5).getReg .x12=z.getReg .x12+signExtend12 4064 := rfl
theorem suffixPC (z : MachineState) : (suffixState z 5).pc=z.pc+20 := by
  change z.pc+4+4+4+4+4=_
  simp only [BitVec.add_assoc];rfl

theorem narrowRegs (s : MachineState) (n : Nat) (v : BitVec 256) (r : ParentRegs s (n+1)) :
    ParentRegs (suffixState (parentWritten s (n+1) v) 5) n := by
  let raw:=parentWritten s (n+1) v
  have next:=next_parent_regs s n v r
  have keep (j : Reg) (a : Reg.x10≠j) (b : Reg.x12≠j) (c : Reg.x7≠j) :
      (suffixState raw 5).getReg j=s.getReg j :=
    (suffixKeeps raw j a b c).trans (writeBits_register s (wordAddress (treeWord (n+1))) v j)
  refine ⟨(source raw).trans ?_,(target raw).trans ?_,(keep .x5 (by decide) (by decide) (by decide)).trans r.selector,
    (keep .x11 (by decide) (by decide) (by decide)).trans r.size,
    (keep .x13 (by decide) (by decide) (by decide)).trans r.primitive,
    (keep .x9 (by decide) (by decide) (by decide)).trans r.heap⟩
  · exact next.source
  · exact next.target
end TwoPermutationPrototype.RV64.R1bParents
