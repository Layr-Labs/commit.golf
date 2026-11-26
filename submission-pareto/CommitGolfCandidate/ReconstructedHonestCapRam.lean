import CommitGolfCandidate.ReconstructedHonestRecordMemory
import CommitGolfCandidate.ReconstructedHonestCapState

namespace CommitGolfCandidate.Reconstruction.HonestCapRam
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open HonestRanges HonestRegionStep HonestProtected HonestCapPlan
open HonestRecordMemory (context constant proofBase)
open HonestCapState (Path Matches)
open CommitBlocks (addr)

set_option maxRecDepth 32768
attribute [local irreducible] ArtifactEncoding.decode

abbrev activeBase : Nat := 4259840
abbrev Frozen (s : MachineState) := ∀ q, protects context q=true → Contains (context.fixed q) (s.getMem q)

def needed (idx : Nat) : RegFacts :=
  if idx=1470 then [(.x24,⟨activeBase,activeBase+1024⟩),(.x20,⟨0,256⟩),(.x9,constant HonestCapTables.scratch)]
  else if idx=1512 ∨ idx=1626 then [(.x7,⟨0,70000000000⟩),(.x17,constant proofBase)]
  else []

def nothing (_ : Word) : Option Shape := some ⟨[],[]⟩

private theorem memory_table (idx fee : Nat) (hit : (idx,fee)∈HonestCapFrame.prices) :
    HonestRegionBlocks.check context Artifact.openingCode HonestCapStages.stops nothing fee (addr idx)
      ((⟨needed idx,[]⟩ : Shape).model context) = true := by
  simp only [HonestCapFrame.prices,List.mem_cons,List.not_mem_nil,or_false] at hit
  rcases hit with h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> decide +kernel

theorem preserved (idx fee : Nat) (hit : (idx,fee)∈HonestCapFrame.prices) (s t : MachineState)
    (coins : Bool) (pc : s.pc=addr idx) (old : Frozen s) (regs : RegFacts.hold s (needed idx))
    (walk : Path coins s t) : Frozen t := by
  have inShape : Holds context ⟨needed idx,[]⟩ s := ⟨regs,⟨(by intro q v h; cases h),old⟩⟩
  obtain ⟨_,_,h⟩ := HonestRegionBlocks.from_shape context Artifact.openingCode (Artifact.submission.image .opening)
    (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide) HonestCapStages.stops nothing fee (addr idx) _
    (memory_table idx fee hit) s t coins pc inShape walk
  exact h.2.2

def widthInput (d : Nat) : Shape := ⟨[(.x10,constant d),(.x8,constant HonestCapTables.sp.toNat)],[]⟩
def widthOutput (pc : Word) : Option Shape :=
  if pc=addr 1512 then some ⟨[(.x23,⟨0,64⟩)],[]⟩ else some ⟨[],[]⟩

private theorem width_table (d : Fin 9) : HonestRegionBlocks.check context Artifact.openingCode
    HonestCapStages.stops widthOutput 26 (addr 1483) ((widthInput (d.val+1)).model context) = true := by
  exact (by decide +kernel : ∀ i : Fin 9, HonestRegionBlocks.check context Artifact.openingCode
    HonestCapStages.stops widthOutput 26 (addr 1483) ((widthInput (i.val+1)).model context) = true) d

theorem width (d : Fin 9) (s t : MachineState) (coins : Bool) (start : s.pc=addr 1483)
    (stack : s.getReg .x8=HonestCapTables.sp) (depth : s.getReg .x10=HonestCapTables.w (d.val+1))
    (old : Frozen s) (walk : Path coins s t) (ending : t.pc=addr 1512) :
    (t.getReg .x23).toNat≤64 := by
  have inputs : Holds context (widthInput (d.val+1)) s := by
    refine ⟨?_,⟨(by intro q v h; cases h),old⟩⟩
    intro r v h
    simp only [widthInput,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h <;> cases h
    · rw [depth]; exact precise _
    · rw [stack]; exact precise _
  obtain ⟨b,shape,held⟩ := HonestRegionBlocks.from_shape context Artifact.openingCode
    (Artifact.submission.image .opening) (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
    HonestCapStages.stops widthOutput _ _ _ (width_table d) s t coins start inputs walk
  simp only [widthOutput,ending,ite_true,Option.some.injEq] at shape
  subst b
  exact (held.1 _ _ List.mem_cons_self).2

end CommitGolfCandidate.Reconstruction.HonestCapRam
