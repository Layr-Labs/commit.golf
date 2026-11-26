import CommitGolfCandidate.ReconstructedOpeningOps

namespace CommitGolfCandidate.Reconstruction.OpeningStraight
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafSteps LeafModel OpeningOps CommitBlocks
set_option maxRecDepth 12000
attribute [local irreducible] Riscv.execute ArtifactEncoding.decode

abbrev image := Artifact.submission.image .opening

/-- The official instruction decoder handles the register-register word operations
separately. SUBW has the same destination and sign extension in both semantics. -/
def actualForm : Instr → Instruction
  | .SUBW rd x y => .word .sub rd x y
  | op => .base op

private theorem same (s : MachineState) (op : Instr) :
    ordinaryStep s (actualForm op) = ordinaryStep s (.base op) := by
  cases op <;> rfl

def actualAt (i : Nat) := decodeInstruction (Artifact.openingCode.get 32 ⟨i%1660,by omega⟩)
def Listed : Nat → List Instr → Prop
  | _,[] => True
  | i,op::rest => actualAt i=some (actualForm op) ∧ Listed (i+1) rest

theorem fetched (i : Nat) (ins : Instruction) (inside : i<1660) (entry : actualAt i=some ins)
    (s : MachineState) (pc : s.pc=addr i) : fetch image s=some ins := by
  rw [fetch_packed image Artifact.openingCode rfl i inside (by omega) s pc]
  simpa only [actualAt,Nat.mod_eq_of_lt inside] using entry

theorem segment {o : Oracle} {ops : List Instr} {s t : MachineState} (run : Run o ops s t)
    (i : Nat) (bound : i+ops.length≤1660) (pc : s.pc=addr i) (table : Listed i ops) :
    CommitExact.Segment o image ops.length s t := by
  induction run generalizing i with
  | nil => exact CommitExact.empty _ _ _
  | @cons op ops s t u step rest ih =>
    obtain ⟨first,tail⟩ := table
    simp only [List.length_cons] at bound
    have f := fetched i _ (by omega) first s pc
    have e : CommitExact.Segment o image 1 s t := by
      cases step with
      | ordinary _ _ _ h _ => exact CommitExact.plain _ _ _ _ _ f ((same ..).trans h)
      | permute _ _ _ room fits src dst mode len kind =>
        exact CommitExact.permutation _ _ _ _ _ room fits src dst mode len kind f
    have next := (step.advance.trans (congrArg (·+4) pc)).trans (addr_next i).symm
    simpa only [List.length_cons,Nat.add_comm 1] using CommitExact.compose e (ih (i+1) (by omega) next tail)

theorem block (o : Oracle) (m : Model) (ops : List Op) (i : Nat) (bound : i+ops.length≤1660)
    (table : Listed i (ops.map Op.instr)) (ok : Checked m ops) (s : MachineState)
    (pc : s.pc=addr i) (fits : Fits s m) :
    ∃ t, CommitExact.Segment o image ops.length s t ∧ t.pc=addr (i+ops.length) ∧
      Fits t (ops.foldl (fun a op => op.apply a) m) := by
  obtain ⟨t,r,hh⟩ := checked_run o m ops ok s fits
  have b : i+(ops.map Op.instr).length≤1660 := by simpa using bound
  exact ⟨t,by simpa only [List.length_map] using segment r i b pc table,
    by simpa only [List.length_map] using r.next_pc i pc,hh⟩

end CommitGolfCandidate.Reconstruction.OpeningStraight
