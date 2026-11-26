import CommitGolfCandidate.ReconstructedHonestCapStages

namespace CommitGolfCandidate.Reconstruction.HonestCapGuards
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCapStages HonestCuts
open CommitBlocks (addr)

set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode

private theorem read_at (i : Fin 1660) : HonestBlocks.readOp Artifact.openingCode (addr i.val) =
    decodeInstruction (Artifact.openingCode.get 32 i) := by
  have bound := i.isLt
  have exactIdx : HonestBinaryRank.index (addr i.val) = i.val := by
    unfold HonestBinaryRank.index addr
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  unfold HonestBlocks.readOp
  simp only [exactIdx,beq_self_eq_true,ite_true,dite_eq_left bound]

private theorem word1469 : HonestBlocks.readOp Artifact.openingCode (addr 1469) = some (.base (.BGEU .x21 .x22 56)) := by
  rw [read_at (i := ⟨1469,by decide⟩)]
  rw [show Artifact.openingCode.get 32 ⟨1469,by decide⟩ = 0x36afc63 by decide +kernel]
  rfl

private theorem word1602 : HonestBlocks.readOp Artifact.openingCode (addr 1602) = some (.base (.BGEU .x21 .x20 7580)) := by
  rw [read_at (i := ⟨1602,by decide⟩)]
  rw [show Artifact.openingCode.get 32 ⟨1602,by decide⟩ = 0xd94afee3 by decide +kernel]
  rfl

private theorem word1511 : HonestBlocks.readOp Artifact.openingCode (addr 1511) = some (.base (.BEQ .x24 .x25 280)) := by
  rw [read_at (i := ⟨1511,by decide⟩)]
  rw [show Artifact.openingCode.get 32 ⟨1511,by decide⟩ = 0x119c0c63 by decide +kernel]
  rfl

private theorem ends_here (im : Image) (s t : MachineState) (coins : Bool) (cut : Word → Bool) (op : Instruction)
    (read : fetch im s = some op) (plain : op ≠ .base .ECALL) (target : Word) (stop : cut target = true)
    (pc : ∀ u, ordinaryStep s op = some u → u.pc = target) (walk : Reaches im coins cut s t) : t.pc = target := by
  cases walk with
  | hit run cont _ => exact pc _ (HonestAbstract.continued_step im s op coins read plain _ run cont)
  | more run cont inside _ =>
    rw [pc _ (HonestAbstract.continued_step im s op coins read plain _ run cont),stop] at inside
    cases inside

private theorem bge (s t : MachineState) (coins : Bool) (idx fall take : Nat) (x y : Reg) (disp : BitVec 13)
    (pc : s.pc = addr idx) (word : HonestBlocks.readOp Artifact.openingCode (addr idx) = some (.base (.BGEU x y disp)))
    (sequential : addr idx+4 = addr fall) (jump : addr idx+signExtend13 disp = addr take)
    (stays : stops (addr fall) = true) (leaves : stops (addr take) = true)
    (walk : Reaches (Artifact.submission.image .opening) coins stops s t) :
    t.pc = (if (s.getReg x).ult (s.getReg y) then addr fall else addr take) := by
  have read := HonestBlocks.fetch_op Artifact.openingCode (Artifact.submission.image .opening) (Eq.refl (ArtifactEncoding.decode 32 Artifact.openingCode)) (by decide)
    s (.base (.BGEU x y disp)) (pc ▸ word)
  apply ends_here _ s t coins stops _ read (by simp) _ (by split <;> assumption) _ walk
  intro u step
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
  subst u
  simp only [execInstrBr]
  split <;> simp_all [MachineState.setPC]

theorem scan (s t : MachineState) (coins : Bool) (pc : s.pc = addr 1469)
    (walk : Reaches (Artifact.submission.image .opening) coins stops s t) :
    t.pc = (if (s.getReg .x21).ult (s.getReg .x22) then addr 1470 else addr 1483) := by
  exact bge s t coins 1469 1470 1483 .x21 .x22 56 pc word1469 rfl rfl rfl rfl walk

theorem group (s t : MachineState) (coins : Bool) (pc : s.pc = addr 1602)
    (walk : Reaches (Artifact.submission.image .opening) coins stops s t) :
    t.pc = (if (s.getReg .x21).ult (s.getReg .x20) then addr 1603 else addr 1449) := by
  exact bge s t coins 1602 1603 1449 .x21 .x20 7580 pc word1602 rfl rfl rfl rfl walk

theorem emit (s t : MachineState) (coins : Bool) (pc : s.pc = addr 1511)
    (walk : Reaches (Artifact.submission.image .opening) coins stops s t) :
    t.pc = (if s.getReg .x24 = s.getReg .x25 then addr 1581 else addr 1512) := by
  have word := word1511
  have read := HonestBlocks.fetch_op Artifact.openingCode (Artifact.submission.image .opening) (Eq.refl (ArtifactEncoding.decode 32 Artifact.openingCode)) (by decide)
    s (.base (.BEQ .x24 .x25 280)) (pc ▸ word)
  apply ends_here _ s t coins stops _ read (by simp) _ (by split <;> rfl) _ walk
  intro u step
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
  subst u
  simp only [execInstrBr,beq_iff_eq]
  split <;> simp [MachineState.setPC,pc,addr,signExtend13, *]

end CommitGolfCandidate.Reconstruction.HonestCapGuards
