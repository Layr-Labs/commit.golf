import CommitGolfCandidate.LateArtifact
import CommitGolfCandidate.Execution
namespace CommitGolfCandidate.Late.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def checker := Late.submission.image .check
private theorem check_lookup {m : Nat} (a : ArtifactEncoding.Packed m) (j : Nat) (h : j<m) :
    (ArtifactEncoding.decode 32 a)[j]? = some (a.get 32 ⟨j,h⟩) := by
  simp only [ArtifactEncoding.decode, List.getElem?_ofFn, dif_pos h]
attribute [local irreducible] ArtifactEncoding.decode

private theorem at_instr (q : MachineState) (j : Nat) (op : Instr) (h : j<433)
    (p : q.pc = BitVec.ofNat 64 (4096+4*j))
    (dec : decodeInstruction (Artifact.checkCode.get 32 ⟨j,h⟩) = some (.base op)) :
    fetch checker q = some (.base op) := by
  have eq : checker.code[j]? = _ := check_lookup Artifact.checkCode j h
  simp only [fetch,p,BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4096+4*j < 2^64 by omega)]
  rw [if_pos (by constructor <;> omega)]
  simp only [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by decide : 0<4), eq, dec]

attribute [local irreducible] checker

theorem batch_length_reject (s : MachineState) (pc : s.pc = 4096)
    (mode : s.getReg .x16 = 128)
    (bad : (72704 : Word) ≠ s.getReg .x17) (fuel : Nat) :
    ∃ out, execute checker (fuel+14) s false = pure out ∧
      out.exit = Exit.failure ∧ out.cycles = 14 ∧ out.oracleCalls = 0 := by
  have f0 : fetch checker s = some (.base (.ADDI .x26 .x11 0)) := at_instr _ 0 _ (by decide) pc (by rfl)
  let s1 := execInstrBr s (.ADDI .x26 .x11 0)
  have e0 : ordinaryStep s (.base (.ADDI .x26 .x11 0)) = some s1 := rfl
  have p1 : s1.pc = 4100 := by change s.pc+4 = _; rw [pc]; rfl
  have f1 : fetch checker s1 = some (.base (.ADDI .x24 .x13 0)) := at_instr _ 1 _ (by decide) p1 (by rfl)
  let s2 := execInstrBr s1 (.ADDI .x24 .x13 0)
  have e1 : ordinaryStep s1 (.base (.ADDI .x24 .x13 0)) = some s2 := rfl
  have p2 : s2.pc = 4104 := by change s1.pc+4 = _; rw [p1]; rfl
  have f2 : fetch checker s2 = some (.base (.ADDI .x8 .x14 0)) := at_instr _ 2 _ (by decide) p2 (by rfl)
  let s3 := execInstrBr s2 (.ADDI .x8 .x14 0)
  have e2 : ordinaryStep s2 (.base (.ADDI .x8 .x14 0)) = some s3 := rfl
  have p3 : s3.pc = 4108 := by change s2.pc+4 = _; rw [p2]; rfl
  have f3 : fetch checker s3 = some (.base (.ADDI .x25 .x15 0)) := at_instr _ 3 _ (by decide) p3 (by rfl)
  let s4 := execInstrBr s3 (.ADDI .x25 .x15 0)
  have e3 : ordinaryStep s3 (.base (.ADDI .x25 .x15 0)) = some s4 := rfl
  have p4 : s4.pc = 4112 := by change s3.pc+4 = _; rw [p3]; rfl
  have f4 : fetch checker s4 = some (.base (.ADDI .x27 .x16 0)) := at_instr _ 4 _ (by decide) p4 (by rfl)
  let s5 := execInstrBr s4 (.ADDI .x27 .x16 0)
  have e4 : ordinaryStep s4 (.base (.ADDI .x27 .x16 0)) = some s5 := rfl
  have p5 : s5.pc = 4116 := by change s4.pc+4 = _; rw [p4]; rfl
  have f5 : fetch checker s5 = some (.base (.ADDI .x6 .x0 128)) := at_instr _ 5 _ (by decide) p5 (by rfl)
  let s6 := execInstrBr s5 (.ADDI .x6 .x0 128)
  have e5 : ordinaryStep s5 (.base (.ADDI .x6 .x0 128)) = some s6 := rfl
  have p6 : s6.pc = 4120 := by change s5.pc+4 = _; rw [p5]; rfl
  have f6 : fetch checker s6 = some (.base (.BEQ .x27 .x6 764)) := at_instr _ 6 _ (by decide) p6 (by rfl)
  have g1_16 : s1.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s (.ADDI .x26 .x11 0)).getReg .x16 = _
    rw [proj] <;> rfl
  have g2_16 : s2.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x24 .x13 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s1 (.ADDI .x24 .x13 0)).getReg .x16 = _
    rw [proj,g1_16] <;> rfl
  have g3_16 : s3.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x8 .x14 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s2 (.ADDI .x8 .x14 0)).getReg .x16 = _
    rw [proj,g2_16] <;> rfl
  have g4_16 : s4.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x25 .x15 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s3 (.ADDI .x25 .x15 0)).getReg .x16 = _
    rw [proj,g3_16] <;> rfl
  have g5_27 : s5.getReg .x27 = (s.getReg .x16 + 0) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x27 .x16 0)).getReg .x27 = q.getReg .x16 + 0 := rfl
    change (execInstrBr s4 (.ADDI .x27 .x16 0)).getReg .x27 = _
    rw [proj,g4_16] <;> rfl
  have g6_27 : s6.getReg .x27 = (s.getReg .x16 + 0) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x27 = q.getReg .x27 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x27 = _
    rw [proj,g5_27] <;> rfl
  have g1_0 : s1.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s (.ADDI .x26 .x11 0)).getReg .x0 = _
    rw [proj] <;> rfl
  have g2_0 : s2.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x24 .x13 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s1 (.ADDI .x24 .x13 0)).getReg .x0 = _
    rw [proj,g1_0] <;> rfl
  have g3_0 : s3.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x8 .x14 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s2 (.ADDI .x8 .x14 0)).getReg .x0 = _
    rw [proj,g2_0] <;> rfl
  have g4_0 : s4.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x25 .x15 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s3 (.ADDI .x25 .x15 0)).getReg .x0 = _
    rw [proj,g3_0] <;> rfl
  have g5_0 : s5.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x27 .x16 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s4 (.ADDI .x27 .x16 0)).getReg .x0 = _
    rw [proj,g4_0] <;> rfl
  have g6_6 : s6.getReg .x6 = ((0 : Word) + 128) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x6 = q.getReg .x0 + 128 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x6 = _
    rw [proj,g5_0] <;> rfl
  let s7 := s6.setPC 4884
  have e6 : ordinaryStep s6 (.base (.BEQ .x27 .x6 764)) = some s7 := by
    change some (if s6.getReg .x27 == s6.getReg .x6 then s6.setPC (s6.pc+signExtend13 764) else s6.setPC (s6.pc+4)) = _
    rw [g6_27,g6_6,p6]
    rw [if_pos (beq_iff_eq.mpr (by simpa using mode))]; rfl
  have p7 : s7.pc = 4884 := rfl
  have f7 : fetch checker s7 = some (.base (.ADDI .x6 .x0 35)) := at_instr _ 197 _ (by decide) p7 (by rfl)
  let s8 := execInstrBr s7 (.ADDI .x6 .x0 35)
  have e7 : ordinaryStep s7 (.base (.ADDI .x6 .x0 35)) = some s8 := rfl
  have p8 : s8.pc = 4888 := by change s7.pc+4 = _; rw [p7]; rfl
  have f8 : fetch checker s8 = some (.base (.SLLI .x6 .x6 11)) := at_instr _ 198 _ (by decide) p8 (by rfl)
  let s9 := execInstrBr s8 (.SLLI .x6 .x6 11)
  have e8 : ordinaryStep s8 (.base (.SLLI .x6 .x6 11)) = some s9 := rfl
  have p9 : s9.pc = 4892 := by change s8.pc+4 = _; rw [p8]; rfl
  have f9 : fetch checker s9 = some (.base (.ADDI .x6 .x6 1024)) := at_instr _ 199 _ (by decide) p9 (by rfl)
  let s10 := execInstrBr s9 (.ADDI .x6 .x6 1024)
  have e9 : ordinaryStep s9 (.base (.ADDI .x6 .x6 1024)) = some s10 := rfl
  have p10 : s10.pc = 4896 := by change s9.pc+4 = _; rw [p9]; rfl
  have f10 : fetch checker s10 = some (.base (.BNE .x6 .x17 7728)) := at_instr _ 200 _ (by decide) p10 (by rfl)
  have g6_0 : s6.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x0 = _
    rw [proj,g5_0] <;> rfl
  have g7_0 : s7.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (q.setPC 4884).getReg .x0 = q.getReg .x0 := rfl
    change (s6.setPC 4884).getReg .x0 = _
    rw [proj,g6_0] <;> rfl
  have g8_6 : s8.getReg .x6 = ((0 : Word) + 35) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 35)).getReg .x6 = q.getReg .x0 + 35 := rfl
    change (execInstrBr s7 (.ADDI .x6 .x0 35)).getReg .x6 = _
    rw [proj,g7_0] <;> rfl
  have g9_6 : s9.getReg .x6 = (((0 : Word) + 35) <<< 11) := by
    have proj (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x6 = q.getReg .x6 <<< 11 := rfl
    change (execInstrBr s8 (.SLLI .x6 .x6 11)).getReg .x6 = _
    rw [proj,g8_6] <;> rfl
  have g10_6 : s10.getReg .x6 = ((((0 : Word) + 35) <<< 11) + 1024) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 1024)).getReg .x6 = q.getReg .x6 + 1024 := rfl
    change (execInstrBr s9 (.ADDI .x6 .x6 1024)).getReg .x6 = _
    rw [proj,g9_6] <;> rfl
  have g1_17 : s1.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s (.ADDI .x26 .x11 0)).getReg .x17 = _
    rw [proj] <;> rfl
  have g2_17 : s2.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x24 .x13 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s1 (.ADDI .x24 .x13 0)).getReg .x17 = _
    rw [proj,g1_17] <;> rfl
  have g3_17 : s3.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x8 .x14 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s2 (.ADDI .x8 .x14 0)).getReg .x17 = _
    rw [proj,g2_17] <;> rfl
  have g4_17 : s4.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x25 .x15 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s3 (.ADDI .x25 .x15 0)).getReg .x17 = _
    rw [proj,g3_17] <;> rfl
  have g5_17 : s5.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x27 .x16 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s4 (.ADDI .x27 .x16 0)).getReg .x17 = _
    rw [proj,g4_17] <;> rfl
  have g6_17 : s6.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x17 = _
    rw [proj,g5_17] <;> rfl
  have g7_17 : s7.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (q.setPC 4884).getReg .x17 = q.getReg .x17 := rfl
    change (s6.setPC 4884).getReg .x17 = _
    rw [proj,g6_17] <;> rfl
  have g8_17 : s8.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 35)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s7 (.ADDI .x6 .x0 35)).getReg .x17 = _
    rw [proj,g7_17] <;> rfl
  have g9_17 : s9.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s8 (.SLLI .x6 .x6 11)).getReg .x17 = _
    rw [proj,g8_17] <;> rfl
  have g10_17 : s10.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 1024)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s9 (.ADDI .x6 .x6 1024)).getReg .x17 = _
    rw [proj,g9_17] <;> rfl
  let s11 := s10.setPC 4432
  have e10 : ordinaryStep s10 (.base (.BNE .x6 .x17 7728)) = some s11 := by
    change some (if s10.getReg .x6 != s10.getReg .x17 then s10.setPC (s10.pc+signExtend13 7728) else s10.setPC (s10.pc+4)) = _
    rw [g10_6,g10_17,p10]
    rw [if_pos (bne_iff_ne.mpr (by simpa using bad))]; rfl
  have p11 : s11.pc = 4432 := rfl
  have f11 : fetch checker s11 = some (.base (.ADDI .x5 .x0 1)) := at_instr _ 84 _ (by decide) p11 (by rfl)
  let s12 := execInstrBr s11 (.ADDI .x5 .x0 1)
  have e11 : ordinaryStep s11 (.base (.ADDI .x5 .x0 1)) = some s12 := rfl
  have p12 : s12.pc = 4436 := by change s11.pc+4 = _; rw [p11]; rfl
  have f12 : fetch checker s12 = some (.base (.ADDI .x10 .x0 1)) := at_instr _ 85 _ (by decide) p12 (by rfl)
  let s13 := execInstrBr s12 (.ADDI .x10 .x0 1)
  have e12 : ordinaryStep s12 (.base (.ADDI .x10 .x0 1)) = some s13 := rfl
  have p13 : s13.pc = 4440 := by change s12.pc+4 = _; rw [p12]; rfl
  have f13 : fetch checker s13 = some (.base .ECALL) := at_instr _ 86 _ (by decide) p13 (by rfl)
  have g8_0 : s8.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 35)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s7 (.ADDI .x6 .x0 35)).getReg .x0 = _
    rw [proj,g7_0] <;> rfl
  have g9_0 : s9.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s8 (.SLLI .x6 .x6 11)).getReg .x0 = _
    rw [proj,g8_0] <;> rfl
  have g10_0 : s10.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x6 1024)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s9 (.ADDI .x6 .x6 1024)).getReg .x0 = _
    rw [proj,g9_0] <;> rfl
  have g11_0 : s11.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (q.setPC 4432).getReg .x0 = q.getReg .x0 := rfl
    change (s10.setPC 4432).getReg .x0 = _
    rw [proj,g10_0] <;> rfl
  have g12_5 : s12.getReg .x5 = ((0 : Word) + 1) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 1)).getReg .x5 = q.getReg .x0 + 1 := rfl
    change (execInstrBr s11 (.ADDI .x5 .x0 1)).getReg .x5 = _
    rw [proj,g11_0] <;> rfl
  have g13_5 : s13.getReg .x5 = ((0 : Word) + 1) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x10 .x0 1)).getReg .x5 = q.getReg .x5 := rfl
    change (execInstrBr s12 (.ADDI .x10 .x0 1)).getReg .x5 = _
    rw [proj,g12_5] <;> rfl
  have g12_0 : s12.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 1)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s11 (.ADDI .x5 .x0 1)).getReg .x0 = _
    rw [proj,g11_0] <;> rfl
  have g13_10 : s13.getReg .x10 = ((0 : Word) + 1) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x10 .x0 1)).getReg .x10 = q.getReg .x0 + 1 := rfl
    change (execInstrBr s12 (.ADDI .x10 .x0 1)).getReg .x10 = _
    rw [proj,g12_0] <;> rfl
  have endRun : execute checker (fuel+1) s13 false = pure ⟨.failure,s13,1,0⟩ := by
    rw [execute,f13,g13_5,g13_10]; rfl
  refine ⟨⟨.failure,s13,14,0⟩,?_,rfl,rfl,rfl⟩
  rw [execute_ordinary_step _ _ _ _ _ _ f0 e0,
    execute_ordinary_step _ _ _ _ _ _ f1 e1,
    execute_ordinary_step _ _ _ _ _ _ f2 e2,
    execute_ordinary_step _ _ _ _ _ _ f3 e3,
    execute_ordinary_step _ _ _ _ _ _ f4 e4,
    execute_ordinary_step _ _ _ _ _ _ f5 e5,
    execute_ordinary_step _ _ _ _ _ _ f6 e6,
    execute_ordinary_step _ _ _ _ _ _ f7 e7,
    execute_ordinary_step _ _ _ _ _ _ f8 e8,
    execute_ordinary_step _ _ _ _ _ _ f9 e9,
    execute_ordinary_step _ _ _ _ _ _ f10 e10,
    execute_ordinary_step _ _ _ _ _ _ f11 e11,
    execute_ordinary_step _ _ _ _ _ _ f12 e12,endRun]
  rfl

theorem normal_length_reject (s : MachineState) (pc : s.pc = 4096)
    (mode : s.getReg .x16 ≠ 128)
    (bad : s.getReg .x16 * 792 ≠ s.getReg .x17) (fuel : Nat) :
    ∃ out, execute checker (fuel+15) s false = pure out ∧
      out.exit = Exit.failure ∧ out.cycles = 18 ∧ out.oracleCalls = 0 := by
  have f0 : fetch checker s = some (.base (.ADDI .x26 .x11 0)) := at_instr _ 0 _ (by decide) pc (by rfl)
  let s1 := execInstrBr s (.ADDI .x26 .x11 0)
  have e0 : ordinaryStep s (.base (.ADDI .x26 .x11 0)) = some s1 := rfl
  have p1 : s1.pc = 4100 := by change s.pc+4 = _; rw [pc]; rfl
  have f1 : fetch checker s1 = some (.base (.ADDI .x24 .x13 0)) := at_instr _ 1 _ (by decide) p1 (by rfl)
  let s2 := execInstrBr s1 (.ADDI .x24 .x13 0)
  have e1 : ordinaryStep s1 (.base (.ADDI .x24 .x13 0)) = some s2 := rfl
  have p2 : s2.pc = 4104 := by change s1.pc+4 = _; rw [p1]; rfl
  have f2 : fetch checker s2 = some (.base (.ADDI .x8 .x14 0)) := at_instr _ 2 _ (by decide) p2 (by rfl)
  let s3 := execInstrBr s2 (.ADDI .x8 .x14 0)
  have e2 : ordinaryStep s2 (.base (.ADDI .x8 .x14 0)) = some s3 := rfl
  have p3 : s3.pc = 4108 := by change s2.pc+4 = _; rw [p2]; rfl
  have f3 : fetch checker s3 = some (.base (.ADDI .x25 .x15 0)) := at_instr _ 3 _ (by decide) p3 (by rfl)
  let s4 := execInstrBr s3 (.ADDI .x25 .x15 0)
  have e3 : ordinaryStep s3 (.base (.ADDI .x25 .x15 0)) = some s4 := rfl
  have p4 : s4.pc = 4112 := by change s3.pc+4 = _; rw [p3]; rfl
  have f4 : fetch checker s4 = some (.base (.ADDI .x27 .x16 0)) := at_instr _ 4 _ (by decide) p4 (by rfl)
  let s5 := execInstrBr s4 (.ADDI .x27 .x16 0)
  have e4 : ordinaryStep s4 (.base (.ADDI .x27 .x16 0)) = some s5 := rfl
  have p5 : s5.pc = 4116 := by change s4.pc+4 = _; rw [p4]; rfl
  have f5 : fetch checker s5 = some (.base (.ADDI .x6 .x0 128)) := at_instr _ 5 _ (by decide) p5 (by rfl)
  let s6 := execInstrBr s5 (.ADDI .x6 .x0 128)
  have e5 : ordinaryStep s5 (.base (.ADDI .x6 .x0 128)) = some s6 := rfl
  have p6 : s6.pc = 4120 := by change s5.pc+4 = _; rw [p5]; rfl
  have f6 : fetch checker s6 = some (.base (.BEQ .x27 .x6 764)) := at_instr _ 6 _ (by decide) p6 (by rfl)
  have g1_16 : s1.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s (.ADDI .x26 .x11 0)).getReg .x16 = _
    rw [proj] <;> rfl
  have g2_16 : s2.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x24 .x13 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s1 (.ADDI .x24 .x13 0)).getReg .x16 = _
    rw [proj,g1_16] <;> rfl
  have g3_16 : s3.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x8 .x14 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s2 (.ADDI .x8 .x14 0)).getReg .x16 = _
    rw [proj,g2_16] <;> rfl
  have g4_16 : s4.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x25 .x15 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s3 (.ADDI .x25 .x15 0)).getReg .x16 = _
    rw [proj,g3_16] <;> rfl
  have g5_27 : s5.getReg .x27 = (s.getReg .x16 + 0) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x27 .x16 0)).getReg .x27 = q.getReg .x16 + 0 := rfl
    change (execInstrBr s4 (.ADDI .x27 .x16 0)).getReg .x27 = _
    rw [proj,g4_16] <;> rfl
  have g6_27 : s6.getReg .x27 = (s.getReg .x16 + 0) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x27 = q.getReg .x27 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x27 = _
    rw [proj,g5_27] <;> rfl
  have g1_0 : s1.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s (.ADDI .x26 .x11 0)).getReg .x0 = _
    rw [proj] <;> rfl
  have g2_0 : s2.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x24 .x13 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s1 (.ADDI .x24 .x13 0)).getReg .x0 = _
    rw [proj,g1_0] <;> rfl
  have g3_0 : s3.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x8 .x14 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s2 (.ADDI .x8 .x14 0)).getReg .x0 = _
    rw [proj,g2_0] <;> rfl
  have g4_0 : s4.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x25 .x15 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s3 (.ADDI .x25 .x15 0)).getReg .x0 = _
    rw [proj,g3_0] <;> rfl
  have g5_0 : s5.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x27 .x16 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s4 (.ADDI .x27 .x16 0)).getReg .x0 = _
    rw [proj,g4_0] <;> rfl
  have g6_6 : s6.getReg .x6 = ((0 : Word) + 128) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x6 = q.getReg .x0 + 128 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x6 = _
    rw [proj,g5_0] <;> rfl
  let s7 := s6.setPC 4124
  have e6 : ordinaryStep s6 (.base (.BEQ .x27 .x6 764)) = some s7 := by
    change some (if s6.getReg .x27 == s6.getReg .x6 then s6.setPC (s6.pc+signExtend13 764) else s6.setPC (s6.pc+4)) = _
    rw [g6_27,g6_6,p6]
    rw [if_neg (fun h => mode (by simpa using beq_iff_eq.mp h))]; rfl
  have p7 : s7.pc = 4124 := rfl
  have f7 : fetch checker s7 = some (.base (.ADDI .x6 .x0 0)) := at_instr _ 7 _ (by decide) p7 (by rfl)
  let s8 := execInstrBr s7 (.ADDI .x6 .x0 0)
  have e7 : ordinaryStep s7 (.base (.ADDI .x6 .x0 0)) = some s8 := rfl
  have p8 : s8.pc = 4128 := by change s7.pc+4 = _; rw [p7]; rfl
  have f8 : fetch checker s8 = some (.base (.SLLI .x6 .x6 11)) := at_instr _ 8 _ (by decide) p8 (by rfl)
  let s9 := execInstrBr s8 (.SLLI .x6 .x6 11)
  have e8 : ordinaryStep s8 (.base (.SLLI .x6 .x6 11)) = some s9 := rfl
  have p9 : s9.pc = 4132 := by change s8.pc+4 = _; rw [p8]; rfl
  have f9 : fetch checker s9 = some (.base (.ADDI .x6 .x0 792)) := at_instr _ 9 _ (by decide) p9 (by rfl)
  let s10 := execInstrBr s9 (.ADDI .x6 .x0 792)
  have e9 : ordinaryStep s9 (.base (.ADDI .x6 .x0 792)) = some s10 := rfl
  have p10 : s10.pc = 4136 := by change s9.pc+4 = _; rw [p9]; rfl
  have f10 : fetch checker s10 = some (.base (.MUL .x7 .x16 .x6)) := at_instr _ 10 _ (by decide) p10 (by rfl)
  let s11 := execInstrBr s10 (.MUL .x7 .x16 .x6)
  have e10 : ordinaryStep s10 (.base (.MUL .x7 .x16 .x6)) = some s11 := rfl
  have p11 : s11.pc = 4140 := by change s10.pc+4 = _; rw [p10]; rfl
  have f11 : fetch checker s11 = some (.base (.BNE .x7 .x17 292)) := at_instr _ 11 _ (by decide) p11 (by rfl)
  have g5_16 : s5.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x27 .x16 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s4 (.ADDI .x27 .x16 0)).getReg .x16 = _
    rw [proj,g4_16] <;> rfl
  have g6_16 : s6.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x16 = _
    rw [proj,g5_16] <;> rfl
  have g7_16 : s7.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (q.setPC 4124).getReg .x16 = q.getReg .x16 := rfl
    change (s6.setPC 4124).getReg .x16 = _
    rw [proj,g6_16] <;> rfl
  have g8_16 : s8.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 0)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s7 (.ADDI .x6 .x0 0)).getReg .x16 = _
    rw [proj,g7_16] <;> rfl
  have g9_16 : s9.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s8 (.SLLI .x6 .x6 11)).getReg .x16 = _
    rw [proj,g8_16] <;> rfl
  have g10_16 : s10.getReg .x16 = s.getReg .x16 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 792)).getReg .x16 = q.getReg .x16 := rfl
    change (execInstrBr s9 (.ADDI .x6 .x0 792)).getReg .x16 = _
    rw [proj,g9_16] <;> rfl
  have g6_0 : s6.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x0 = _
    rw [proj,g5_0] <;> rfl
  have g7_0 : s7.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (q.setPC 4124).getReg .x0 = q.getReg .x0 := rfl
    change (s6.setPC 4124).getReg .x0 = _
    rw [proj,g6_0] <;> rfl
  have g8_0 : s8.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 0)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s7 (.ADDI .x6 .x0 0)).getReg .x0 = _
    rw [proj,g7_0] <;> rfl
  have g9_0 : s9.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s8 (.SLLI .x6 .x6 11)).getReg .x0 = _
    rw [proj,g8_0] <;> rfl
  have g10_6 : s10.getReg .x6 = ((0 : Word) + 792) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 792)).getReg .x6 = q.getReg .x0 + 792 := rfl
    change (execInstrBr s9 (.ADDI .x6 .x0 792)).getReg .x6 = _
    rw [proj,g9_0] <;> rfl
  have g11_7 : s11.getReg .x7 = (s.getReg .x16 * ((0 : Word) + 792)) := by
    have proj (q : MachineState) : (execInstrBr q (.MUL .x7 .x16 .x6)).getReg .x7 = q.getReg .x16 * q.getReg .x6 := rfl
    change (execInstrBr s10 (.MUL .x7 .x16 .x6)).getReg .x7 = _
    rw [proj,g10_16,g10_6] <;> rfl
  have g1_17 : s1.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x26 .x11 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s (.ADDI .x26 .x11 0)).getReg .x17 = _
    rw [proj] <;> rfl
  have g2_17 : s2.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x24 .x13 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s1 (.ADDI .x24 .x13 0)).getReg .x17 = _
    rw [proj,g1_17] <;> rfl
  have g3_17 : s3.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x8 .x14 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s2 (.ADDI .x8 .x14 0)).getReg .x17 = _
    rw [proj,g2_17] <;> rfl
  have g4_17 : s4.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x25 .x15 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s3 (.ADDI .x25 .x15 0)).getReg .x17 = _
    rw [proj,g3_17] <;> rfl
  have g5_17 : s5.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x27 .x16 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s4 (.ADDI .x27 .x16 0)).getReg .x17 = _
    rw [proj,g4_17] <;> rfl
  have g6_17 : s6.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 128)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s5 (.ADDI .x6 .x0 128)).getReg .x17 = _
    rw [proj,g5_17] <;> rfl
  have g7_17 : s7.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (q.setPC 4124).getReg .x17 = q.getReg .x17 := rfl
    change (s6.setPC 4124).getReg .x17 = _
    rw [proj,g6_17] <;> rfl
  have g8_17 : s8.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 0)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s7 (.ADDI .x6 .x0 0)).getReg .x17 = _
    rw [proj,g7_17] <;> rfl
  have g9_17 : s9.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.SLLI .x6 .x6 11)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s8 (.SLLI .x6 .x6 11)).getReg .x17 = _
    rw [proj,g8_17] <;> rfl
  have g10_17 : s10.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 792)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s9 (.ADDI .x6 .x0 792)).getReg .x17 = _
    rw [proj,g9_17] <;> rfl
  have g11_17 : s11.getReg .x17 = s.getReg .x17 := by
    have proj (q : MachineState) : (execInstrBr q (.MUL .x7 .x16 .x6)).getReg .x17 = q.getReg .x17 := rfl
    change (execInstrBr s10 (.MUL .x7 .x16 .x6)).getReg .x17 = _
    rw [proj,g10_17] <;> rfl
  let s12 := s11.setPC 4432
  have e11 : ordinaryStep s11 (.base (.BNE .x7 .x17 292)) = some s12 := by
    change some (if s11.getReg .x7 != s11.getReg .x17 then s11.setPC (s11.pc+signExtend13 292) else s11.setPC (s11.pc+4)) = _
    rw [g11_7,g11_17,p11]
    rw [if_pos (bne_iff_ne.mpr (by simpa using bad))]; rfl
  have p12 : s12.pc = 4432 := rfl
  have f12 : fetch checker s12 = some (.base (.ADDI .x5 .x0 1)) := at_instr _ 84 _ (by decide) p12 (by rfl)
  let s13 := execInstrBr s12 (.ADDI .x5 .x0 1)
  have e12 : ordinaryStep s12 (.base (.ADDI .x5 .x0 1)) = some s13 := rfl
  have p13 : s13.pc = 4436 := by change s12.pc+4 = _; rw [p12]; rfl
  have f13 : fetch checker s13 = some (.base (.ADDI .x10 .x0 1)) := at_instr _ 85 _ (by decide) p13 (by rfl)
  let s14 := execInstrBr s13 (.ADDI .x10 .x0 1)
  have e13 : ordinaryStep s13 (.base (.ADDI .x10 .x0 1)) = some s14 := rfl
  have p14 : s14.pc = 4440 := by change s13.pc+4 = _; rw [p13]; rfl
  have f14 : fetch checker s14 = some (.base .ECALL) := at_instr _ 86 _ (by decide) p14 (by rfl)
  have g10_0 : s10.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x6 .x0 792)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s9 (.ADDI .x6 .x0 792)).getReg .x0 = _
    rw [proj,g9_0] <;> rfl
  have g11_0 : s11.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.MUL .x7 .x16 .x6)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s10 (.MUL .x7 .x16 .x6)).getReg .x0 = _
    rw [proj,g10_0] <;> rfl
  have g12_0 : s12.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (q.setPC 4432).getReg .x0 = q.getReg .x0 := rfl
    change (s11.setPC 4432).getReg .x0 = _
    rw [proj,g11_0] <;> rfl
  have g13_5 : s13.getReg .x5 = ((0 : Word) + 1) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 1)).getReg .x5 = q.getReg .x0 + 1 := rfl
    change (execInstrBr s12 (.ADDI .x5 .x0 1)).getReg .x5 = _
    rw [proj,g12_0] <;> rfl
  have g14_5 : s14.getReg .x5 = ((0 : Word) + 1) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x10 .x0 1)).getReg .x5 = q.getReg .x5 := rfl
    change (execInstrBr s13 (.ADDI .x10 .x0 1)).getReg .x5 = _
    rw [proj,g13_5] <;> rfl
  have g13_0 : s13.getReg .x0 = (0 : Word) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x5 .x0 1)).getReg .x0 = q.getReg .x0 := rfl
    change (execInstrBr s12 (.ADDI .x5 .x0 1)).getReg .x0 = _
    rw [proj,g12_0] <;> rfl
  have g14_10 : s14.getReg .x10 = ((0 : Word) + 1) := by
    have proj (q : MachineState) : (execInstrBr q (.ADDI .x10 .x0 1)).getReg .x10 = q.getReg .x0 + 1 := rfl
    change (execInstrBr s13 (.ADDI .x10 .x0 1)).getReg .x10 = _
    rw [proj,g13_0] <;> rfl
  have endRun : execute checker (fuel+1) s14 false = pure ⟨.failure,s14,1,0⟩ := by
    rw [execute,f14,g14_5,g14_10]; rfl
  refine ⟨⟨.failure,s14,18,0⟩,?_,rfl,rfl,rfl⟩
  rw [execute_ordinary_step _ _ _ _ _ _ f0 e0,
    execute_ordinary_step _ _ _ _ _ _ f1 e1,
    execute_ordinary_step _ _ _ _ _ _ f2 e2,
    execute_ordinary_step _ _ _ _ _ _ f3 e3,
    execute_ordinary_step _ _ _ _ _ _ f4 e4,
    execute_ordinary_step _ _ _ _ _ _ f5 e5,
    execute_ordinary_step _ _ _ _ _ _ f6 e6,
    execute_ordinary_step _ _ _ _ _ _ f7 e7,
    execute_ordinary_step _ _ _ _ _ _ f8 e8,
    execute_ordinary_step _ _ _ _ _ _ f9 e9,
    execute_ordinary_step _ _ _ _ _ _ f10 e10,
    execute_ordinary_step _ _ _ _ _ _ f11 e11,
    execute_ordinary_step _ _ _ _ _ _ f12 e12,
    execute_ordinary_step _ _ _ _ _ _ f13 e13,endRun]
  rfl

end CommitGolfCandidate.Late.Check
