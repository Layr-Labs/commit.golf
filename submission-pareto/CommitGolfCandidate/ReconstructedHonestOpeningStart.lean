import CommitGolf.Artifact
import CommitGolfCandidate.ReconstructedHonestMachine

namespace CommitGolfCandidate.Reconstruction.HonestOpeningStart
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestMachine

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

private def code := Artifact.submission.image .opening
private def instructions : Trace :=
  [⟨24, .ADDI .x2 .x2 2064⟩,
   ⟨25, .SD .x2 .x1 2024⟩,
   ⟨26, .SD .x2 .x8 2016⟩,
   ⟨27, .SD .x2 .x9 2008⟩,
   ⟨28, .SD .x2 .x18 2000⟩,
   ⟨29, .SD .x2 .x19 1992⟩,
   ⟨30, .SD .x2 .x20 1984⟩,
   ⟨31, .SD .x2 .x21 1976⟩,
   ⟨32, .SD .x2 .x22 1968⟩,
   ⟨33, .SD .x2 .x23 1960⟩,
   ⟨34, .SD .x2 .x24 1952⟩,
   ⟨35, .SD .x2 .x25 1944⟩,
   ⟨36, .SD .x2 .x26 1936⟩,
   ⟨37, .SD .x2 .x27 1928⟩,
   ⟨38, .ADDI .x8 .x2 2032⟩,
   ⟨39, .ADDI .x2 .x2 3808⟩,
   ⟨40, .ADDI .x12 .x10 0⟩,
   ⟨41, .ADDI .x7 .x0 0⟩,
   ⟨42, .ADDI .x10 .x0 4095⟩,
   ⟨43, .SRLI .x11 .x10 16⟩,
   ⟨44, .LUI .x13 1⟩,
   ⟨45, .SUB .x13 .x8 .x13⟩,
   ⟨46, .SD .x13 .x11 1856⟩,
   ⟨47, .SRLI .x11 .x10 18⟩,
   ⟨48, .LUI .x13 1⟩,
   ⟨49, .SUB .x13 .x8 .x13⟩,
   ⟨50, .SD .x13 .x11 1848⟩,
   ⟨51, .SRLI .x11 .x10 20⟩,
   ⟨52, .LUI .x13 1⟩,
   ⟨53, .SUB .x13 .x8 .x13⟩,
   ⟨54, .SD .x13 .x11 1840⟩,
   ⟨55, .SRLI .x11 .x10 31⟩,
   ⟨56, .LUI .x13 1⟩,
   ⟨57, .SUB .x13 .x8 .x13⟩,
   ⟨58, .SD .x13 .x11 1832⟩,
   ⟨59, .LUI .x11 172032⟩,
   ⟨60, .ADDIW .x11 .x11 493⟩,
   ⟨61, .SLLI .x11 .x11 3⟩,
   ⟨62, .LUI .x13 1⟩,
   ⟨63, .SUB .x13 .x8 .x13⟩,
   ⟨64, .SD .x13 .x11 1824⟩,
   ⟨65, .SRLI .x10 .x10 32⟩,
   ⟨66, .LUI .x11 1⟩,
   ⟨67, .SUB .x11 .x8 .x11⟩,
   ⟨68, .SD .x11 .x10 1872⟩,
   ⟨69, .LUI .x10 524288⟩,
   ⟨70, .ADDIW .x10 .x10 4095⟩,
   ⟨71, .LUI .x11 1⟩,
   ⟨72, .SUB .x11 .x8 .x11⟩,
   ⟨73, .SD .x11 .x10 1864⟩,
   ⟨74, .LUI .x10 262144⟩,
   ⟨75, .ADDIW .x10 .x10 4095⟩,
   ⟨76, .LUI .x11 1⟩,
   ⟨77, .SUB .x11 .x8 .x11⟩,
   ⟨78, .SD .x11 .x10 1816⟩,
   ⟨79, .LUI .x10 131072⟩,
   ⟨80, .ADDIW .x10 .x10 4095⟩,
   ⟨81, .LUI .x11 1⟩,
   ⟨82, .SUB .x11 .x8 .x11⟩,
   ⟨83, .SD .x11 .x10 1808⟩,
   ⟨84, .LUI .x10 1⟩,
   ⟨85, .ADDIW .x31 .x10 2051⟩,
   ⟨86, .LUI .x10 45056⟩,
   ⟨87, .ADDIW .x10 .x10 129⟩,
   ⟨88, .SLLI .x11 .x10 5⟩,
   ⟨89, .LUI .x10 43691⟩,
   ⟨90, .SLLI .x10 .x10 4⟩,
   ⟨91, .LUI .x13 1⟩,
   ⟨92, .SUB .x13 .x8 .x13⟩,
   ⟨93, .SD .x13 .x10 1792⟩,
   ⟨94, .LUI .x10 16⟩,
   ⟨95, .ADDIW .x10 .x10 4095⟩,
   ⟨96, .LUI .x13 1⟩,
   ⟨97, .SUB .x13 .x8 .x13⟩,
   ⟨98, .SD .x13 .x10 1784⟩,
   ⟨99, .ADDI .x6 .x8 2048⟩,
   ⟨100, .ADDI .x6 .x6 3984⟩,
   ⟨101, .LUI .x10 78848⟩,
   ⟨102, .ADDIW .x25 .x10 131⟩,
   ⟨103, .SLLI .x25 .x25 5⟩,
   ⟨104, .LUI .x10 32768⟩,
   ⟨105, .ADDIW .x22 .x10 129⟩,
   ⟨106, .SLLI .x22 .x22 5⟩,
   ⟨107, .LUI .x10 1⟩,
   ⟨108, .SUB .x10 .x8 .x10⟩,
   ⟨109, .SD .x10 .x31 1800⟩,
   ⟨110, .JAL .x0 132⟩]

private theorem actual : Fetched code instructions := by
  apply fetched_of_index
  · change ∀ k : Fin 87, _; intro k; fin_cases k <;> rfl
  · change ∀ k : Fin 87, _; decide

private def canonical (s : MachineState) := (s.setReg .x2 68719476336).setPC 4192

private theorem canonical_eq (s : MachineState) (p : s.pc = 4192)
    (sp : s.getReg .x2 = 68719476336) : canonical s = s := by
  have h : s.regs .x2 = 68719476336 := sp
  cases s
  simp only [canonical, MachineState.setPC, MachineState.setReg] at *
  congr 1
  · funext r; cases r <;> simp_all
  · exact p.symm

/-- Normalized effects of each actual instruction. Memory and register writes
retain input values symbolically and fixed addresses and PCs stay reduced. -/
private def effects (s : MachineState) : List (MachineState → MachineState) :=
  [fun t => (t.setReg .x2 68719474304).setPC 4196,
   fun t => (t.setMem 68719476328 (s.getReg .x1)).setPC 4200,
   fun t => (t.setMem 68719476320 (s.getReg .x8)).setPC 4204,
   fun t => (t.setMem 68719476312 (s.getReg .x9)).setPC 4208,
   fun t => (t.setMem 68719476304 (s.getReg .x18)).setPC 4212,
   fun t => (t.setMem 68719476296 (s.getReg .x19)).setPC 4216,
   fun t => (t.setMem 68719476288 (s.getReg .x20)).setPC 4220,
   fun t => (t.setMem 68719476280 (s.getReg .x21)).setPC 4224,
   fun t => (t.setMem 68719476272 (s.getReg .x22)).setPC 4228,
   fun t => (t.setMem 68719476264 (s.getReg .x23)).setPC 4232,
   fun t => (t.setMem 68719476256 (s.getReg .x24)).setPC 4236,
   fun t => (t.setMem 68719476248 (s.getReg .x25)).setPC 4240,
   fun t => (t.setMem 68719476240 (s.getReg .x26)).setPC 4244,
   fun t => (t.setMem 68719476232 (s.getReg .x27)).setPC 4248,
   fun t => (t.setReg .x8 68719476336).setPC 4252,
   fun t => (t.setReg .x2 68719474016).setPC 4256,
   fun t => (t.setReg .x12 ((s.getReg .x10) + 0)).setPC 4260,
   fun t => (t.setReg .x7 0).setPC 4264,
   fun t => (t.setReg .x10 18446744073709551615).setPC 4268,
   fun t => (t.setReg .x11 281474976710655).setPC 4272,
   fun t => (t.setReg .x13 4096).setPC 4276,
   fun t => (t.setReg .x13 68719472240).setPC 4280,
   fun t => (t.setMem 68719474096 281474976710655).setPC 4284,
   fun t => (t.setReg .x11 70368744177663).setPC 4288,
   fun t => (t.setReg .x13 4096).setPC 4292,
   fun t => (t.setReg .x13 68719472240).setPC 4296,
   fun t => (t.setMem 68719474088 70368744177663).setPC 4300,
   fun t => (t.setReg .x11 17592186044415).setPC 4304,
   fun t => (t.setReg .x13 4096).setPC 4308,
   fun t => (t.setReg .x13 68719472240).setPC 4312,
   fun t => (t.setMem 68719474080 17592186044415).setPC 4316,
   fun t => (t.setReg .x11 8589934591).setPC 4320,
   fun t => (t.setReg .x13 4096).setPC 4324,
   fun t => (t.setReg .x13 68719472240).setPC 4328,
   fun t => (t.setMem 68719474072 8589934591).setPC 4332,
   fun t => (t.setReg .x11 704643072).setPC 4336,
   fun t => (t.setReg .x11 704643565).setPC 4340,
   fun t => (t.setReg .x11 5637148520).setPC 4344,
   fun t => (t.setReg .x13 4096).setPC 4348,
   fun t => (t.setReg .x13 68719472240).setPC 4352,
   fun t => (t.setMem 68719474064 5637148520).setPC 4356,
   fun t => (t.setReg .x10 4294967295).setPC 4360,
   fun t => (t.setReg .x11 4096).setPC 4364,
   fun t => (t.setReg .x11 68719472240).setPC 4368,
   fun t => (t.setMem 68719474112 4294967295).setPC 4372,
   fun t => (t.setReg .x10 18446744071562067968).setPC 4376,
   fun t => (t.setReg .x10 2147483647).setPC 4380,
   fun t => (t.setReg .x11 4096).setPC 4384,
   fun t => (t.setReg .x11 68719472240).setPC 4388,
   fun t => (t.setMem 68719474104 2147483647).setPC 4392,
   fun t => (t.setReg .x10 1073741824).setPC 4396,
   fun t => (t.setReg .x10 1073741823).setPC 4400,
   fun t => (t.setReg .x11 4096).setPC 4404,
   fun t => (t.setReg .x11 68719472240).setPC 4408,
   fun t => (t.setMem 68719474056 1073741823).setPC 4412,
   fun t => (t.setReg .x10 536870912).setPC 4416,
   fun t => (t.setReg .x10 536870911).setPC 4420,
   fun t => (t.setReg .x11 4096).setPC 4424,
   fun t => (t.setReg .x11 68719472240).setPC 4428,
   fun t => (t.setMem 68719474048 536870911).setPC 4432,
   fun t => (t.setReg .x10 4096).setPC 4436,
   fun t => (t.setReg .x31 2051).setPC 4440,
   fun t => (t.setReg .x10 184549376).setPC 4444,
   fun t => (t.setReg .x10 184549505).setPC 4448,
   fun t => (t.setReg .x11 5905584160).setPC 4452,
   fun t => (t.setReg .x10 178958336).setPC 4456,
   fun t => (t.setReg .x10 2863333376).setPC 4460,
   fun t => (t.setReg .x13 4096).setPC 4464,
   fun t => (t.setReg .x13 68719472240).setPC 4468,
   fun t => (t.setMem 68719474032 2863333376).setPC 4472,
   fun t => (t.setReg .x10 65536).setPC 4476,
   fun t => (t.setReg .x10 65535).setPC 4480,
   fun t => (t.setReg .x13 4096).setPC 4484,
   fun t => (t.setReg .x13 68719472240).setPC 4488,
   fun t => (t.setMem 68719474024 65535).setPC 4492,
   fun t => (t.setReg .x6 68719474288).setPC 4496,
   fun t => (t.setReg .x6 68719474176).setPC 4500,
   fun t => (t.setReg .x10 322961408).setPC 4504,
   fun t => (t.setReg .x25 322961539).setPC 4508,
   fun t => (t.setReg .x25 10334769248).setPC 4512,
   fun t => (t.setReg .x10 134217728).setPC 4516,
   fun t => (t.setReg .x22 134217857).setPC 4520,
   fun t => (t.setReg .x22 4294971424).setPC 4524,
   fun t => (t.setReg .x10 4096).setPC 4528,
   fun t => (t.setReg .x10 68719472240).setPC 4532,
   fun t => (t.setMem 68719474040 2051).setPC 4536,
   fun t => t.setPC 4668]

private def after (s : MachineState) : Nat → MachineState
  | 0 => canonical s
  | n+1 => ((effects s)[n]?.getD id) (after s n)

private def opAt (i : Nat) := (instructions[i]?.getD (0,.EBREAK)).2

def entry (s : MachineState) := after s 87

private theorem op_in (i : Fin 87) : (24+i.val, opAt i.val) ∈ instructions := by
  have mem : (instructions[i.val]'(by exact i.isLt)) ∈ instructions := List.getElem_mem _
  have h : ∀ j : Fin 87, (instructions[j.val]'(by exact j.isLt)).1 = 24+j.val := by
    decide
  have key := h i
  have value : (instructions[i.val]'(by exact i.isLt)).2 = opAt i.val := by
    unfold opAt
    rw [List.getElem?_eq_getElem (show i.val < instructions.length from i.isLt)]
    rfl
  simpa only [←key,←value] using mem

private theorem step24 (s : MachineState) :
    ordinaryStep (after s 0) (.base (opAt 0)) = some (after s 1) := by
  let t := after s 0
  have pc : t.pc = 4192#64 := rfl
  have r2 : t.regs .x2 = 68719476336#64 := rfl
  change ordinaryStep t (.base (.ADDI .x2 .x2 2064)) = some ((t.setReg .x2 68719474304).setPC 4196)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, MachineState.setReg, signExtend12]

private theorem step25 (s : MachineState) :
    ordinaryStep (after s 1) (.base (opAt 1)) = some (after s 2) := by
  let t := after s 1
  have pc : t.pc = 4196#64 := rfl
  have r1 : t.regs .x1 = (s.getReg .x1) := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  change ordinaryStep t (.base (.SD .x2 .x1 2024)) = some ((t.setMem 68719476328 (s.getReg .x1)).setPC 4200)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r1, r2, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step26 (s : MachineState) :
    ordinaryStep (after s 2) (.base (opAt 2)) = some (after s 3) := by
  let t := after s 2
  have pc : t.pc = 4200#64 := rfl
  have r8 : t.regs .x8 = (s.getReg .x8) := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  change ordinaryStep t (.base (.SD .x2 .x8 2016)) = some ((t.setMem 68719476320 (s.getReg .x8)).setPC 4204)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r2, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step27 (s : MachineState) :
    ordinaryStep (after s 3) (.base (opAt 3)) = some (after s 4) := by
  let t := after s 3
  have pc : t.pc = 4204#64 := rfl
  have r9 : t.regs .x9 = (s.getReg .x9) := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  change ordinaryStep t (.base (.SD .x2 .x9 2008)) = some ((t.setMem 68719476312 (s.getReg .x9)).setPC 4208)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r9, r2, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step28 (s : MachineState) :
    ordinaryStep (after s 4) (.base (opAt 4)) = some (after s 5) := by
  let t := after s 4
  have pc : t.pc = 4208#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r18 : t.regs .x18 = (s.getReg .x18) := rfl
  change ordinaryStep t (.base (.SD .x2 .x18 2000)) = some ((t.setMem 68719476304 (s.getReg .x18)).setPC 4212)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r18, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step29 (s : MachineState) :
    ordinaryStep (after s 5) (.base (opAt 5)) = some (after s 6) := by
  let t := after s 5
  have pc : t.pc = 4212#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r19 : t.regs .x19 = (s.getReg .x19) := rfl
  change ordinaryStep t (.base (.SD .x2 .x19 1992)) = some ((t.setMem 68719476296 (s.getReg .x19)).setPC 4216)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r19, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step30 (s : MachineState) :
    ordinaryStep (after s 6) (.base (opAt 6)) = some (after s 7) := by
  let t := after s 6
  have pc : t.pc = 4216#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r20 : t.regs .x20 = (s.getReg .x20) := rfl
  change ordinaryStep t (.base (.SD .x2 .x20 1984)) = some ((t.setMem 68719476288 (s.getReg .x20)).setPC 4220)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r20, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step31 (s : MachineState) :
    ordinaryStep (after s 7) (.base (opAt 7)) = some (after s 8) := by
  let t := after s 7
  have pc : t.pc = 4220#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r21 : t.regs .x21 = (s.getReg .x21) := rfl
  change ordinaryStep t (.base (.SD .x2 .x21 1976)) = some ((t.setMem 68719476280 (s.getReg .x21)).setPC 4224)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r21, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step32 (s : MachineState) :
    ordinaryStep (after s 8) (.base (opAt 8)) = some (after s 9) := by
  let t := after s 8
  have pc : t.pc = 4224#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r22 : t.regs .x22 = (s.getReg .x22) := rfl
  change ordinaryStep t (.base (.SD .x2 .x22 1968)) = some ((t.setMem 68719476272 (s.getReg .x22)).setPC 4228)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r22, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step33 (s : MachineState) :
    ordinaryStep (after s 9) (.base (opAt 9)) = some (after s 10) := by
  let t := after s 9
  have pc : t.pc = 4228#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r23 : t.regs .x23 = (s.getReg .x23) := rfl
  change ordinaryStep t (.base (.SD .x2 .x23 1960)) = some ((t.setMem 68719476264 (s.getReg .x23)).setPC 4232)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r23, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step34 (s : MachineState) :
    ordinaryStep (after s 10) (.base (opAt 10)) = some (after s 11) := by
  let t := after s 10
  have pc : t.pc = 4232#64 := rfl
  have r24 : t.regs .x24 = (s.getReg .x24) := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  change ordinaryStep t (.base (.SD .x2 .x24 1952)) = some ((t.setMem 68719476256 (s.getReg .x24)).setPC 4236)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r24, r2, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step35 (s : MachineState) :
    ordinaryStep (after s 11) (.base (opAt 11)) = some (after s 12) := by
  let t := after s 11
  have pc : t.pc = 4236#64 := rfl
  have r25 : t.regs .x25 = (s.getReg .x25) := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  change ordinaryStep t (.base (.SD .x2 .x25 1944)) = some ((t.setMem 68719476248 (s.getReg .x25)).setPC 4240)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r25, r2, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step36 (s : MachineState) :
    ordinaryStep (after s 12) (.base (opAt 12)) = some (after s 13) := by
  let t := after s 12
  have pc : t.pc = 4240#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r26 : t.regs .x26 = (s.getReg .x26) := rfl
  change ordinaryStep t (.base (.SD .x2 .x26 1936)) = some ((t.setMem 68719476240 (s.getReg .x26)).setPC 4244)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r26, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step37 (s : MachineState) :
    ordinaryStep (after s 13) (.base (opAt 13)) = some (after s 14) := by
  let t := after s 13
  have pc : t.pc = 4244#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  have r27 : t.regs .x27 = (s.getReg .x27) := rfl
  change ordinaryStep t (.base (.SD .x2 .x27 1928)) = some ((t.setMem 68719476232 (s.getReg .x27)).setPC 4248)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, r27, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step38 (s : MachineState) :
    ordinaryStep (after s 14) (.base (opAt 14)) = some (after s 15) := by
  let t := after s 14
  have pc : t.pc = 4248#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  change ordinaryStep t (.base (.ADDI .x8 .x2 2032)) = some ((t.setReg .x8 68719476336).setPC 4252)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, MachineState.setReg, signExtend12]

private theorem step39 (s : MachineState) :
    ordinaryStep (after s 15) (.base (opAt 15)) = some (after s 16) := by
  let t := after s 15
  have pc : t.pc = 4252#64 := rfl
  have r2 : t.regs .x2 = 68719474304#64 := rfl
  change ordinaryStep t (.base (.ADDI .x2 .x2 3808)) = some ((t.setReg .x2 68719474016).setPC 4256)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r2, MachineState.setReg, signExtend12]

private theorem step40 (s : MachineState) :
    ordinaryStep (after s 16) (.base (opAt 16)) = some (after s 17) := by
  let t := after s 16
  have pc : t.pc = 4256#64 := rfl
  have r10 : t.regs .x10 = (s.getReg .x10) := rfl
  change ordinaryStep t (.base (.ADDI .x12 .x10 0)) = some ((t.setReg .x12 ((s.getReg .x10) + 0)).setPC 4260)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step41 (s : MachineState) :
    ordinaryStep (after s 17) (.base (opAt 17)) = some (after s 18) := by
  let t := after s 17
  have pc : t.pc = 4260#64 := rfl
  change ordinaryStep t (.base (.ADDI .x7 .x0 0)) = some ((t.setReg .x7 0).setPC 4264)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, MachineState.setReg, signExtend12]

private theorem step42 (s : MachineState) :
    ordinaryStep (after s 18) (.base (opAt 18)) = some (after s 19) := by
  let t := after s 18
  have pc : t.pc = 4264#64 := rfl
  change ordinaryStep t (.base (.ADDI .x10 .x0 4095)) = some ((t.setReg .x10 18446744073709551615).setPC 4268)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, MachineState.setReg, signExtend12]

private theorem step43 (s : MachineState) :
    ordinaryStep (after s 19) (.base (opAt 19)) = some (after s 20) := by
  let t := after s 19
  have pc : t.pc = 4268#64 := rfl
  have r10 : t.regs .x10 = 18446744073709551615#64 := rfl
  change ordinaryStep t (.base (.SRLI .x11 .x10 16)) = some ((t.setReg .x11 281474976710655).setPC 4272)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg]

private theorem step44 (s : MachineState) :
    ordinaryStep (after s 20) (.base (opAt 20)) = some (after s 21) := by
  let t := after s 20
  have pc : t.pc = 4272#64 := rfl
  change ordinaryStep t (.base (.LUI .x13 1)) = some ((t.setReg .x13 4096).setPC 4276)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step45 (s : MachineState) :
    ordinaryStep (after s 21) (.base (opAt 21)) = some (after s 22) := by
  let t := after s 21
  have pc : t.pc = 4276#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r13 : t.regs .x13 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x13 .x8 .x13)) = some ((t.setReg .x13 68719472240).setPC 4280)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r13, MachineState.setReg]

private theorem step46 (s : MachineState) :
    ordinaryStep (after s 22) (.base (opAt 22)) = some (after s 23) := by
  let t := after s 22
  have pc : t.pc = 4280#64 := rfl
  have r11 : t.regs .x11 = 281474976710655#64 := rfl
  have r13 : t.regs .x13 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x13 .x11 1856)) = some ((t.setMem 68719474096 281474976710655).setPC 4284)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r11, r13, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step47 (s : MachineState) :
    ordinaryStep (after s 23) (.base (opAt 23)) = some (after s 24) := by
  let t := after s 23
  have pc : t.pc = 4284#64 := rfl
  have r10 : t.regs .x10 = 18446744073709551615#64 := rfl
  change ordinaryStep t (.base (.SRLI .x11 .x10 18)) = some ((t.setReg .x11 70368744177663).setPC 4288)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg]

private theorem step48 (s : MachineState) :
    ordinaryStep (after s 24) (.base (opAt 24)) = some (after s 25) := by
  let t := after s 24
  have pc : t.pc = 4288#64 := rfl
  change ordinaryStep t (.base (.LUI .x13 1)) = some ((t.setReg .x13 4096).setPC 4292)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step49 (s : MachineState) :
    ordinaryStep (after s 25) (.base (opAt 25)) = some (after s 26) := by
  let t := after s 25
  have pc : t.pc = 4292#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r13 : t.regs .x13 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x13 .x8 .x13)) = some ((t.setReg .x13 68719472240).setPC 4296)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r13, MachineState.setReg]

private theorem step50 (s : MachineState) :
    ordinaryStep (after s 26) (.base (opAt 26)) = some (after s 27) := by
  let t := after s 26
  have pc : t.pc = 4296#64 := rfl
  have r11 : t.regs .x11 = 70368744177663#64 := rfl
  have r13 : t.regs .x13 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x13 .x11 1848)) = some ((t.setMem 68719474088 70368744177663).setPC 4300)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r11, r13, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step51 (s : MachineState) :
    ordinaryStep (after s 27) (.base (opAt 27)) = some (after s 28) := by
  let t := after s 27
  have pc : t.pc = 4300#64 := rfl
  have r10 : t.regs .x10 = 18446744073709551615#64 := rfl
  change ordinaryStep t (.base (.SRLI .x11 .x10 20)) = some ((t.setReg .x11 17592186044415).setPC 4304)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg]

private theorem step52 (s : MachineState) :
    ordinaryStep (after s 28) (.base (opAt 28)) = some (after s 29) := by
  let t := after s 28
  have pc : t.pc = 4304#64 := rfl
  change ordinaryStep t (.base (.LUI .x13 1)) = some ((t.setReg .x13 4096).setPC 4308)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step53 (s : MachineState) :
    ordinaryStep (after s 29) (.base (opAt 29)) = some (after s 30) := by
  let t := after s 29
  have pc : t.pc = 4308#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r13 : t.regs .x13 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x13 .x8 .x13)) = some ((t.setReg .x13 68719472240).setPC 4312)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r13, MachineState.setReg]

private theorem step54 (s : MachineState) :
    ordinaryStep (after s 30) (.base (opAt 30)) = some (after s 31) := by
  let t := after s 30
  have pc : t.pc = 4312#64 := rfl
  have r11 : t.regs .x11 = 17592186044415#64 := rfl
  have r13 : t.regs .x13 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x13 .x11 1840)) = some ((t.setMem 68719474080 17592186044415).setPC 4316)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r11, r13, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step55 (s : MachineState) :
    ordinaryStep (after s 31) (.base (opAt 31)) = some (after s 32) := by
  let t := after s 31
  have pc : t.pc = 4316#64 := rfl
  have r10 : t.regs .x10 = 18446744073709551615#64 := rfl
  change ordinaryStep t (.base (.SRLI .x11 .x10 31)) = some ((t.setReg .x11 8589934591).setPC 4320)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg]

private theorem step56 (s : MachineState) :
    ordinaryStep (after s 32) (.base (opAt 32)) = some (after s 33) := by
  let t := after s 32
  have pc : t.pc = 4320#64 := rfl
  change ordinaryStep t (.base (.LUI .x13 1)) = some ((t.setReg .x13 4096).setPC 4324)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step57 (s : MachineState) :
    ordinaryStep (after s 33) (.base (opAt 33)) = some (after s 34) := by
  let t := after s 33
  have pc : t.pc = 4324#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r13 : t.regs .x13 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x13 .x8 .x13)) = some ((t.setReg .x13 68719472240).setPC 4328)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r13, MachineState.setReg]

private theorem step58 (s : MachineState) :
    ordinaryStep (after s 34) (.base (opAt 34)) = some (after s 35) := by
  let t := after s 34
  have pc : t.pc = 4328#64 := rfl
  have r11 : t.regs .x11 = 8589934591#64 := rfl
  have r13 : t.regs .x13 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x13 .x11 1832)) = some ((t.setMem 68719474072 8589934591).setPC 4332)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r11, r13, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step59 (s : MachineState) :
    ordinaryStep (after s 35) (.base (opAt 35)) = some (after s 36) := by
  let t := after s 35
  have pc : t.pc = 4332#64 := rfl
  change ordinaryStep t (.base (.LUI .x11 172032)) = some ((t.setReg .x11 704643072).setPC 4336)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step60 (s : MachineState) :
    ordinaryStep (after s 36) (.base (opAt 36)) = some (after s 37) := by
  let t := after s 36
  have pc : t.pc = 4336#64 := rfl
  have r11 : t.regs .x11 = 704643072#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x11 .x11 493)) = some ((t.setReg .x11 704643565).setPC 4340)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r11, MachineState.setReg, signExtend12]

private theorem step61 (s : MachineState) :
    ordinaryStep (after s 37) (.base (opAt 37)) = some (after s 38) := by
  let t := after s 37
  have pc : t.pc = 4340#64 := rfl
  have r11 : t.regs .x11 = 704643565#64 := rfl
  change ordinaryStep t (.base (.SLLI .x11 .x11 3)) = some ((t.setReg .x11 5637148520).setPC 4344)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r11, MachineState.setReg]

private theorem step62 (s : MachineState) :
    ordinaryStep (after s 38) (.base (opAt 38)) = some (after s 39) := by
  let t := after s 38
  have pc : t.pc = 4344#64 := rfl
  change ordinaryStep t (.base (.LUI .x13 1)) = some ((t.setReg .x13 4096).setPC 4348)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step63 (s : MachineState) :
    ordinaryStep (after s 39) (.base (opAt 39)) = some (after s 40) := by
  let t := after s 39
  have pc : t.pc = 4348#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r13 : t.regs .x13 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x13 .x8 .x13)) = some ((t.setReg .x13 68719472240).setPC 4352)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r13, MachineState.setReg]

private theorem step64 (s : MachineState) :
    ordinaryStep (after s 40) (.base (opAt 40)) = some (after s 41) := by
  let t := after s 40
  have pc : t.pc = 4352#64 := rfl
  have r11 : t.regs .x11 = 5637148520#64 := rfl
  have r13 : t.regs .x13 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x13 .x11 1824)) = some ((t.setMem 68719474064 5637148520).setPC 4356)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r11, r13, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step65 (s : MachineState) :
    ordinaryStep (after s 41) (.base (opAt 41)) = some (after s 42) := by
  let t := after s 41
  have pc : t.pc = 4356#64 := rfl
  have r10 : t.regs .x10 = 18446744073709551615#64 := rfl
  change ordinaryStep t (.base (.SRLI .x10 .x10 32)) = some ((t.setReg .x10 4294967295).setPC 4360)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg]

private theorem step66 (s : MachineState) :
    ordinaryStep (after s 42) (.base (opAt 42)) = some (after s 43) := by
  let t := after s 42
  have pc : t.pc = 4360#64 := rfl
  change ordinaryStep t (.base (.LUI .x11 1)) = some ((t.setReg .x11 4096).setPC 4364)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step67 (s : MachineState) :
    ordinaryStep (after s 43) (.base (opAt 43)) = some (after s 44) := by
  let t := after s 43
  have pc : t.pc = 4364#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r11 : t.regs .x11 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x11 .x8 .x11)) = some ((t.setReg .x11 68719472240).setPC 4368)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r11, MachineState.setReg]

private theorem step68 (s : MachineState) :
    ordinaryStep (after s 44) (.base (opAt 44)) = some (after s 45) := by
  let t := after s 44
  have pc : t.pc = 4368#64 := rfl
  have r10 : t.regs .x10 = 4294967295#64 := rfl
  have r11 : t.regs .x11 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x11 .x10 1872)) = some ((t.setMem 68719474112 4294967295).setPC 4372)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, r11, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step69 (s : MachineState) :
    ordinaryStep (after s 45) (.base (opAt 45)) = some (after s 46) := by
  let t := after s 45
  have pc : t.pc = 4372#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 524288)) = some ((t.setReg .x10 18446744071562067968).setPC 4376)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step70 (s : MachineState) :
    ordinaryStep (after s 46) (.base (opAt 46)) = some (after s 47) := by
  let t := after s 46
  have pc : t.pc = 4376#64 := rfl
  have r10 : t.regs .x10 = 18446744071562067968#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x10 .x10 4095)) = some ((t.setReg .x10 2147483647).setPC 4380)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step71 (s : MachineState) :
    ordinaryStep (after s 47) (.base (opAt 47)) = some (after s 48) := by
  let t := after s 47
  have pc : t.pc = 4380#64 := rfl
  change ordinaryStep t (.base (.LUI .x11 1)) = some ((t.setReg .x11 4096).setPC 4384)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step72 (s : MachineState) :
    ordinaryStep (after s 48) (.base (opAt 48)) = some (after s 49) := by
  let t := after s 48
  have pc : t.pc = 4384#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r11 : t.regs .x11 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x11 .x8 .x11)) = some ((t.setReg .x11 68719472240).setPC 4388)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r11, MachineState.setReg]

private theorem step73 (s : MachineState) :
    ordinaryStep (after s 49) (.base (opAt 49)) = some (after s 50) := by
  let t := after s 49
  have pc : t.pc = 4388#64 := rfl
  have r10 : t.regs .x10 = 2147483647#64 := rfl
  have r11 : t.regs .x11 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x11 .x10 1864)) = some ((t.setMem 68719474104 2147483647).setPC 4392)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, r11, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step74 (s : MachineState) :
    ordinaryStep (after s 50) (.base (opAt 50)) = some (after s 51) := by
  let t := after s 50
  have pc : t.pc = 4392#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 262144)) = some ((t.setReg .x10 1073741824).setPC 4396)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step75 (s : MachineState) :
    ordinaryStep (after s 51) (.base (opAt 51)) = some (after s 52) := by
  let t := after s 51
  have pc : t.pc = 4396#64 := rfl
  have r10 : t.regs .x10 = 1073741824#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x10 .x10 4095)) = some ((t.setReg .x10 1073741823).setPC 4400)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step76 (s : MachineState) :
    ordinaryStep (after s 52) (.base (opAt 52)) = some (after s 53) := by
  let t := after s 52
  have pc : t.pc = 4400#64 := rfl
  change ordinaryStep t (.base (.LUI .x11 1)) = some ((t.setReg .x11 4096).setPC 4404)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step77 (s : MachineState) :
    ordinaryStep (after s 53) (.base (opAt 53)) = some (after s 54) := by
  let t := after s 53
  have pc : t.pc = 4404#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r11 : t.regs .x11 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x11 .x8 .x11)) = some ((t.setReg .x11 68719472240).setPC 4408)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r11, MachineState.setReg]

private theorem step78 (s : MachineState) :
    ordinaryStep (after s 54) (.base (opAt 54)) = some (after s 55) := by
  let t := after s 54
  have pc : t.pc = 4408#64 := rfl
  have r10 : t.regs .x10 = 1073741823#64 := rfl
  have r11 : t.regs .x11 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x11 .x10 1816)) = some ((t.setMem 68719474056 1073741823).setPC 4412)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, r11, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step79 (s : MachineState) :
    ordinaryStep (after s 55) (.base (opAt 55)) = some (after s 56) := by
  let t := after s 55
  have pc : t.pc = 4412#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 131072)) = some ((t.setReg .x10 536870912).setPC 4416)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step80 (s : MachineState) :
    ordinaryStep (after s 56) (.base (opAt 56)) = some (after s 57) := by
  let t := after s 56
  have pc : t.pc = 4416#64 := rfl
  have r10 : t.regs .x10 = 536870912#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x10 .x10 4095)) = some ((t.setReg .x10 536870911).setPC 4420)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step81 (s : MachineState) :
    ordinaryStep (after s 57) (.base (opAt 57)) = some (after s 58) := by
  let t := after s 57
  have pc : t.pc = 4420#64 := rfl
  change ordinaryStep t (.base (.LUI .x11 1)) = some ((t.setReg .x11 4096).setPC 4424)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step82 (s : MachineState) :
    ordinaryStep (after s 58) (.base (opAt 58)) = some (after s 59) := by
  let t := after s 58
  have pc : t.pc = 4424#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r11 : t.regs .x11 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x11 .x8 .x11)) = some ((t.setReg .x11 68719472240).setPC 4428)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r11, MachineState.setReg]

private theorem step83 (s : MachineState) :
    ordinaryStep (after s 59) (.base (opAt 59)) = some (after s 60) := by
  let t := after s 59
  have pc : t.pc = 4428#64 := rfl
  have r10 : t.regs .x10 = 536870911#64 := rfl
  have r11 : t.regs .x11 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x11 .x10 1808)) = some ((t.setMem 68719474048 536870911).setPC 4432)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, r11, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step84 (s : MachineState) :
    ordinaryStep (after s 60) (.base (opAt 60)) = some (after s 61) := by
  let t := after s 60
  have pc : t.pc = 4432#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 1)) = some ((t.setReg .x10 4096).setPC 4436)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step85 (s : MachineState) :
    ordinaryStep (after s 61) (.base (opAt 61)) = some (after s 62) := by
  let t := after s 61
  have pc : t.pc = 4436#64 := rfl
  have r10 : t.regs .x10 = 4096#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x31 .x10 2051)) = some ((t.setReg .x31 2051).setPC 4440)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step86 (s : MachineState) :
    ordinaryStep (after s 62) (.base (opAt 62)) = some (after s 63) := by
  let t := after s 62
  have pc : t.pc = 4440#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 45056)) = some ((t.setReg .x10 184549376).setPC 4444)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step87 (s : MachineState) :
    ordinaryStep (after s 63) (.base (opAt 63)) = some (after s 64) := by
  let t := after s 63
  have pc : t.pc = 4444#64 := rfl
  have r10 : t.regs .x10 = 184549376#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x10 .x10 129)) = some ((t.setReg .x10 184549505).setPC 4448)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step88 (s : MachineState) :
    ordinaryStep (after s 64) (.base (opAt 64)) = some (after s 65) := by
  let t := after s 64
  have pc : t.pc = 4448#64 := rfl
  have r10 : t.regs .x10 = 184549505#64 := rfl
  change ordinaryStep t (.base (.SLLI .x11 .x10 5)) = some ((t.setReg .x11 5905584160).setPC 4452)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg]

private theorem step89 (s : MachineState) :
    ordinaryStep (after s 65) (.base (opAt 65)) = some (after s 66) := by
  let t := after s 65
  have pc : t.pc = 4452#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 43691)) = some ((t.setReg .x10 178958336).setPC 4456)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step90 (s : MachineState) :
    ordinaryStep (after s 66) (.base (opAt 66)) = some (after s 67) := by
  let t := after s 66
  have pc : t.pc = 4456#64 := rfl
  have r10 : t.regs .x10 = 178958336#64 := rfl
  change ordinaryStep t (.base (.SLLI .x10 .x10 4)) = some ((t.setReg .x10 2863333376).setPC 4460)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg]

private theorem step91 (s : MachineState) :
    ordinaryStep (after s 67) (.base (opAt 67)) = some (after s 68) := by
  let t := after s 67
  have pc : t.pc = 4460#64 := rfl
  change ordinaryStep t (.base (.LUI .x13 1)) = some ((t.setReg .x13 4096).setPC 4464)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step92 (s : MachineState) :
    ordinaryStep (after s 68) (.base (opAt 68)) = some (after s 69) := by
  let t := after s 68
  have pc : t.pc = 4464#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r13 : t.regs .x13 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x13 .x8 .x13)) = some ((t.setReg .x13 68719472240).setPC 4468)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r13, MachineState.setReg]

private theorem step93 (s : MachineState) :
    ordinaryStep (after s 69) (.base (opAt 69)) = some (after s 70) := by
  let t := after s 69
  have pc : t.pc = 4468#64 := rfl
  have r10 : t.regs .x10 = 2863333376#64 := rfl
  have r13 : t.regs .x13 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x13 .x10 1792)) = some ((t.setMem 68719474032 2863333376).setPC 4472)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, r13, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step94 (s : MachineState) :
    ordinaryStep (after s 70) (.base (opAt 70)) = some (after s 71) := by
  let t := after s 70
  have pc : t.pc = 4472#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 16)) = some ((t.setReg .x10 65536).setPC 4476)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step95 (s : MachineState) :
    ordinaryStep (after s 71) (.base (opAt 71)) = some (after s 72) := by
  let t := after s 71
  have pc : t.pc = 4476#64 := rfl
  have r10 : t.regs .x10 = 65536#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x10 .x10 4095)) = some ((t.setReg .x10 65535).setPC 4480)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step96 (s : MachineState) :
    ordinaryStep (after s 72) (.base (opAt 72)) = some (after s 73) := by
  let t := after s 72
  have pc : t.pc = 4480#64 := rfl
  change ordinaryStep t (.base (.LUI .x13 1)) = some ((t.setReg .x13 4096).setPC 4484)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step97 (s : MachineState) :
    ordinaryStep (after s 73) (.base (opAt 73)) = some (after s 74) := by
  let t := after s 73
  have pc : t.pc = 4484#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r13 : t.regs .x13 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x13 .x8 .x13)) = some ((t.setReg .x13 68719472240).setPC 4488)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r13, MachineState.setReg]

private theorem step98 (s : MachineState) :
    ordinaryStep (after s 74) (.base (opAt 74)) = some (after s 75) := by
  let t := after s 74
  have pc : t.pc = 4488#64 := rfl
  have r10 : t.regs .x10 = 65535#64 := rfl
  have r13 : t.regs .x13 = 68719472240#64 := rfl
  change ordinaryStep t (.base (.SD .x13 .x10 1784)) = some ((t.setMem 68719474024 65535).setPC 4492)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, r13, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step99 (s : MachineState) :
    ordinaryStep (after s 75) (.base (opAt 75)) = some (after s 76) := by
  let t := after s 75
  have pc : t.pc = 4492#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  change ordinaryStep t (.base (.ADDI .x6 .x8 2048)) = some ((t.setReg .x6 68719474288).setPC 4496)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, MachineState.setReg, signExtend12]

private theorem step100 (s : MachineState) :
    ordinaryStep (after s 76) (.base (opAt 76)) = some (after s 77) := by
  let t := after s 76
  have pc : t.pc = 4496#64 := rfl
  have r6 : t.regs .x6 = 68719474288#64 := rfl
  change ordinaryStep t (.base (.ADDI .x6 .x6 3984)) = some ((t.setReg .x6 68719474176).setPC 4500)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r6, MachineState.setReg, signExtend12]

private theorem step101 (s : MachineState) :
    ordinaryStep (after s 77) (.base (opAt 77)) = some (after s 78) := by
  let t := after s 77
  have pc : t.pc = 4500#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 78848)) = some ((t.setReg .x10 322961408).setPC 4504)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step102 (s : MachineState) :
    ordinaryStep (after s 78) (.base (opAt 78)) = some (after s 79) := by
  let t := after s 78
  have pc : t.pc = 4504#64 := rfl
  have r10 : t.regs .x10 = 322961408#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x25 .x10 131)) = some ((t.setReg .x25 322961539).setPC 4508)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step103 (s : MachineState) :
    ordinaryStep (after s 79) (.base (opAt 79)) = some (after s 80) := by
  let t := after s 79
  have pc : t.pc = 4508#64 := rfl
  have r25 : t.regs .x25 = 322961539#64 := rfl
  change ordinaryStep t (.base (.SLLI .x25 .x25 5)) = some ((t.setReg .x25 10334769248).setPC 4512)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r25, MachineState.setReg]

private theorem step104 (s : MachineState) :
    ordinaryStep (after s 80) (.base (opAt 80)) = some (after s 81) := by
  let t := after s 80
  have pc : t.pc = 4512#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 32768)) = some ((t.setReg .x10 134217728).setPC 4516)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step105 (s : MachineState) :
    ordinaryStep (after s 81) (.base (opAt 81)) = some (after s 82) := by
  let t := after s 81
  have pc : t.pc = 4516#64 := rfl
  have r10 : t.regs .x10 = 134217728#64 := rfl
  change ordinaryStep t (.base (.ADDIW .x22 .x10 129)) = some ((t.setReg .x22 134217857).setPC 4520)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, MachineState.setReg, signExtend12]

private theorem step106 (s : MachineState) :
    ordinaryStep (after s 82) (.base (opAt 82)) = some (after s 83) := by
  let t := after s 82
  have pc : t.pc = 4520#64 := rfl
  have r22 : t.regs .x22 = 134217857#64 := rfl
  change ordinaryStep t (.base (.SLLI .x22 .x22 5)) = some ((t.setReg .x22 4294971424).setPC 4524)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r22, MachineState.setReg]

private theorem step107 (s : MachineState) :
    ordinaryStep (after s 83) (.base (opAt 83)) = some (after s 84) := by
  let t := after s 83
  have pc : t.pc = 4524#64 := rfl
  change ordinaryStep t (.base (.LUI .x10 1)) = some ((t.setReg .x10 4096).setPC 4528)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC, pc, MachineState.setReg]

private theorem step108 (s : MachineState) :
    ordinaryStep (after s 84) (.base (opAt 84)) = some (after s 85) := by
  let t := after s 84
  have pc : t.pc = 4528#64 := rfl
  have r8 : t.regs .x8 = 68719476336#64 := rfl
  have r10 : t.regs .x10 = 4096#64 := rfl
  change ordinaryStep t (.base (.SUB .x10 .x8 .x10)) = some ((t.setReg .x10 68719472240).setPC 4532)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r8, r10, MachineState.setReg]

private theorem step109 (s : MachineState) :
    ordinaryStep (after s 85) (.base (opAt 85)) = some (after s 86) := by
  let t := after s 85
  have pc : t.pc = 4532#64 := rfl
  have r10 : t.regs .x10 = 68719472240#64 := rfl
  have r31 : t.regs .x31 = 2051#64 := rfl
  change ordinaryStep t (.base (.SD .x10 .x31 1800)) = some ((t.setMem 68719474040 2051).setPC 4536)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, r10, r31, signExtend12, accessValid, rangeValid, MEMORY_BYTES]

private theorem step110 (s : MachineState) :
    ordinaryStep (after s 86) (.base (opAt 86)) = some (after s 87) := by
  let t := after s 86
  have pc : t.pc = 4536#64 := rfl
  change ordinaryStep t (.base (.JAL .x0 132)) = some (t.setPC 4668)
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg, MachineState.setPC, pc, MachineState.setReg, signExtend21]

private theorem step (s : MachineState) (i : Fin 87) :
    ordinaryStep (after s i.val) (.base (opAt i.val)) = some (after s (i.val+1)) := by
  fin_cases i
  case «0» => exact step24 s
  case «1» => exact step25 s
  case «2» => exact step26 s
  case «3» => exact step27 s
  case «4» => exact step28 s
  case «5» => exact step29 s
  case «6» => exact step30 s
  case «7» => exact step31 s
  case «8» => exact step32 s
  case «9» => exact step33 s
  case «10» => exact step34 s
  case «11» => exact step35 s
  case «12» => exact step36 s
  case «13» => exact step37 s
  case «14» => exact step38 s
  case «15» => exact step39 s
  case «16» => exact step40 s
  case «17» => exact step41 s
  case «18» => exact step42 s
  case «19» => exact step43 s
  case «20» => exact step44 s
  case «21» => exact step45 s
  case «22» => exact step46 s
  case «23» => exact step47 s
  case «24» => exact step48 s
  case «25» => exact step49 s
  case «26» => exact step50 s
  case «27» => exact step51 s
  case «28» => exact step52 s
  case «29» => exact step53 s
  case «30» => exact step54 s
  case «31» => exact step55 s
  case «32» => exact step56 s
  case «33» => exact step57 s
  case «34» => exact step58 s
  case «35» => exact step59 s
  case «36» => exact step60 s
  case «37» => exact step61 s
  case «38» => exact step62 s
  case «39» => exact step63 s
  case «40» => exact step64 s
  case «41» => exact step65 s
  case «42» => exact step66 s
  case «43» => exact step67 s
  case «44» => exact step68 s
  case «45» => exact step69 s
  case «46» => exact step70 s
  case «47» => exact step71 s
  case «48» => exact step72 s
  case «49» => exact step73 s
  case «50» => exact step74 s
  case «51» => exact step75 s
  case «52» => exact step76 s
  case «53» => exact step77 s
  case «54» => exact step78 s
  case «55» => exact step79 s
  case «56» => exact step80 s
  case «57» => exact step81 s
  case «58» => exact step82 s
  case «59» => exact step83 s
  case «60» => exact step84 s
  case «61» => exact step85 s
  case «62» => exact step86 s
  case «63» => exact step87 s
  case «64» => exact step88 s
  case «65» => exact step89 s
  case «66» => exact step90 s
  case «67» => exact step91 s
  case «68» => exact step92 s
  case «69» => exact step93 s
  case «70» => exact step94 s
  case «71» => exact step95 s
  case «72» => exact step96 s
  case «73» => exact step97 s
  case «74» => exact step98 s
  case «75» => exact step99 s
  case «76» => exact step100 s
  case «77» => exact step101 s
  case «78» => exact step102 s
  case «79» => exact step103 s
  case «80» => exact step104 s
  case «81» => exact step105 s
  case «82» => exact step106 s
  case «83» => exact step107 s
  case «84» => exact step108 s
  case «85» => exact step109 s
  case «86» => exact step110 s

private theorem pc_at (s : MachineState) (i : Fin 87) :
    (after s i.val).pc = BitVec.ofNat 64 (4096 + 4*(24+i.val)) := by
  fin_cases i <;> rfl

private theorem price (i : Fin 87) : instructionCycles (.base (opAt i.val)) = 1 := by
  fin_cases i <;> rfl

theorem execute_setup (s : MachineState) (p : s.pc = 4192)
    (sp : s.getReg .x2 = 68719476336) (fuel : Nat) (coins : Bool) :
    execute code (87+fuel) s coins =
      (do let r ← execute code fuel (entry s) coins; return r.charge 87 0) := by
  have start : after s 0 = s := canonical_eq s p sp
  have run := execute_unit_steps code 87 fuel _ coins (fun i hi => ⟨_, actual _ _ (op_in ⟨i,hi⟩)
    _ (pc_at s ⟨i,hi⟩), step s ⟨i,hi⟩,price ⟨i,hi⟩⟩)
  rwa [start] at run

theorem entry_registers (s : MachineState) :
    (entry s).pc = 4668 ∧ (entry s).getReg .x2 = 68719474016 ∧
    (entry s).getReg .x8 = 68719476336 ∧ (entry s).getReg .x6 = 68719474176 ∧
    (entry s).getReg .x7 = 0 ∧ (entry s).getReg .x12 = s.getReg .x10 ∧
    (entry s).getReg .x25 = 10334769248 ∧ (entry s).getReg .x22 = 4294971424 ∧
    (entry s).getMem 68719476328 = s.getReg .x1 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl⟩
  change s.getReg .x10 + 0 = s.getReg .x10
  simp

/-- Stack writes in program order. The ABI tables, input buffers, cap and
output proof all lie below this stack frame. -/
private def stackWrites (s : MachineState) : List (Word × Word) :=
  [(68719476328,(s.getReg .x1)),
   (68719476320,(s.getReg .x8)),
   (68719476312,(s.getReg .x9)),
   (68719476304,(s.getReg .x18)),
   (68719476296,(s.getReg .x19)),
   (68719476288,(s.getReg .x20)),
   (68719476280,(s.getReg .x21)),
   (68719476272,(s.getReg .x22)),
   (68719476264,(s.getReg .x23)),
   (68719476256,(s.getReg .x24)),
   (68719476248,(s.getReg .x25)),
   (68719476240,(s.getReg .x26)),
   (68719476232,(s.getReg .x27)),
   (68719474096,281474976710655),
   (68719474088,70368744177663),
   (68719474080,17592186044415),
   (68719474072,8589934591),
   (68719474064,5637148520),
   (68719474112,4294967295),
   (68719474104,2147483647),
   (68719474056,1073741823),
   (68719474048,536870911),
   (68719474032,2863333376),
   (68719474024,65535),
   (68719474040,2051)]

private def put (m : Word → Word) (cell : Word × Word) :=
  fun a => if a == cell.1 then cell.2 else m a

private theorem fold_frame (cells : List (Word × Word)) (m : Word → Word) (addr : Word)
    (disjoint : ∀ c ∈ cells, addr ≠ c.1) : (cells.foldl put m) addr = m addr := by
  induction cells generalizing m with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons,ih _ (fun p hp => disjoint p (List.mem_cons_of_mem _ hp))]
    simp [put,disjoint c List.mem_cons_self]

theorem entry_frame (s : MachineState) (a : Word) (below : a.toNat < 68719474016) :
    (entry s).getMem a = s.getMem a := by
  have view : (entry s).getMem a = ((stackWrites s).foldl put s.mem) a := by rfl
  rw [view]
  apply fold_frame
  have low : ∀ c ∈ stackWrites s, 68719474016 ≤ c.1.toNat := by
    intro c hc
    simp only [stackWrites,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only <;> decide
  intro cell member same
  have lim := low cell member
  rw [←same] at lim
  omega

theorem entry_constants (s : MachineState) :
    (entry s).getReg .x11 = 5905584160 ∧ (entry s).getReg .x31 = 2051 ∧
    (entry s).getMem 68719474040 = 2051 := by exact ⟨rfl,rfl,rfl⟩

end CommitGolfCandidate.Reconstruction.HonestOpeningStart
