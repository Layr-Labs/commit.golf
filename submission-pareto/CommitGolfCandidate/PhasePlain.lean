import CommitGolfCandidate.PhaseTrace
import CommitGolfCandidate.PhaseImage

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate OracleComp
set_option maxHeartbeats 2500000
set_option maxRecDepth 16000
attribute [local irreducible] execute

def plainOps : List Instr := [
  .ADD .x28 .x28 .x7,
  .ADD .x6 .x6 .x19,
  .ADD .x7 .x22 .x7,
  .ADD .x7 .x26 .x7,
  .ADD .x7 .x7 .x24,
  .ADD .x7 .x9 .x7,
  .ADDI .x18 .x18 4095,
  .ADDI .x21 .x21 16,
  .ADDI .x21 .x21 30,
  .ADDI .x21 .x21 32,
  .ADDI .x21 .x21 96,
  .ADDI .x28 .x28 72,
  .ADDI .x8 .x8 8,
  .ANDI .x10 .x6 3,
  .MUL .x7 .x7 .x4,
  .LD .x6 .x8 0,
  .SD .x7 .x23 0,
  .SLLI .x28 .x28 5,
  .SLLI .x7 .x6 3,
  .SLLI .x7 .x6 4,
  .SRLI .x7 .x6 2,
  .SLLI .x7 .x7 5,
  .SRLI .x6 .x6 1,
  .SRLI .x6 .x6 2,
  .XORI .x28 .x10 1,
  .XORI .x28 .x10 2,
  .XORI .x28 .x10 3,
  .XORI .x7 .x6 1]

def beforeOps (f : Fin 18) : List Instr :=
  match f.val with
  | 0 => [.LD .x6 .x8 0, .SLLI .x7 .x6 4, .ADD .x7 .x22 .x7]
  | 1 => [.ADDI .x21 .x21 16, .SRLI .x7 .x6 2, .MUL .x7 .x7 .x4, .ADD .x7 .x7 .x24, .ANDI .x10 .x6 3, .XORI .x28 .x10 1, .SLLI .x28 .x28 5, .ADD .x28 .x28 .x7, .ADDI .x28 .x28 72]
  | 2 => [.XORI .x28 .x10 2, .SLLI .x28 .x28 5, .ADD .x28 .x28 .x7, .ADDI .x28 .x28 72]
  | 3 => [.XORI .x28 .x10 3, .SLLI .x28 .x28 5, .ADD .x28 .x28 .x7, .ADDI .x28 .x28 72]
  | 4 => [.ADDI .x21 .x21 96, .SRLI .x6 .x6 2, .ADD .x6 .x6 .x19, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 5 => [.ADDI .x21 .x21 32, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 6 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 7 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 8 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 9 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 10 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 11 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 12 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 13 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 14 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 15 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 16 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | 17 => [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7]
  | _ => []
def lastOps : List Instr := [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1, .SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .SD .x7 .x23 0, .ADDI .x8 .x8 8, .ADDI .x18 .x18 4095]
def beforePC (p : Fin 4) (f : Fin 18) := fieldPC p f-(beforeOps f).length
def lastPC (p : Fin 4) := fieldPC p 17+2*(widths p 17).length

private theorem op_member : ∀ f : Fin 18, (beforeOps f).all (fun x => decide (x∈plainOps))=true := by decide

theorem before_member (f : Fin 18) (op : Instr) (inside : op∈beforeOps f) : op∈plainOps :=
  of_decide_eq_true (List.all_eq_true.mp (op_member f) _ inside)

theorem last_member (op : Instr) (inside : op∈lastOps) : op∈plainOps :=
  of_decide_eq_true (List.all_eq_true.mp
    (show lastOps.all (fun x => decide (x∈plainOps))=true by decide) _ inside)

def opsDecoded (p : Fin 4) (ws : List Instr) (atPC : Nat) : Bool :=
  (List.range ws.length).all fun j => decodeAt (atPC+j) == ws[j]?

private theorem before_0_0 : opsDecoded 0 (beforeOps 0) (beforePC 0 0)=true := by decide
private theorem before_0_1 : opsDecoded 0 (beforeOps 1) (beforePC 0 1)=true := by decide
private theorem before_0_2 : opsDecoded 0 (beforeOps 2) (beforePC 0 2)=true := by decide
private theorem before_0_3 : opsDecoded 0 (beforeOps 3) (beforePC 0 3)=true := by decide
private theorem before_0_4 : opsDecoded 0 (beforeOps 4) (beforePC 0 4)=true := by decide
private theorem before_0_5 : opsDecoded 0 (beforeOps 5) (beforePC 0 5)=true := by decide
private theorem before_0_6 : opsDecoded 0 (beforeOps 6) (beforePC 0 6)=true := by decide
private theorem before_0_7 : opsDecoded 0 (beforeOps 7) (beforePC 0 7)=true := by decide
private theorem before_0_8 : opsDecoded 0 (beforeOps 8) (beforePC 0 8)=true := by decide
private theorem before_0_9 : opsDecoded 0 (beforeOps 9) (beforePC 0 9)=true := by decide
private theorem before_0_10 : opsDecoded 0 (beforeOps 10) (beforePC 0 10)=true := by decide
private theorem before_0_11 : opsDecoded 0 (beforeOps 11) (beforePC 0 11)=true := by decide
private theorem before_0_12 : opsDecoded 0 (beforeOps 12) (beforePC 0 12)=true := by decide
private theorem before_0_13 : opsDecoded 0 (beforeOps 13) (beforePC 0 13)=true := by decide
private theorem before_0_14 : opsDecoded 0 (beforeOps 14) (beforePC 0 14)=true := by decide
private theorem before_0_15 : opsDecoded 0 (beforeOps 15) (beforePC 0 15)=true := by decide
private theorem before_0_16 : opsDecoded 0 (beforeOps 16) (beforePC 0 16)=true := by decide
private theorem before_0_17 : opsDecoded 0 (beforeOps 17) (beforePC 0 17)=true := by decide
private theorem before_1_0 : opsDecoded 1 (beforeOps 0) (beforePC 1 0)=true := by decide
private theorem before_1_1 : opsDecoded 1 (beforeOps 1) (beforePC 1 1)=true := by decide
private theorem before_1_2 : opsDecoded 1 (beforeOps 2) (beforePC 1 2)=true := by decide
private theorem before_1_3 : opsDecoded 1 (beforeOps 3) (beforePC 1 3)=true := by decide
private theorem before_1_4 : opsDecoded 1 (beforeOps 4) (beforePC 1 4)=true := by decide
private theorem before_1_5 : opsDecoded 1 (beforeOps 5) (beforePC 1 5)=true := by decide
private theorem before_1_6 : opsDecoded 1 (beforeOps 6) (beforePC 1 6)=true := by decide
private theorem before_1_7 : opsDecoded 1 (beforeOps 7) (beforePC 1 7)=true := by decide
private theorem before_1_8 : opsDecoded 1 (beforeOps 8) (beforePC 1 8)=true := by decide
private theorem before_1_9 : opsDecoded 1 (beforeOps 9) (beforePC 1 9)=true := by decide
private theorem before_1_10 : opsDecoded 1 (beforeOps 10) (beforePC 1 10)=true := by decide
private theorem before_1_11 : opsDecoded 1 (beforeOps 11) (beforePC 1 11)=true := by decide
private theorem before_1_12 : opsDecoded 1 (beforeOps 12) (beforePC 1 12)=true := by decide
private theorem before_1_13 : opsDecoded 1 (beforeOps 13) (beforePC 1 13)=true := by decide
private theorem before_1_14 : opsDecoded 1 (beforeOps 14) (beforePC 1 14)=true := by decide
private theorem before_1_15 : opsDecoded 1 (beforeOps 15) (beforePC 1 15)=true := by decide
private theorem before_1_16 : opsDecoded 1 (beforeOps 16) (beforePC 1 16)=true := by decide
private theorem before_1_17 : opsDecoded 1 (beforeOps 17) (beforePC 1 17)=true := by decide
private theorem before_2_0 : opsDecoded 2 (beforeOps 0) (beforePC 2 0)=true := by decide
private theorem before_2_1 : opsDecoded 2 (beforeOps 1) (beforePC 2 1)=true := by decide
private theorem before_2_2 : opsDecoded 2 (beforeOps 2) (beforePC 2 2)=true := by decide
private theorem before_2_3 : opsDecoded 2 (beforeOps 3) (beforePC 2 3)=true := by decide
private theorem before_2_4 : opsDecoded 2 (beforeOps 4) (beforePC 2 4)=true := by decide
private theorem before_2_5 : opsDecoded 2 (beforeOps 5) (beforePC 2 5)=true := by decide
private theorem before_2_6 : opsDecoded 2 (beforeOps 6) (beforePC 2 6)=true := by decide
private theorem before_2_7 : opsDecoded 2 (beforeOps 7) (beforePC 2 7)=true := by decide
private theorem before_2_8 : opsDecoded 2 (beforeOps 8) (beforePC 2 8)=true := by decide
private theorem before_2_9 : opsDecoded 2 (beforeOps 9) (beforePC 2 9)=true := by decide
private theorem before_2_10 : opsDecoded 2 (beforeOps 10) (beforePC 2 10)=true := by decide
private theorem before_2_11 : opsDecoded 2 (beforeOps 11) (beforePC 2 11)=true := by decide
private theorem before_2_12 : opsDecoded 2 (beforeOps 12) (beforePC 2 12)=true := by decide
private theorem before_2_13 : opsDecoded 2 (beforeOps 13) (beforePC 2 13)=true := by decide
private theorem before_2_14 : opsDecoded 2 (beforeOps 14) (beforePC 2 14)=true := by decide
private theorem before_2_15 : opsDecoded 2 (beforeOps 15) (beforePC 2 15)=true := by decide
private theorem before_2_16 : opsDecoded 2 (beforeOps 16) (beforePC 2 16)=true := by decide
private theorem before_2_17 : opsDecoded 2 (beforeOps 17) (beforePC 2 17)=true := by decide
private theorem before_3_0 : opsDecoded 3 (beforeOps 0) (beforePC 3 0)=true := by decide
private theorem before_3_1 : opsDecoded 3 (beforeOps 1) (beforePC 3 1)=true := by decide
private theorem before_3_2 : opsDecoded 3 (beforeOps 2) (beforePC 3 2)=true := by decide
private theorem before_3_3 : opsDecoded 3 (beforeOps 3) (beforePC 3 3)=true := by decide
private theorem before_3_4 : opsDecoded 3 (beforeOps 4) (beforePC 3 4)=true := by decide
private theorem before_3_5 : opsDecoded 3 (beforeOps 5) (beforePC 3 5)=true := by decide
private theorem before_3_6 : opsDecoded 3 (beforeOps 6) (beforePC 3 6)=true := by decide
private theorem before_3_7 : opsDecoded 3 (beforeOps 7) (beforePC 3 7)=true := by decide
private theorem before_3_8 : opsDecoded 3 (beforeOps 8) (beforePC 3 8)=true := by decide
private theorem before_3_9 : opsDecoded 3 (beforeOps 9) (beforePC 3 9)=true := by decide
private theorem before_3_10 : opsDecoded 3 (beforeOps 10) (beforePC 3 10)=true := by decide
private theorem before_3_11 : opsDecoded 3 (beforeOps 11) (beforePC 3 11)=true := by decide
private theorem before_3_12 : opsDecoded 3 (beforeOps 12) (beforePC 3 12)=true := by decide
private theorem before_3_13 : opsDecoded 3 (beforeOps 13) (beforePC 3 13)=true := by decide
private theorem before_3_14 : opsDecoded 3 (beforeOps 14) (beforePC 3 14)=true := by decide
private theorem before_3_15 : opsDecoded 3 (beforeOps 15) (beforePC 3 15)=true := by decide
private theorem before_3_16 : opsDecoded 3 (beforeOps 16) (beforePC 3 16)=true := by decide
private theorem before_3_17 : opsDecoded 3 (beforeOps 17) (beforePC 3 17)=true := by decide
theorem before_decoded (p : Fin 4) (f : Fin 18) : opsDecoded p (beforeOps f) (beforePC p f)=true := by
  fin_cases p <;> fin_cases f
  · exact before_0_0
  · exact before_0_1
  · exact before_0_2
  · exact before_0_3
  · exact before_0_4
  · exact before_0_5
  · exact before_0_6
  · exact before_0_7
  · exact before_0_8
  · exact before_0_9
  · exact before_0_10
  · exact before_0_11
  · exact before_0_12
  · exact before_0_13
  · exact before_0_14
  · exact before_0_15
  · exact before_0_16
  · exact before_0_17
  · exact before_1_0
  · exact before_1_1
  · exact before_1_2
  · exact before_1_3
  · exact before_1_4
  · exact before_1_5
  · exact before_1_6
  · exact before_1_7
  · exact before_1_8
  · exact before_1_9
  · exact before_1_10
  · exact before_1_11
  · exact before_1_12
  · exact before_1_13
  · exact before_1_14
  · exact before_1_15
  · exact before_1_16
  · exact before_1_17
  · exact before_2_0
  · exact before_2_1
  · exact before_2_2
  · exact before_2_3
  · exact before_2_4
  · exact before_2_5
  · exact before_2_6
  · exact before_2_7
  · exact before_2_8
  · exact before_2_9
  · exact before_2_10
  · exact before_2_11
  · exact before_2_12
  · exact before_2_13
  · exact before_2_14
  · exact before_2_15
  · exact before_2_16
  · exact before_2_17
  · exact before_3_0
  · exact before_3_1
  · exact before_3_2
  · exact before_3_3
  · exact before_3_4
  · exact before_3_5
  · exact before_3_6
  · exact before_3_7
  · exact before_3_8
  · exact before_3_9
  · exact before_3_10
  · exact before_3_11
  · exact before_3_12
  · exact before_3_13
  · exact before_3_14
  · exact before_3_15
  · exact before_3_16
  · exact before_3_17
theorem last_decoded (p : Fin 4) : opsDecoded p lastOps (lastPC p)=true := by
  exact (show ∀ q : Fin 4, opsDecoded q lastOps (lastPC q)=true by decide) p

theorem source_rows_range (p : Fin 4) (f : Fin 18) : 762≤beforePC p f ∧
    beforePC p f+(beforeOps f).length=fieldPC p f ∧ fieldPC p f≤2680 := by
  exact (show ∀ t : Fin 4, ∀ j : Fin 18, 762≤beforePC t j ∧
    beforePC t j+(beforeOps j).length=fieldPC t j ∧ fieldPC t j≤2680 by decide) p f

theorem tail_rows_range (p : Fin 4) : 762≤lastPC p ∧ lastPC p+lastOps.length≤2680 := by
  exact (show ∀ t : Fin 4, 762≤lastPC t ∧ lastPC t+lastOps.length≤2680 by decide) p

theorem decoded_rows (pi : Image) (p : Fin 4) (xs : List Instr) (base j : Nat)
    (d : opsDecoded p xs base=true) (inside : j<xs.length) (low : 761≤base) (high : base+xs.length≤2680)
    (s : MachineState) (pc : s.pc=addr (4096+4*(base+j))) :
    fetch (stitched pi) s=some (.base xs[j]) := by
  have dec:=List.all_eq_true.mp d j (List.mem_range.mpr inside)
  apply stitched_fetch pi _ _ s (by omega) (by omega) _ pc
  simpa [List.getElem?_eq_getElem inside] using of_decide_eq_true (show decide (decodeAt (base+j) = xs[j]?)=true by
    simpa only [decide_eq_true_eq,beq_iff_eq] using dec)

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

private theorem lifted (old actual : MachineState) (same : Rel old actual) (k : Reg) (safe : k≠.x31) :
    old.getReg k=actual.getReg k := same.reg k safe

def surcharge : Instr → Nat
  | .MUL _ _ _ => 3
  | _ => 0
def extraOps : List Instr → Nat
  | [] => 0
  | op::ops => surcharge op+extraOps ops

theorem plain_rel (old actual : MachineState) (same : Rel old actual) (op : Instr) (inOps : op∈plainOps) :
    Rel (execInstrBr old op) (execInstrBr actual op) ∧
    (execInstrBr actual op).pc=actual.pc+4 ∧ instructionCycles (.base op)=1+surcharge op := by
  have registers (r : Reg) (safe : r ≠ .x31 := by decide) := same.reg r safe
  have memory := same.mem
  simp only [plainOps,List.mem_cons,List.not_mem_nil,or_false] at inOps
  rcases inOps with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals refine ⟨⟨?_,?_⟩,rfl,rfl⟩
  all_goals first
    | solve | simp [execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.setMem,
         MachineState.getMem,memory,registers .x4,registers .x6,registers .x7,registers .x8,registers .x9,registers .x10,registers .x18,registers .x19,registers .x21,registers .x22,registers .x23,registers .x24,registers .x26,registers .x28]
    | intro r hr
      simp [execInstrBr,MachineState.getMem,memory,same.reg r hr,registers .x4,registers .x6,registers .x7,registers .x8,registers .x9,registers .x10,registers .x18,registers .x19,registers .x21,registers .x22,registers .x23,registers .x24,registers .x26,registers .x28]

#print axioms plain_rel
end TwoPermutationPrototype.PhaseOpening
