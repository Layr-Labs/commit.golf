import CommitGolfCandidate.TruncCheckFetch
import CommitGolfCandidate.TruncRecordExit
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000

def simple : Instr → Bool
  | .LD .. | .SD .. | .SB .. | .LBU .. | .ADDI .. | .ADD .. | .SLLI .. | .SRLI .. => true
  | _ => false

def stepPrefix (ops : List Instr) (s : MachineState) (i : Nat) :=
  (ops.take i).foldl execInstrBr s

def safeSteps (ops : List Instr) (s : MachineState) :=
  ∀ i : Fin ops.length, memoryArgumentsValid (stepPrefix ops s i.val) ops[i] = true

private theorem simpleStep (s : MachineState) (op : Instr) (isSimple : simple op)
    (mem : memoryArgumentsValid s op) :
    ordinaryStep s (.base op) = some (execInstrBr s op) ∧
      (execInstrBr s op).pc = s.pc + 4 ∧ instructionCycles (.base op) = 1 := by
  cases op <;> simp [simple] at isSimple <;> simp [ordinaryStep,mem,execInstrBr,instructionCycles,MachineState.setPC]

private theorem simplePC (s : MachineState) (op : Instr) (isSimple : simple op) :
    (execInstrBr s op).pc = s.pc + 4 := by
  cases op <;> simp [simple] at isSimple <;> rfl

theorem plainBlock (ops : List Instr) (start : Nat) (within : start+ops.length≤2048)
    (plain : ∀ i : Fin ops.length, simple ops[i])
    (enc : ∀ i : Fin ops.length, ((Trunc.wireImage true).code[start+i.val]?).bind decodeInstruction =
      some (.base ops[i])) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*start))
    (safe : safeSteps ops s) (fuel : Nat) (coins : Bool) :
    execute (Trunc.wireImage true) (ops.length+fuel) s coins =
    (do let next ← execute (Trunc.wireImage true) fuel (ops.foldl execInstrBr s) coins
        return next.charge ops.length 0) := by
  have succ (i : Nat) (hi : i<ops.length) : stepPrefix ops s (i+1) = execInstrBr (stepPrefix ops s i) ops[i] := by
    unfold stepPrefix; rw [List.take_succ_eq_append_getElem hi, List.foldl_append]; rfl
  have pcs (i : Nat) (bi : i ≤ ops.length) :
      (stepPrefix ops s i).pc = BitVec.ofNat 64 (4096+4*(start+i)) := by
    induction i with
    | zero => simpa [stepPrefix] using pc
    | succ i ih =>
      have pl : simple ops[i] := plain ⟨i,by omega⟩
      rw [succ i (by omega),simplePC _ _ pl,ih (by omega),
        show 4096+4*(start+(i+1)) = (4096+4*(start+i))+4 by omega]
      exact (BitVec.ofNat_add (4096+4*(start+i)) 4).symm
  have run := execute_unit_steps (Trunc.wireImage true) ops.length fuel (stepPrefix ops s) coins (by
    intro i hi
    refine ⟨.base ops[i],fetchAt _ _ _ _ (by omega) (pcs i (by omega)) (enc ⟨i,hi⟩),?_,?_⟩
    · rw [succ i hi]; exact (simpleStep _ _ (plain ⟨i,hi⟩) (safe ⟨i,hi⟩)).1
    · exact (simpleStep _ _ (plain ⟨i,hi⟩) (safe ⟨i,hi⟩)).2.2)
  simpa only [stepPrefix,List.take_zero,List.foldl_nil,List.take_length] using run
end CommitGolfCandidate.Trunc
