import CommitGolfCandidate.TruncMoveRun
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
def control : Instr → Bool
  | .ADDI .. | .SLLI .. | .BNE .. | .BEQ .. | .JAL .. => true
  | _=>false
def straight : Instr → Bool
  | .ADDI .. | .SLLI .. =>true
  | _=>false
private theorem controlOK (s : MachineState) (op : Instr) (h : control op=true) :
    ordinaryStep s (.base op)=some (execInstrBr s op) ∧ instructionCycles (.base op)=1 := by
  cases op <;> simp [control] at h <;> exact ⟨rfl,rfl⟩
private theorem straightPC (s : MachineState) (op : Instr) (h : straight op=true) : (execInstrBr s op).pc=s.pc+4 := by
  cases op <;> simp [straight] at h <;> rfl

theorem controlRun (im : Image) (i : Nat) (ops : List Instr) (s : MachineState) (pc : s.pc=loc i)
    (space : i+ops.length≤2048) (enc : Slice im i ops)
    (ctrl : ∀ j : Fin ops.length,control ops[j]=true)
    (plain : ∀ j : Fin ops.length,j.val+1<ops.length → straight ops[j]=true) :
    Runs im s (ops.foldl execInstrBr s) ops.length ops.length := by
  have succ (j : Nat) (hj : j<ops.length) : blockPrefix ops s (j+1)=execInstrBr (blockPrefix ops s j) ops[j] := by
    unfold blockPrefix;rw [List.take_succ_eq_append_getElem hj,List.foldl_append];rfl
  have addr (j : Nat) (hj : j<ops.length) : (blockPrefix ops s j).pc=loc (i+j) := by
    induction j with
    | zero=>exact pc
    | succ j ih =>
      have ok : straight ops[j]=true:=plain ⟨j,by omega⟩ hj
      rw [succ j (by omega),straightPC _ _ ok,ih (by omega)]
      unfold loc;exact ofNat64_add_eq _ 4 _ (by omega)
  intro fuel coin
  have endEq : ops.foldl execInstrBr s=blockPrefix ops s ops.length := by simp [blockPrefix]
  rw [endEq]
  apply execute_unit_steps (states:=blockPrefix ops s)
  intro j hj
  have ctl : control ops[j]=true:=ctrl ⟨j,hj⟩
  refine ⟨.base ops[j],fetchAt im _ (i+j) _ (by omega) (addr j hj) (enc j hj),?_,(controlOK (blockPrefix ops s j) _ ctl).2⟩
  rw [succ j hj];exact (controlOK (blockPrefix ops s j) _ ctl).1
end CommitGolfCandidate.Trunc.Wire
