import CommitGolfCandidate.Stage3cCode

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Partial register values suffice for address setup. Any omitted register can
contain arbitrary input data. -/
abbrev KnownRegs := Reg → Option Word
def Agrees (q : KnownRegs) (s : MachineState) := ∀ r v, q r = some v → s.getReg r = v

def recordReg (q : KnownRegs) (dst : Reg) (v : Option Word) : KnownRegs :=
  fun r => if dst=r then v else q r

def knownStep (q : KnownRegs) : Instr → KnownRegs
  | .ADDI d r n => recordReg q d ((q r).map (· + signExtend12 n))
  | .SLLI d r n => recordReg q d ((q r).map (fun v : Word => v <<< n.toNat))
  | .ADD d a b => recordReg q d (do return (←q a)+(←q b))
  | .LUI d n => recordReg q d (some (((n.zeroExtend 32) <<< 12).signExtend 64))
  | .OR d a b => recordReg q d (do return (←q a) ||| (←q b))
  | _ => fun _ => none

def setupOp : Instr → Bool
  | .ADDI d _ _ | .SLLI d _ _ | .ADD d _ _ | .OR d _ _ | .LUI d _ => d != .x0
  | _ => false

private theorem updated_agrees (q : KnownRegs) (s : MachineState) (dst : Reg) (v : Word) (w : Option Word)
    (nz : dst ≠ .x0) (good : Agrees q s) (computed : ∀ z, w = some z → v=z) (pc : Word) :
    Agrees (recordReg q dst w) ((s.setReg dst v).setPC pc) := by
  intro r z eq
  simp only [MachineState.getReg_setPC]
  by_cases same : dst=r
  · subst r
    rw [MachineState.getReg_setReg_eq nz]
    exact computed z (by simpa [recordReg] using eq)
  · rw [MachineState.getReg_setReg_ne _ _ _ _ same]
    exact good _ _ (by simpa [recordReg,same] using eq)

private theorem known_step_sound (q : KnownRegs) (s : MachineState) (op : Instr) (ok : setupOp op)
    (good : Agrees q s) : Agrees (knownStep q op) (execInstrBr s op) := by
  cases op <;> simp only [setupOp, bne_iff_ne, Bool.false_eq_true] at ok
  case ADDI dst r n =>
    apply updated_agrees _ _ _ _ _ ok good
    intro z hz
    cases eq : q r with
    | none => simp [eq] at hz
    | some x => rw [good r x eq]; simpa only [eq,Option.map_some,Option.some.injEq] using hz
  case SLLI dst r n =>
    apply updated_agrees _ _ _ _ _ ok good
    intro z hz
    cases eq : q r with
    | none => simp [eq] at hz
    | some x => rw [good r x eq]; simpa only [eq,Option.map_some,Option.some.injEq] using hz
  case ADD dst a b =>
    apply updated_agrees _ _ _ _ _ ok good
    intro z h
    cases ea : q a <;> cases eb : q b <;> simp [ea,eb] at h
    rw [good _ _ ea,good _ _ eb]; exact h

  case OR dst a b =>
    apply updated_agrees _ _ _ _ _ ok good
    intro z h
    cases ea : q a <;> cases eb : q b <;> simp [ea,eb] at h
    rw [good _ _ ea,good _ _ eb]; exact h

  case LUI dst n =>
    apply updated_agrees _ _ _ _ _ ok good
    exact fun z h=>Option.some.inj h

theorem known_header (ops : List Instr) (q : KnownRegs) (s : MachineState)
    (sane : ∀ op ∈ ops, setupOp op) (good : Agrees q s) :
    Agrees (ops.foldl knownStep q) (ops.foldl execInstrBr s) := by
  induction ops generalizing q s with
  | nil => exact good
  | cons op ops ih =>
    exact ih _ _ (fun x hx => sane x (by simp [hx]))
      (known_step_sound q s op (sane _ (by simp)) good)

theorem header_properties (ops : List Instr) (s : MachineState) (sane : ∀ op ∈ ops, setupOp op) :
    (ops.foldl execInstrBr s).mem=s.mem ∧
    (ops.foldl execInstrBr s).pc=s.pc+BitVec.ofNat 64 (4*ops.length) := by
  induction ops generalizing s with
  | nil => simp
  | cons op ops ih =>
    have valid := sane op (by simp)
    obtain ⟨m,p⟩ := ih (execInstrBr s op) (fun x hx => sane x (by simp [hx]))
    have step : (execInstrBr s op).mem=s.mem ∧ (execInstrBr s op).pc=s.pc+4 := by
      cases op <;> simp [setupOp] at valid
      all_goals first | (rename_i dst _ _; cases dst <;> exact ⟨rfl,rfl⟩) | (rename_i dst _; cases dst <;> exact ⟨rfl,rfl⟩)
    refine ⟨m.trans step.1, ?_⟩
    rw [List.foldl_cons,p,step.2,List.length_cons]
    change s.pc + BitVec.ofNat 64 4 + _ = _
    rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4+4*ops.length=4*(ops.length+1) by omega]

theorem header_straight (op : Instr) (ok : setupOp op) : straight op := by
  cases op <;> simp only [setupOp, Bool.false_eq_true] at ok
  all_goals intro s; exact ⟨rfl,rfl,rfl⟩

end CommitGolfCandidate.Chained.BinaryMachine
