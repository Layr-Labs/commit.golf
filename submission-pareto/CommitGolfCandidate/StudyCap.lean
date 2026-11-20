import CommitGolfCandidate.StudyExecution
import CommitGolfCandidate.StudyDecode
import CommitGolfCandidate.StudyMeaning
namespace CapStudy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem
set_option maxRecDepth 8192

private theorem saved : ∀ j : Fin 9, Postorder.reg j.val ∉ ([.x20,.x21,.x25,.x26,.x27,.x23] : List Reg) := by decide

theorem pass_register (s : MachineState) (r : Reg) (keep : r ∈ ([.x20,.x21,.x25,.x26,.x27,.x23] : List Reg)) :
    (Postorder.eval s 1 8 0).getReg r = s.getReg r :=
  Postorder.eval_register _ _ _ _ _ (by intro j lo hi eq; exact saved ⟨j,by omega⟩ (eq ▸ keep))

def unrollEnter (s : MachineState) : MachineState :=
  (s.setReg .x6 (s.getReg .x26 + 2047)).setPC (Postorder.pcOf 1098)

theorem entry_run (s : MachineState) (pc : s.pc = 0x1a24) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) s coins =
      (do let r ← execute openingImage fuel (unrollEnter s) coins
          return r.charge 2 0) := by
  let mid := s.setPC (Postorder.pcOf 1097)
  have f1 := packed_fetch_raw s 649 (.JAL .x0 1792) (by decide) pc rfl
  have h1 : ordinaryStep s (.base (.JAL .x0 1792)) = some mid := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, mid, pc, Postorder.pcOf, MachineState.setReg]
  have f2 := packed_fetch_raw mid 1097 (.ADDI .x6 .x26 2047) (by decide) rfl rfl
  have h2 : ordinaryStep mid (.base (.ADDI .x6 .x26 2047)) = some (unrollEnter s) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, mid,
      unrollEnter, Postorder.pcOf, MachineState.setReg, MachineState.setPC, MachineState.getReg]
  rw [show 2+fuel = fuel+1+1 by omega, execute_ordinary_step _ _ _ _ _ _ f1 h1,
    execute_ordinary_step _ _ _ _ _ _ f2 h2]
  simp [Execution.charge, instructionCycles, Nat.add_assoc, ← Nat.add_assoc]


def cursorEntry (s : MachineState) : MachineState :=
  ((s.setReg .x6 1).setReg .x30 7).setPC 0x1a54

theorem return_run (s : MachineState) (pc : s.pc = Postorder.pcOf 1864) (fuel : Nat) (coins : Bool) :
    execute openingImage (3+fuel) s coins =
      (do let r ← execute openingImage fuel (cursorEntry s) coins
          return r.charge 3 0) := by
  let s1 := (s.setReg .x6 1).setPC (Postorder.pcOf 1865)
  let s2 := ((s.setReg .x6 1).setReg .x30 7).setPC (Postorder.pcOf 1866)
  have f1 := packed_fetch_raw s 1864 (.ADDI .x6 .x0 1) (by decide) pc rfl
  have f2 := packed_fetch_raw s1 1865 (.ADDI .x30 .x0 7) (by decide) rfl rfl
  have f3 := packed_fetch_raw s2 1866 (.JAL .x0 2092332) (by decide) rfl rfl
  have h1 : ordinaryStep s (.base (.ADDI .x6 .x0 1)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc, Postorder.pcOf,
      MachineState.setReg, MachineState.setPC, MachineState.getReg]
  have h2 : ordinaryStep s1 (.base (.ADDI .x30 .x0 7)) = some s2 := by
    rfl
  have h3 : ordinaryStep s2 (.base (.JAL .x0 2092332)) = some (cursorEntry s) := by
    have jump : Postorder.pcOf 1866 + signExtend21 2092332 = 0x1a54 := by decide
    change some (s2.setPC (Postorder.pcOf 1866 + signExtend21 2092332)) = some (cursorEntry s)
    rw [jump]
    rfl
  rw [show 3+fuel = fuel+1+1+1 by omega, execute_ordinary_step _ _ _ _ _ _ f1 h1,
      execute_ordinary_step _ _ _ _ _ _ f2 h2, execute_ordinary_step _ _ _ _ _ _ f3 h3]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

def capPreparation (s : MachineState) : MachineState :=
  cursorEntry (Postorder.eval (unrollEnter s) 1 8 0)

theorem execute_cap_preparation (s : MachineState) (pc : s.pc = 0x1a24)
    (base : s.getReg .x26 = BitVec.ofNat 64 markBase) (fuel : Nat) (coins : Bool) :
    execute openingImage (771+fuel) s coins =
      (do let r ← execute openingImage fuel (capPreparation s) coins
          return r.charge 771 0) := by
  let first := unrollEnter s
  let after := Postorder.eval first 1 8 0
  have midbase : first.getReg .x6 = 6143#64 := by
    simp [first, unrollEnter, base, markBase]
  have body := Postorder.run first 1 8 0 1098 (3+fuel) coins Postorder.code_at_root
    cap_span_root (by decide) (by decide) midbase rfl
  have returnPC : after.pc = Postorder.pcOf 1864 := Postorder.eval_pc first 1 8 0 1098 rfl
  have finalStep := return_run after returnPC fuel coins
  rw [show 771+fuel = 2 + (766+(3+fuel)) by omega, entry_run s pc _ coins]
  change (do let out ← execute openingImage (Postorder.cost 8+(3+fuel)) first coins; return out.charge 2 0) = _
  rw [body]
  simp only [bind_pure_comp, Functor.map_map]
  change (fun out => (out.charge (Postorder.cost 8) 0).charge 2 0) <$> execute openingImage (3+fuel) after coins = _
  rw [finalStep]
  simp [capPreparation, first, after, Postorder.cost, Execution.charge, ← Nat.add_assoc]

theorem cap_preparation_context (s : MachineState) (expected : Nat → Word)
    (leaves : ∀ k, 256 ≤ k → k < 512 → s.getMem (Postorder.addr k) = expected k)
    (parent : ∀ k, 0 < k → k < 256 → expected k = expected (2*k) ||| expected (2*k+1)) :
    let out := capPreparation s
    out.pc = 0x1a54 ∧ out.getReg .x6 = 1 ∧ out.getReg .x30 = 7 ∧
    (∀ r, r ∈ ([.x20,.x21,.x25,.x26,.x27,.x23] : List Reg) → out.getReg r = s.getReg r) ∧
    (∀ k, 0 < k → k < 512 → out.getMem (Postorder.addr k) = expected k) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro r keep
    have a : Reg.x30 ≠ r := by intro eq; subst r; simp at keep
    have b : Reg.x6 ≠ r := by intro eq; subst r; simp at keep
    simpa [capPreparation, cursorEntry, unrollEnter, a, b] using pass_register (unrollEnter s) r keep
  · exact Postorder.root_marks (unrollEnter s) expected leaves parent

theorem cap_preparation_frame (s : MachineState) (address : Nat)
    (above : trapdoorBase ≤ address) (fit : address < 2^64) :
    (capPreparation s).getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address) :=
  Postorder.frame (unrollEnter s) 1 8 0 address cap_span_root above fit


end CapStudy
