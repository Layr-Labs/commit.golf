import CommitGolfCandidate.LateLatch

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

structure UpdateRegs (s t : MachineState) (i : Fin 32) : Prop where
  message : t.getReg .x8 = if i.val%8=7 then s.getReg .x8 + s.getReg .x29 else s.getReg .x8
  row : t.getReg .x18 = if i.val%16=15 then s.getReg .x18+1536 else s.getReg .x18
  nodes : t.getReg .x23 = if i.val=31 then s.getReg .x23+1536 else s.getReg .x23
  count : t.getReg .x20 = if i.val=31 then s.getReg .x20-1 else s.getReg .x20
  pc : t.pc = s.pc + BitVec.ofNat 64 (4*(updates i).length)
  mem : t.mem = s.mem

set_option maxRecDepth 12000 in
theorem update_regs (s : MachineState) (i : Fin 32) : UpdateRegs s (updatesState s i) i := by
  have neg : signExtend12 4095 = -(1 : Word) := by decide
  have pos : signExtend12 1536 = (1536 : Word) := by decide
  by_cases a : i.val%8=7 <;> by_cases b : i.val%16=15 <;> by_cases c : i.val=31 <;>
    constructor <;>
    simp only [updatesState, updates, a,b,c, ↓reduceIte, List.cons_append, List.nil_append,
      List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil, execInstrBr,
      neg, pos, BitVec.sub_eq_add_neg, MachineState.getReg_setPC, MachineState.setPC, BitVec.add_assoc] <;>
    first | rfl | simp [MachineState.getReg,MachineState.setReg,BitVec.sub_eq_add_neg]

theorem update_keeps (s : MachineState) (i : Fin 32) (r : Reg)
    (r8 : Reg.x8 ≠ r) (r18 : Reg.x18 ≠ r) (r23 : Reg.x23 ≠ r) (r20 : Reg.x20 ≠ r) :
    (updatesState s i).getReg r = s.getReg r := by
  unfold updatesState updates
  split <;> split <;> split <;>
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ r8,
      MachineState.getReg_setReg_ne _ _ _ _ r18, MachineState.getReg_setReg_ne _ _ _ _ r23,
      MachineState.getReg_setReg_ne _ _ _ _ r20]

theorem exit_pc (h : Compression) (s : MachineState) (tile : Nat) (i : Fin 32)
    (pc : s.pc = pcAt (leafPC i 0)) :
    (finalLeafState h s tile i).pc = pcAt (latchStart i) := by
  have each (q : MachineState) (j : Fin 4) :
      (siteResult h tile q i j).pc = q.pc+12 := call_pc _ _ _ _ _ _
  simp only [finalLeafState, each, pc, latchStart, BitVec.add_assoc]
  change BitVec.ofNat 64 (4096 + 4 * leafPC i 0) + BitVec.ofNat 64 48 = BitVec.ofNat 64 _
  rw [←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  omega

theorem final_keeps (h : Compression) (s : MachineState) (tile : Nat) (i : Fin 32) (r : Reg)
    (r10 : Reg.x10 ≠ r) (r12 : Reg.x12 ≠ r) : (finalLeafState h s tile i).getReg r = s.getReg r := by
  have each (q : MachineState) (j : Fin 4) :
      (siteResult h tile q i j).getReg r = q.getReg r := call_register _ _ _ r _ _ _ r10 r12
  simp only [finalLeafState, each]

end CommitGolfCandidate.Late
