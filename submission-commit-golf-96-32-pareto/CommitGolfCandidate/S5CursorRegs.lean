import CommitGolfCandidate.S5Changes
import CommitGolfCandidate.S5LeafRun
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def updatesState (s : MachineState) (i : Fin 256) := (updates i).foldl execInstrBr s

structure UpdateRegs (s t : MachineState) (i : Fin 256) : Prop where
  message : t.getReg .x21=if i.val%16=15 then s.getReg .x21+s.getReg .x25 else s.getReg .x21
  rows : t.getReg .x22=if i.val%42=41 then s.getReg .x22+s.getReg .x26 else if i.val=255 then s.getReg .x22+s.getReg .x27 else s.getReg .x22
  nodes : t.getReg .x23=if i.val%128=127 then s.getReg .x23+s.getReg .x25 else s.getReg .x23
  count : t.getReg .x20=if i.val=255 then s.getReg .x20-1 else s.getReg .x20
  pc : t.pc=s.pc+BitVec.ofNat 64 (4*(updates i).length)
  mem : t.mem=s.mem

theorem update_regs (s : MachineState) (i : Fin 256) : UpdateRegs s (updatesState s i) i := by
  have frame:=frame_effect (changes i) s
  have len : (changes i).length=(updates i).length := by rw [←changes_correct i,List.length_map]
  rw [changes_correct,len] at frame
  constructor
  · rw [updatesState,updates_read];simp only [selected];split <;> rfl
  · rw [updatesState,updates_read];simp only [selected];split <;> first | rfl | (split <;> rfl)
  · rw [updatesState,updates_read];simp only [selected];split <;> first | rfl | (split <;> rfl)
  · rw [updatesState,updates_read];simp only [selected];split <;> simp [applyDeltas,Move.delta,BitVec.sub_eq_add_neg]
  · exact frame.1
  · exact frame.2

theorem update_keeps (s : MachineState) (i : Fin 256) (r : Reg)
    (r21 : Reg.x21≠r) (r22 : Reg.x22≠r) (r23 : Reg.x23≠r) (r20 : Reg.x20≠r) :
    (updatesState s i).getReg r=s.getReg r := by
  rw [updatesState,updates_read]
  cases r <;> first | rfl | contradiction

theorem exit_pc (h : Compression) (s : MachineState) (tile : Nat) (i : Fin 256)
    (pc : s.pc = pcAt (leafPC i 0)) :
    (finalLeafState h s tile i).pc = pcAt (updateStart i) := by
  have each (q : MachineState) (j : Fin 4) :
      (siteResult h tile q i j).pc = q.pc+12 := call_pc _ _ _ _ _ _
  simp only [finalLeafState, each, pc, updateStart, BitVec.add_assoc]
  change BitVec.ofNat 64 (4096 + 4 * leafPC i 0) + BitVec.ofNat 64 48 = BitVec.ofNat 64 _
  rw [←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  change 4096+4*(tileSite i 0)+48=4096+4*(tileSite i 0+12)
  omega

theorem final_keeps (h : Compression) (s : MachineState) (tile : Nat) (i : Fin 256) (r : Reg)
    (r10 : Reg.x10 ≠ r) (r12 : Reg.x12 ≠ r) : (finalLeafState h s tile i).getReg r = s.getReg r := by
  have each (q : MachineState) (j : Fin 4) :
      (siteResult h tile q i j).getReg r = q.getReg r := call_register _ _ _ r _ _ _ r10 r12
  simp only [finalLeafState, each]

end CommitGolfCandidate.S5Machine
