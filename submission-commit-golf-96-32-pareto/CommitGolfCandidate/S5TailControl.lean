import CommitGolfCandidate.S5Tiles
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000

def tailOps (odd : Bool) : List Instr :=
  [.ADDI .x21 .x21 96,.ADDI .x22 .x22 32,.BEQ .x7 .x0 8]++
    (if odd then [.ADDI .x22 .x22 32] else [])++[.XORI .x7 .x7 1,.ADDI .x20 .x20 4095]
def tailCtrlPC (d : Height) :=tailPC d+laneWords d
def tailOff (odd : Bool) (n : Nat) := n+(if odd=false ∧ 3≤n then 1 else 0)
def prefixState (s : MachineState) (ops : List Instr) (n : Nat) := (ops.take n).foldl execInstrBr s
theorem prefix_next (s : MachineState) (ops : List Instr) (n : Nat) (lt : n<ops.length) :
    prefixState s ops (n+1)=execInstrBr (prefixState s ops n) ops[n] := by
  unfold prefixState;rw [List.take_succ_eq_append_getElem lt,List.foldl_append];rfl

private theorem offset_pc (s : MachineState) (odd : Bool) (n : Nat) (within : n≤(tailOps odd).length)
    (flag : s.getReg .x7=(if odd then 1 else 0)) :
    (prefixState s (tailOps odd) n).pc=s.pc+BitVec.ofNat 64 (4*tailOff odd n) := by
  have x : s.regs .x7=(if odd then 1 else 0) := flag
  cases odd <;> simp [tailOps] at within <;> interval_cases n <;>
    simp [prefixState,tailOps,tailOff,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,x,
      signExtend13,BitVec.add_assoc] <;> rfl

private theorem tail_table_ctrl : ∀ d : Height,¬chained d → d.val<23 →
    tailCtrlPC d+6=gatePos false (passEnd d) ∧ tailCtrlPC d+6<18492 ∧
    ∀ odd : Bool,∀ j : Fin (tailOps odd).length,
    decoded (tailCtrlPC d+tailOff odd j.val)=some (.base ((tailOps odd).get j)) := by decide +kernel

def tailUpdated (s : MachineState) (odd : Bool) := (tailOps odd).foldl execInstrBr s

theorem controller_run (o : Oracle) (d : Height) (simple : ¬chained d) (inner : d.val<23)
    (s : MachineState) (odd : Bool) (flag : s.getReg .x7=(if odd then 1 else 0)) (atSite : s.pc=pcAt (tailCtrlPC d)) :
    Runs .commit true o s (tailUpdated s odd) (tailOps odd).length (tailOps odd).length 0 := by
  obtain ⟨end_,small,fetches⟩:=tail_table_ctrl d simple inner
  apply runs_pure;intro fuel
  have run:=execute_unit_steps (image .commit) (tailOps odd).length fuel (prefixState s (tailOps odd)) true (by
    intro i hi
    let op:=(tailOps odd)[i]
    have off : tailOff odd i≤6 := by cases odd <;> simp [tailOps] at hi <;> unfold tailOff <;> split_ifs <;> omega
    have code:=decoded_site (by omega : tailCtrlPC d+tailOff odd i<18492) (fetches odd ⟨i,hi⟩)
    refine ⟨.base op,code _ ?_,?_,?_⟩
    · rw [offset_pc s odd i hi.le flag,atSite,pcAt,pcAt,←BitVec.ofNat_add];congr 1 <;> omega
    · rw [prefix_next _ _ _ hi]
      cases odd <;> simp [tailOps] at hi <;> interval_cases i <;> rfl
    · cases odd <;> simp [tailOps] at hi <;> interval_cases i <;> rfl)
  rw [Nat.add_comm] at run
  simpa only [prefixState,List.take_length,List.take_zero,List.foldl_nil,tailUpdated] using run

theorem controller_pc (s : MachineState) (d : Height) (simple : ¬chained d) (inner : d.val<23)
    (odd : Bool) (flag : s.getReg .x7=(if odd then 1 else 0)) (pc : s.pc=pcAt (tailCtrlPC d)) :
    (tailUpdated s odd).pc=pcAt (gatePos false (passEnd d)) := by
  have p:=offset_pc s odd (tailOps odd).length le_rfl flag
  simp only [prefixState,List.take_length] at p
  rw [show tailOff odd (tailOps odd).length=6 by cases odd <;> rfl,pc,←(tail_table_ctrl d simple inner).1] at *
  change ((tailOps odd).foldl execInstrBr s).pc=_
  rw [p,pcAt,pcAt,←BitVec.ofNat_add];congr 1 <;> omega
end CommitGolfCandidate.S5Machine
