import CommitGolfCandidate.S4Model
import CommitGolfCandidate.S4BranchRun
import CommitGolfCandidate.S4MaskState
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest pc_succ)
def maskPCs : List Nat := [434, 534, 634, 734, 834, 934, 1034, 1134, 1234, 1334, 1434, 1534, 1634, 1734, 1834, 1934, 2034, 2134, 2234, 2334, 2434, 2534, 3081, 3178, 3275, 3372, 3469, 3566, 3663, 3760, 3857, 3954, 4051, 4148, 4245, 4342, 4493, 4548, 4585, 4629, 4666, 4710, 4747, 4791]
def narrowAt (n : Nat) := ([834, 934, 1034, 1134, 1234, 1334, 1434, 1534, 1634, 1734, 1834, 1934, 2034, 2134, 2234, 2334, 2434, 2534, 3469, 3566, 3663, 3760, 3857, 3954, 4051, 4148, 4245, 4342, 4493, 4548, 4585, 4629, 4666, 4710, 4747, 4791] : List Nat).contains n

def islandOp (b : Bool) : Fin 4→Instr
  | 0=>if b then .LHU .x10 .x12 28 else .SH .x12 .x0 30
  | 1=>if b then .SLLI .x10 .x10 50 else .ADDI .x10 .x10 0
  | 2=>if b then .SRLI .x10 .x10 50 else .ADDI .x10 .x10 0
  | 3=>if b then .SW .x12 .x10 28 else .ADDI .x10 .x10 0

def Island (n : Nat) := directs .check n (n+8192) ∧ directs .check (n+8196) (n+1) ∧ n+8196<Code.check.count ∧
  ∀ j : Fin 4,stands .check (n+8192+j) (islandOp (narrowAt n) j)
instance (n : Nat) : Decidable (Island n):=inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
set_option maxRecDepth 12000 in
private theorem checkedIslands : ∀ i : Fin 44,Island (maskPCs[i.val]'(i.isLt)) := by decide
theorem islandOf {n : Nat} (m : n∈maskPCs) : Island n := by
  obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem m
  exact checkedIslands ⟨i,hi⟩

def projected (height : Nat) := decide (2≤height ∧ height<24)
def maskFits (n h : Nat) := projected h=true → n∈maskPCs ∧ narrowAt n=decide (6≤h)
instance (n h : Nat) : Decidable (maskFits n h):=inferInstanceAs (Decidable (_ → _))

def trimAt (n : Nat) (cut : Bool) (v : Digest) :=
  if cut then if narrowAt n then Trunc.pad238 v else Trunc.padLow v else v
def scratch (n : Nat) (cut : Bool) (w : Digest) (s : MachineState) :=
  if cut && narrowAt n then s.setReg .x10 (Trunc.maskValue w) else s
theorem scratch_mem (n : Nat) (c : Bool) (w : Digest) (s : MachineState) : (scratch n c w s).mem=s.mem := by unfold scratch;split <;> rfl
theorem scratch_reg (n : Nat) (c : Bool) (w : Digest) (s : MachineState) (r : Reg) (nr : r≠.x10) :
    (scratch n c w s).getReg r=s.getReg r := by unfold scratch;split;exact MachineState.getReg_setReg_ne _ _ _ _ nr.symm;rfl

theorem trimIsRetained (n height : Nat) (ok : maskFits n height) (d : Digest) :
    trimAt n (projected height) d=retained .packed height d := by
  by_cases c : 2≤height ∧ height<24
  · have yes:=decide_eq_true c
    have m:=(ok yes).2
    unfold trimAt retained bits
    rw [if_neg (by omega : ¬(height<2 ∨ 24≤height)),show projected height=true from yes,m]
    by_cases narrow : 6≤height <;> simp [narrow,Trunc.pad238,Trunc.padLow,low240]
  · have wide : height<2 ∨ 24≤height:=by omega
    unfold trimAt projected retained bits;rw [if_pos wide];simp [c]
end CommitGolfCandidate.S4.Machine
