import CommitGolfCandidate.S4Header
import CommitGolfCandidate.S4OpenInput
import CommitGolfCandidate.S4BranchRun
import CommitGolfCandidate.S4Pieces
import CommitGolfCandidate.S4Address
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Runs proofBase indexBase)
open Late (Trapdoor pcAt)
def modePC (k : Nat) := if k=128 then 3 else 5275
def modeSteps (k : Nat) := if k=128 then 2 else 3
def modeStart (s : MachineState) (k : Nat) := (execInstrBr s (.ADDI .x6 .x0 128)).setPC (pcAt (modePC k))
theorem mode (td : Trapdoor) (ps : Positions) :
    let s:=initial td ps
    let t:=modeStart s ps.card
    Runs .opening s t (modeSteps ps.card) (modeSteps ps.card) ∧ t.pc=pcAt (modePC ps.card) ∧
    t.mem=s.mem ∧ ∀ r,r≠.x6 → t.getReg r=s.getReg r := by
  let s:=initial td ps;let u:=execInstrBr s (.ADDI .x6 .x0 128)
  have a : Runs .opening s u 1 1:=Machine.stepAdd _ s 0 _ _ _ (by decide) rfl (by rfl)
  have test:=Machine.alternate .opening 1 3 5275 .x16 .x6 true (by decide) (by decide) rfl u rfl
  have count : u.getReg .x16=W ps.card:=rfl
  have size : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
  change ps.card≤16777216 at size
  have check : ((u.getReg .x16==u.getReg .x6)==true)=decide (ps.card=128):=by
    change ((W ps.card==W 128)==true)=_;rw [Machine.eqNatural _ _ (by omega) (by decide)];simp
  rw [check] at test
  refine ⟨?_,rfl,rfl,fun r ne=>MachineState.getReg_setPC.trans (Machine.keepAdd s .x6 .x0 r 128 (Ne.symm ne))⟩
  by_cases b : ps.card=128
  · rw [decide_eq_true b] at test;simp only [modePC,modeSteps,modeStart,if_pos b];exact a.trans test
  · rw [decide_eq_false b] at test;simp only [modePC,modeSteps,modeStart,if_neg b];exact a.trans test

def setupOps (b : Bool) : List Machine.Sym.Calc :=
  if b then [.addi .x19 .x15 0,.addi .x24 .x0 512,.addi .x25 .x0 1,.addi .x27 .x0 3,.addi .x9 .x0 16]
  else [.addi .x19 .x15 0,.addi .x27 .x0 3,.addi .x20 .x16 0,.addi .x21 .x13 0]
def entrySite (b : Bool) := if b then 16359 else 5275
def entryEnd (b : Bool) := if b then 16364 else 5279
def setup (b : Bool) (s : MachineState) := Machine.Sym.evaluated (setupOps b) s
private theorem sites (b : Bool) : (Machine.Fragment.arithmetic (setupOps b)).valid .opening (entrySite b) (entryEnd b) ∧
    (setupOps b).all (fun c=>c.dst != .x0) ∧ Machine.Sym.requirements Machine.Sym.original (setupOps b)=[] := by cases b <;> decide

theorem entrySetup (b : Bool) (s : MachineState) (pc : s.pc=pcAt (entrySite b)) :
    let t:=setup b s
    Runs .opening s t (if b then 5 else 4) (if b then 5 else 4) ∧ t.pc=pcAt (entryEnd b) ∧ t.mem=s.mem ∧
    t.getReg .x19=s.getReg .x15 ∧ t.getReg .x27=3 ∧ t.getReg .x13=s.getReg .x13 ∧ t.getReg .x15=s.getReg .x15 ∧
    (b=true → t.getReg .x24=512 ∧ t.getReg .x25=1 ∧ t.getReg .x9=16) ∧
    (b=false → t.getReg .x20=s.getReg .x16 ∧ t.getReg .x21=s.getReg .x13) := by
  obtain ⟨good,nz,reads⟩:=sites b
  obtain ⟨run,regs,mem,atEnd⟩:=Machine.evalMath .opening _ _ _ s pc good
    (fun c member=>bne_iff_ne.mp (List.all_eq_true.mp nz c member)) (fun _ m=>by rw [reads] at m;cases m)
  have cost : Machine.Sym.price (setupOps b)=(if b then 5 else 4) ∧ (setupOps b).length=(if b then 5 else 4):=by cases b <;> decide
  rw [cost.1,cost.2] at run
  refine ⟨run,atEnd,mem,?_,?_,?_,?_,?_,?_⟩
  · exact (regs _).trans (by cases b <;> exact BitVec.add_zero _)
  · exact (regs _).trans (by cases b <;> rfl)
  · exact (regs _).trans (by cases b <;> rfl)
  · exact (regs _).trans (by cases b <;> rfl)
  · rintro rfl;exact ⟨(regs _).trans rfl,(regs _).trans rfl,(regs _).trans rfl⟩
  · rintro rfl;exact ⟨(regs _).trans (BitVec.add_zero _),(regs _).trans (BitVec.add_zero _)⟩
end CommitGolfCandidate.S4.Open
