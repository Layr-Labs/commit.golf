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
/-- Control flow from the restored register file, at the displaced instruction's successor. -/
def resumeState (s : MachineState) (k : Nat) := s.setPC (pcAt (modePC k))
def resumeSteps (k : Nat) := if k=128 then 1 else 2

theorem resumeMode (ps : Positions) (s : MachineState) (pc : s.pc=pcAt 1)
    (count : s.getReg .x16=W ps.card) (sentinel : s.getReg .x6=128) :
    Runs .opening s (resumeState s ps.card) (resumeSteps ps.card) (resumeSteps ps.card) := by
  have test:=Machine.alternate .opening 1 3 5275 .x16 .x6 true (by decide) (by decide) rfl s pc
  rw [count,sentinel] at test
  have size : ps.card≤LENGTH:=by simpa using Finset.card_le_univ ps
  change ps.card≤16777216 at size
  have check : ((W ps.card==W 128)==true)=decide (ps.card=128):=by
    rw [Machine.eqNatural _ _ (by omega) (by decide)];simp
  change Runs .opening s (s.setPC (pcAt (if (W ps.card==W 128)==true then 3 else 5275))) (if (W ps.card==W 128)==true then 1 else 2) (if (W ps.card==W 128)==true then 1 else 2) at test
  rw [check] at test
  by_cases b : ps.card=128
  · simpa only [resumeState,modePC,resumeSteps,if_pos b,decide_eq_true b,ite_true] using test
  · simpa only [resumeState,modePC,resumeSteps,if_neg b,decide_eq_false b,Bool.false_eq_true,ite_false] using test

structure ReadyAtOne (td : Trapdoor) (ps : Positions) (s : MachineState) : Prop where
  pc : s.pc=pcAt 1
  regs : ∀ r,s.getReg r=((initial td ps).setReg .x6 128).getReg r
  bytes : ∀ q,q<2^36 → Machine.byte s q=Machine.byte (initial td ps) q
theorem ReadyAtOne.sources {td ps s} (r : ReadyAtOne td ps s) : Sources td ps s :=
  fun q _ hi=>r.bytes q (by unfold Machine.valueBase at hi;omega)

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
