import CommitGolfCandidate.S4Frames
import CommitGolfCandidate.S4Catalog
import CommitGolfCandidate.S4CheckSystem
import CommitGolfCandidate.S4EdgeSites
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

private def initOps : List Sym.Calc := [.addi .x8 .x13 0,.addi .x9 .x14 0,.addi .x18 .x15 0,
  .addi .x19 .x16 0,.addi .x27 .x11 0,.addi .x5 .x0 0,.addi .x13 .x0 0,.addi .x11 .x0 96,
  .addi .x23 .x0 3,.addi .x28 .x0 7,.slli .x28 .x28 11,.addi .x28 .x28 2047,.addi .x6 .x0 128]
def entered (i : CheckInput) := Sym.evaluated initOps (initial i)

private theorem initValid : (Fragment.arithmetic initOps).valid .check 0 13 := by decide
private theorem noReads : Sym.requirements Sym.original initOps=[] := rfl
private theorem nonzero : initOps.all (fun op=>op.dst != .x0)=true:=by decide

structure Header (i : CheckInput) (s : MachineState) extends Env i s, Cursor i s 0 : Prop where
  rawCount : s.getReg .x16=W i.positions.card
  proofLen : s.getReg .x17=W i.proof.length
  batch : s.getReg .x6=128

theorem initialRegisters (i : CheckInput) (o : Oracle) :
    CheckRuns o (initial i) (entered i) 13 0 ∧ (entered i).pc=pcAt 13 ∧ Header i (entered i) ∧ (entered i).mem=(initial i).mem := by
  have h:=evalMath .check initOps 0 13 (initial i) rfl initValid
    (fun op member=>bne_iff_ne.mp (List.all_eq_true.mp nonzero op member))
    (fun _ mem=>by rw [noReads] at mem;cases mem)
  obtain ⟨run,regs,mem,pc⟩:=h
  refine ⟨ofRuns o run,pc,?_,mem⟩
  have eval (r : Reg) : (entered i).getReg r=((initOps.foldl Sym.bump Sym.original) r).eval (initial i):=regs r
  refine ⟨⟨?_,?_,?_,?_,?_,(show InputsStill i (initial i) from fun _ _ _=>rfl).regs mem⟩,⟨?_,?_,?_,?_⟩,?_,?_,?_⟩
  all_goals rw [eval]
  all_goals first | rfl | (change W i.positions.card + (0 : Word) = W i.positions.card;exact BitVec.add_zero _)

theorem checkBranch (pc : Nat) (present : pc∈checkPCs) (s : MachineState) (o : Oracle)
    (start : s.pc=pcAt pc) (ident : (checkEdge pc).pc=pc) :
    CheckRuns o s (s.setPC (pcAt ((checkEdge pc).dest s))) 1 0 :=
  ofRuns o ((checkEdge pc).run .check s (ident.symm ▸ start) (checkEdgeValid _ present))

theorem eqNatural (x y : Nat) (bx : x<2^64) (by' : y<2^64) :
    (W x==W y)=decide (x=y) := by
  by_cases same : x=y
  · subst y;simp
  · have ne : W x≠W y:=fun e=>same (wordNumber bx by' e)
    simp [same,ne]

def normalGuard (s : MachineState) :=
  Sym.evaluated [.addi .x6 .x0 824,.mul .x7 .x16 .x6] s

theorem normalSize (s : MachineState) (o : Oracle) (pc : s.pc=pcAt 15) :
    CheckRuns o s (normalGuard s) 2 0 ∧ (normalGuard s).pc=pcAt 17 ∧
    (normalGuard s).getReg .x7=s.getReg .x16*824 ∧
    (∀ r,r≠.x7 → r≠.x6 → (normalGuard s).getReg r=s.getReg r) ∧ (normalGuard s).mem=s.mem := by
  let ops : List Sym.Calc:=[.addi .x6 .x0 824,.mul .x7 .x16 .x6]
  have h:=evalMath .check ops 15 17 s pc (by decide)
    (by intro op mem;simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at mem;rcases mem with rfl|rfl <;> decide)
    (fun _ mem=>by cases mem)
  refine ⟨ofRuns o h.1,h.2.2.2,?_,?_,h.2.2.1⟩
  · exact h.2.1 .x7
  · intro r a b;change (Sym.evaluated ops s).getReg r=_;rw [h.2.1 r];cases r <;> first | rfl | contradiction

end CommitGolfCandidate.S4.Machine
