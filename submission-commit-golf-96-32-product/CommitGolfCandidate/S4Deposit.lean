import CommitGolfCandidate.S4Kernel
import CommitGolfCandidate.S4Address
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
def depositOps (src : Nat) : List Sym.Calc :=
  [.slli .x15 .x1 5,.addi .x15 .x15 512,.addi .x14 .x0 (BitVec.ofNat 12 src)]
def depositCode (src : Nat) := (depositOps src).map Sym.Calc.instr++checkedCopies 4
def deposit (s : MachineState) (src : Nat) := transferN (Sym.evaluated (depositOps src) s) 4
abbrev digestRegister (src : Nat) := src=256 ∨ src=352 ∨ src=384
theorem depositLength (src : Nat) : (depositCode src).length=11:=rfl

structure Deposited (s t : MachineState) (pc src lane : Nat) : Prop where
  run : Runs .check s t 11 11
  next : t.pc=pcAt (pc+11)
  keep : ∀ r,r≠.x6 → r≠.x14 → r≠.x15 → t.getReg r=s.getReg r
  moved : Moved s t src (512+32*lane) 32

theorem depositRun (s : MachineState) (site src lane : Nat) (which : digestRegister src) (small : lane<3)
    (pc : s.pc=pcAt site) (room : site+11≤Code.check.count) (code : Matches .check site (depositCode src))
    (digit : s.getReg .x1=W lane) : Deposited s (deposit s src) site src lane := by
  let ops:=depositOps src;let t:=Sym.evaluated ops s
  obtain ⟨first,regs,mem,next⟩:=calcGiven site .check ops s pc (by change site+3≤_;omega) code.left
    (fun c h=>by simp only [ops,depositOps,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl|rfl <;> simp only [Sym.Calc.dst] <;> decide)
    (fun _ h=>by cases h)
  have imm : signExtend12 (BitVec.ofNat 12 src)=W src:=by rcases which with rfl|rfl|rfl <;> decide
  have srcPtr : t.getReg .x14=W src:=(regs .x14).trans (by change 0+signExtend12 _=_;rw [imm];exact BitVec.zero_add _)
  have dstPtr : t.getReg .x15=W (512+32*lane):=by
    apply (regs .x15).trans
    change (s.getReg .x1 <<< 5)+W 512=_
    rw [digit,shifted]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))
  have second:=copyN t (site+3) src (512+32*lane) 4 next (by omega) code.right srcPtr dstPtr
    (by rcases which with rfl|rfl|rfl <;> decide) (by omega) (by decide)
    (by unfold MEMORY_BYTES;omega) (by unfold MEMORY_BYTES;omega) (Or.inl (by omega))
  refine ⟨first.trans second.run,second.endPC.trans (congrArg pcAt (by omega)),?_,second.bytes.congr mem.symm rfl⟩
  intro r a b c
  apply (second.regs r (Ne.symm a)).trans
  exact outsideCalc ops s t regs [.x14,.x15] (by rfl) r
    (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or];exact ⟨b,c⟩)
end CommitGolfCandidate.S4.Machine
