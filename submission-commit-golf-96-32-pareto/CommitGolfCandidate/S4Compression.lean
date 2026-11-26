import CommitGolfCandidate.S4HashCall
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
def prepareCall (base : Reg) (off dst : Nat) : List Sym.Calc :=
  [.addi .x10 base (BitVec.ofNat 12 off),.addi .x12 .x0 (BitVec.ofNat 12 dst)]
def compressCode (base : Reg) (off dst : Nat) (cut : Bool) := calcCodePrefix++callWords cut
  where calcCodePrefix:=(prepareCall base off dst).map Sym.Calc.instr
def compressed (H : Compression) (s : MachineState) (site : Nat) (base : Reg) (off src dst : Nat) (cut : Bool) :=
  callDone H (Sym.evaluated (prepareCall base off dst) s) (site+2) src dst cut

structure HashResult (o : Oracle) (s t : MachineState) (site src dst : Nat) (cut : Bool) : Prop where
  run : CheckRuns o s t (2+callSteps cut) 1
  pc : t.pc=pcAt (site+(2+callSteps cut))
  keep : ∀ r,r≠.x10 → r≠.x12 → t.getReg r=s.getReg r
  value : readBuffer t dst 32=trimAt (site+3) cut (o.compression (readBuffer s src 96))
  outside : SameOutside s t dst 32

theorem compressRun (o : Oracle) (s : MachineState) (site : Nat) (base : Reg) (off src dst : Nat) (cut : Bool) (island : cut=true → site+3∈maskPCs)
    (room : site+(2+callSteps cut)≤Code.check.count) (pc : s.pc=pcAt site)
    (code : Matches .check site (compressCode base off dst cut))
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96)
    (addr : s.getReg base+signExtend12 (BitVec.ofNat 12 off)=W src) (imm : signExtend12 (BitVec.ofNat 12 dst)=W dst)
    (sr : AddrOK src 96) (dr : AddrOK dst 32) :
    HashResult o s (compressed o.compression s site base off src dst cut) site src dst cut  := by
  let ops:=prepareCall base off dst;let u:=Sym.evaluated ops s
  obtain ⟨run,regs,mem,endPC⟩:=calcGiven site .check ops s pc (by change site+2≤_;omega) code.left
    (fun c h=>by simp only [ops,prepareCall,List.mem_cons,List.not_mem_nil,or_false] at h;rcases h with rfl|rfl <;> simp only [Sym.Calc.dst] <;> decide)
    (fun _ h=>by cases h)
  have ptr : u.getReg .x10=W src:=by
    apply (regs .x10).trans
    change (Sym.mkOp .add (Sym.original base) (.lit _)).eval s=_
    simp only [Sym.eval_mkOp,Sym.Bin.apply,Sym.Expr.eval,liveOriginal,addr]
  have toPtr : u.getReg .x12=W dst:=by apply (regs .x12).trans;change (0 : Word)+signExtend12 _=_;rw [imm];exact BitVec.zero_add _
  have keep (r : Reg) (l : r≠.x10) (v : r≠.x12) : u.getReg r=s.getReg r:=
    outsideCalc ops s u regs [.x10,.x12] rfl r (by simpa using And.intro l v)
  have sub : Matches .check (site+2) (callWords cut):=code.right
  have h:=actualCall o u (site+2) src dst cut island endPC (by omega) sub ((keep _ (by decide) (by decide)).trans mode)
    ((keep _ (by decide) (by decide)).trans kind) ((keep _ (by decide) (by decide)).trans len) ptr toPtr sr dr
  refine ⟨(ofRuns o run).trans h.run,h.pc.trans (congrArg pcAt (by omega)),fun r a b=>(h.keep r a).trans (keep r a b),?_,?_⟩
  · exact h.data.trans (congrArg (fun v=>trimAt (site+3) cut (o.compression v)) (read_buffer_memory_congr u s mem src 96))
  · intro q b outside
    exact (h.outside q b outside).trans (by simp only [byte,MachineState.getByte,MachineState.getMem,show u.mem=s.mem from mem])
end CommitGolfCandidate.S4.Machine
