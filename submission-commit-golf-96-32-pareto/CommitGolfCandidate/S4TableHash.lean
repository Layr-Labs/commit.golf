import CommitGolfCandidate.S4Compression
import CommitGolfCandidate.S4Table
import CommitGolfCandidate.S4Directions
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)
def heapPointers : List Sym.Calc := [.addi .x10 .x14 0,.addi .x12 .x30 0]
def tableHashCode (cut : Bool) := (heapPointers.map Sym.Calc.instr)++callWords cut
def tableReply (o : Oracle) (s : MachineState) (site dst : Nat) (cut : Bool) :=
  callDone o.compression (Sym.evaluated heapPointers s) (site+2) 512 dst cut

theorem tableHash (o : Oracle) (s : MachineState) (site dst : Nat) (cut : Bool) (pc : s.pc=pcAt site)
    (bound : site+(2+callSteps cut)≤Code.check.count) (code : Matches .check site (tableHashCode cut))
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96) (row : s.getReg .x14=W 512)
    (out : s.getReg .x30=W dst) (db : AddrOK dst 32) :
    HashResult o s (tableReply o s site dst cut) site 512 dst cut := by
  let t:=Sym.evaluated heapPointers s
  obtain ⟨pre,regs,mem,ip⟩:=calcRegs .check s heapPointers site pc (by change site+2≤_;omega) code.left
    (by decide) rfl
  have get (r : Reg) (a : r≠.x10) (b : r≠.x12) : t.getReg r=s.getReg r:=
    outsideCalc heapPointers s t regs [.x10,.x12] rfl r (by simpa using And.intro a b)
  have ptr : t.getReg .x10=W 512:=(regs .x10).trans ((BitVec.add_zero _).trans row)
  have dest : t.getReg .x12=W dst:=(regs .x12).trans ((BitVec.add_zero _).trans out)
  have actual:=actualCall o t (site+2) 512 dst cut ip (by omega) code.right ((get _ (by decide) (by decide)).trans mode)
    ((get _ (by decide) (by decide)).trans kind) ((get _ (by decide) (by decide)).trans len) ptr dest
    ⟨by decide,by decide⟩ db
  refine ⟨(ofRuns o pre).trans actual.run,actual.pc.trans (congrArg pcAt (by omega)),
    fun r a b=>(actual.keep r).trans (get r a b),?_,?_⟩
  · exact actual.data.trans (congrArg (fun x=>trim cut (o.compression x)) (read_buffer_memory_congr t s mem 512 96))
  · intro q b away;exact (actual.outside q b away).trans (by simp only [byte,MachineState.getByte,MachineState.getMem,show t.mem=s.mem from mem])
end CommitGolfCandidate.S4.Machine
