import CommitGolfCandidate.S4Kernel
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
def callWords (cut : Bool) := Instr.ECALL::(if cut then [.SH .x12 .x0 30] else [])
def callSteps (cut : Bool) := if cut then 2 else 1
def trim (cut : Bool) (d : Digest) := if cut then Trunc.padLow d else d
def callDone (H : Compression) (s : MachineState) (pc src dst : Nat) (cut : Bool) :=
  (Late.store s dst (trim cut (H (readBuffer s src 96)))).setPC (pcAt (pc+callSteps cut))

structure Called (o : Oracle) (s t : MachineState) (start src dst : Nat) (cut : Bool) : Prop where
  run : CheckRuns o s t (callSteps cut) 1
  pc : t.pc=pcAt (start+callSteps cut)
  keep : ∀ r,t.getReg r=s.getReg r
  data : readBuffer t dst 32=trim cut (o.compression (readBuffer s src 96))
  outside : SameOutside s t dst 32

private theorem changesPC (s : MachineState) (a : Nat) (d : Digest) : (Late.store s a d).pc=s.pc+4:=rfl
private theorem savesRegs (s : MachineState) (a : Nat) (d : Digest) (r : Reg) : (Late.store s a d).getReg r=s.getReg r:=writeBits_register .. 
attribute [local irreducible] readBuffer Late.store trim
theorem actualCall (o : Oracle) (s : MachineState) (n src dst : Nat) (cut : Bool)
    (pc : s.pc=pcAt n) (room : n+callSteps cut≤Code.check.count) (code : Matches .check n (callWords cut))
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (width : s.getReg .x11=96)
    (a : s.getReg .x10=W src) (b : s.getReg .x12=W dst) (sa : AddrOK src 96) (da : AddrOK dst 32) :
    Called o s (callDone o.compression s n src dst cut) n src dst cut := by
  let d:=trim cut (o.compression (readBuffer s src 96))
  let u:=Late.store s dst d
  let t:=callDone o.compression s n src dst cut
  have mem : t.mem=u.mem:=by simp only [t,u,d,callDone,MachineState.setPC]
  refine ⟨?_,rfl,fun r=>MachineState.getReg_setPC.trans (savesRegs ..),?_,?_⟩
  · cases cut with
    | false=>
      have c:=call o (by change n+1≤_ at room;omega) pc code.head mode kind width a b sa da
      have z : (Late.store s dst (o.compression (readBuffer s src 96))).pc=pcAt (n+1):=(changesPC ..).trans ((congrArg (·+4) pc).trans (Late.pc_succ n).symm)
      have erase (s : MachineState) : s.setPC s.pc=s:=by cases s;rfl
      unfold callDone trim;change CheckRuns o s ((Late.store s dst (o.compression (readBuffer s src 96))).setPC (pcAt (n+1))) 1 1
      rw [←z,erase];exact c
    | true=>unfold callDone trim;exact maskedCall o room pc code.head code.tail.head mode kind width a b sa da
  · exact (read_buffer_memory_congr t u mem dst 32).trans (Late.store_read s dst d)
  · intro q h sep;have seen:=storeFrame s dst d (da.2.trans (by decide)) q h sep
    change byte t q=byte s q
    simp only [byte,MachineState.getByte,MachineState.getMem,mem] at *;exact seen

def projected (height : Nat) := decide (2≤height ∧ height<24)
theorem trimIsRetained (height : Nat) (d : Digest) : trim (projected height) d=retained .byte height d := by
  have no : ¬(Profile.byte=Profile.packed ∧ 6≤height):=fun z=>by cases z.1
  by_cases cut : 2≤height ∧ height<24
  · have b : bits .byte height=240:=by unfold bits;rw [if_neg (by omega),if_neg no]
    simp only [trim,projected,decide_eq_true cut,ite_true,retained,b,show ¬(240 : Nat)=238 by decide,ite_false];rfl
  · have b : bits .byte height=256:=by unfold bits;rw [if_pos (by omega)]
    simp only [trim,projected,decide_eq_false cut,Bool.false_eq_true,ite_false,retained,b,
      show ¬(256 : Nat)=238 by decide,show ¬(256 : Nat)=240 by decide]
end CommitGolfCandidate.S4.Machine
