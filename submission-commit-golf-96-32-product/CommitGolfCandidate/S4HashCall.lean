import CommitGolfCandidate.S4Kernel
import CommitGolfCandidate.S4IslandRun
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
def callWords (cut : Bool) := Instr.ECALL::(if cut then [.JAL .x0 32768] else [])
def callSteps (cut : Bool) := if cut then 2 else 1
def callDone (H : Compression) (s : MachineState) (pc src dst : Nat) (cut : Bool) :=
  let w:=H (readBuffer s src 96)
  (scratch (pc+1) cut w (Late.store s dst (trimAt (pc+1) cut w))).setPC (pcAt (pc+callSteps cut))

structure Called (o : Oracle) (s t : MachineState) (start src dst : Nat) (cut : Bool) : Prop where
  run : CheckRuns o s t (callSteps cut) 1
  pc : t.pc=pcAt (start+callSteps cut)
  keep : ∀ r,r≠.x10 → t.getReg r=s.getReg r
  data : readBuffer t dst 32=trimAt (start+1) cut (o.compression (readBuffer s src 96))
  outside : SameOutside s t dst 32

private theorem storePC (s : MachineState) (a : Nat) (d : Digest) : (Late.store s a d).pc=s.pc+4:=rfl
private theorem storeReg (s : MachineState) (a : Nat) (d : Digest) (r : Reg) : (Late.store s a d).getReg r=s.getReg r:=writeBits_register ..
attribute [local irreducible] readBuffer Late.store
theorem actualCall (o : Oracle) (s : MachineState) (n src dst : Nat) (cut : Bool) (island : cut=true → n+1∈maskPCs)
    (pc : s.pc=pcAt n) (room : n+callSteps cut≤Code.check.count) (code : Matches .check n (callWords cut))
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (width : s.getReg .x11=96)
    (a : s.getReg .x10=W src) (b : s.getReg .x12=W dst) (sa : AddrOK src 96) (da : AddrOK dst 32) :
    Called o s (callDone o.compression s n src dst cut) n src dst cut := by
  let w:=o.compression (readBuffer s src 96)
  let d:=trimAt (n+1) cut w
  let u:=Late.store s dst d
  let t:=callDone o.compression s n src dst cut
  have mem : t.mem=u.mem:=scratch_mem .. 
  refine ⟨?_,rfl,fun r nr=>MachineState.getReg_setPC.trans ((scratch_reg _ _ _ _ r nr).trans (storeReg ..)),?_,?_⟩
  · have hb : n<Code.check.count:=by cases cut <;> simp [callSteps] at room <;> omega
    have c:=call o hb pc code.head mode kind width a b sa da
    have z : (Late.store s dst w).pc=pcAt (n+1):=(storePC ..).trans ((congrArg (·+4) pc).trans (Late.pc_succ n).symm)
    cases cut with
    | false=>
      have erase (s : MachineState) : s.setPC s.pc=s:=by cases s;rfl
      change CheckRuns o s ((Late.store s dst w).setPC (pcAt (n+1))) 1 1
      rw [←z,erase];exact c
    | true=>
      have more:=ofRunsShort (k:=1) o (islandRun s (n+1) dst w (island rfl) b da z) (by decide)
      exact c.trans more
  · exact (read_buffer_memory_congr t u mem dst 32).trans (Late.store_read s dst d)
  · intro q h sep;have seen:=storeFrame s dst d (da.2.trans (by decide)) q h sep
    change byte t q=byte s q
    simp only [byte,MachineState.getByte,MachineState.getMem,mem] at *;exact seen
end CommitGolfCandidate.S4.Machine
