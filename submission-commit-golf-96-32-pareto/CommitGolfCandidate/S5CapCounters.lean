import CommitGolfCandidate.S5CapUpperMemory
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def countedState (s : MachineState) (p next : Nat) := (s.setReg .x23 (W (p+1))).setPC (pcAt next)
theorem counted (o : Oracle) (s : MachineState) (pc target p cap : Nat) (limitReg : Reg) (notCounter : limitReg≠.x23)
    (ip : s.pc=pcAt pc) (ctr : s.getReg .x23=W p) (bound : s.getReg limitReg=W cap) (hp : p<cap) (sm : cap<2^64)
    (incCode : matchesWord .check (pc,.ADDI .x23 .x23 1)) (brCode : BranchSite (pc+1) target .lt .x23 limitReg) :
    Flow o s (countedState s p (if p+1<cap then target else pc+2)) 2 0 := by
  let u:=countedState s p (pc+1)
  have inc:=imm_step o s pc .x23 .x23 1 (W (p+1)) ip (known incCode) ((congrArg (·+signExtend12 1) ctr).trans (BitVec.ofNat_add p 1).symm)
  have val : u.getReg limitReg=W cap:=MachineState.getReg_setPC.trans ((MachineState.getReg_setReg_ne _ _ _ _ notCounter.symm).trans bound)
  have flag : Rel.lt.test (u.getReg .x23) (u.getReg limitReg)=decide (p+1<cap):=by
    change BitVec.ult (W (p+1)) (u.getReg limitReg)=_;rw [val];simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt sm,Nat.mod_eq_of_lt (by omega : p+1<2^64)]
  have back:=branch o u (pc+1) target .lt .x23 limitReg brCode rfl _ flag
  rw [show (if decide (p+1<cap) then target else pc+1+1)=(if p+1<cap then target else pc+2) by simp] at back
  exact inc.trans back

def pairPC (p : Nat):=if p<171 then 825 else 909
structure PairState (H : Compression) (x : CheckInput) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc=pcAt (pairPC p)
  ctr : s.getReg .x23=W p
  bound : s.getReg .x14=W 171
  env : CapEnv x s
  entries : Evidence H x 0 s
  cache : Cache s (progress H x 0 p)

end CommitGolfCandidate.S5Machine.Check
