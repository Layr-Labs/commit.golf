import CommitGolfCandidate.R4CommitBase
import CommitGolfCandidate.S4MaskState
import CommitGolfCandidate.LateCalls
import CommitGolfCandidate.LateTreeMemory

namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ)
abbrev Z (n : Nat) := BitVec.ofNat 64 n
abbrev MRun (o : Oracle) := DetRun o (submission.image .commit)
def Site (n : Nat) (op : Instr) := ∀ s : MachineState,s.pc=pcAt n → fetch (submission.image .commit) s=some (.base op)

structure Masked (o : Oracle) (s t : MachineState) (a site e : Nat) (w target : Digest) : Prop where
  run : MRun o (writeBits s (Z a) w) e t e 0
  mem : t.mem=(writeBits s (Z a) target).mem
  pc : t.pc=pcAt (site+e)
  keep : ∀ r : Reg,r≠.x6 → t.getReg r=s.getReg r

attribute [local irreducible] writeBits
set_option maxHeartbeats 1200000
theorem maskNarrow (o : Oracle) (s : MachineState) (n a : Nat) (w : Digest)
    (pc : (writeBits s (Z a) w).pc=pcAt n) (ptr : s.getReg .x12=Z a)
    (mask : s.getReg .x28=16383) (al : a%8=0) (bound : a+32≤MEMORY_BYTES)
    (load : Site n (.LHU .x6 .x12 28)) (cut : Site (n+1) (.AND .x6 .x6 .x28))
    (store : Site (n+2) (.SW .x12 .x6 28)) :
    ∃ t, Masked o s t a n 3 w (Trunc.pad238 w) := by
  let raw:=writeBits s (Z a) w
  let u:=execInstrBr raw (.LHU .x6 .x12 28)
  let v:=execInstrBr u (.AND .x6 .x6 .x28)
  let t:=execInstrBr v (.SW .x12 .x6 28)
  have rptr : raw.getReg .x12=Z a:=(writeBits_register ..).trans ptr
  have rmask : raw.getReg .x28=16383:=(writeBits_register ..).trans mask
  have pa : raw.getReg .x12+signExtend12 28=Z (a+28):=by rw [rptr];exact (BitVec.ofNat_add ..).symm
  have vptr : v.getReg .x12=raw.getReg .x12:=rfl
  have fits : a+32≤2^64:=bound.trans (by decide)
  have acc (k : Nat) (hk : k=2 ∨ k=4) : accessValid (Z (a+28)) k=true:=by
    rcases hk with rfl|rfl <;> simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show a+28<2^64 by omega)] <;> simp [show a+28+2≤MEMORY_BYTES by omega,show a+28+4≤MEMORY_BYTES by omega,show (a+28)%2=0 by omega,show (a+28)%4=0 by omega]
  have lrun : MRun o raw 1 u 1 0:=by
    have safe : memoryArgumentsValid raw (.LHU .x6 .x12 28)=true:=by change accessValid _ 2=true;rw [pa,acc _ (Or.inl rfl)]
    exact DetRun.step1 (load _ pc) (by simp only [ordinaryStep,safe,ite_true];rfl)
  have pc1 : u.pc=pcAt (n+1):=(congrArg (·+4) pc).trans (pc_succ n).symm
  have pc2 : v.pc=pcAt (n+2):=(congrArg (·+4) pc1).trans (pc_succ _).symm
  have crun : MRun o u 1 v 1 0:=DetRun.step1 (cut _ pc1) rfl
  have srun : MRun o v 1 t 1 0:=by
    have safe : memoryArgumentsValid v (.SW .x12 .x6 28)=true:=by change accessValid _ 4=true;rw [vptr,pa,acc _ (Or.inr rfl)]
    exact DetRun.step1 (store _ pc2) (by simp only [ordinaryStep,safe,ite_true];rfl)
  have value : v.getReg .x6=Trunc.maskValue w:=by
    change (raw.getHalfword (raw.getReg .x12+signExtend12 28)).zeroExtend 64 &&& raw.getReg .x28=_
    rw [pa,show raw.getHalfword (Z (a+28))=_ from Trunc.loaded238 s a w al fits,rmask];rfl
  refine ⟨t,⟨(lrun.trans crun).trans srun,?_,(congrArg (·+4) pc2).trans (pc_succ _).symm,?_⟩⟩
  · change (v.setWord32 (v.getReg .x12+signExtend12 28) ((v.getReg .x6).truncate 32)).mem=_
    rw [vptr,pa,value]
    have reduced:=congrArg MachineState.mem (Trunc.cleared238 s a w al fits)
    exact reduced
  · intro r hr
    have sreg : t.getReg r=v.getReg r:=MachineState.getReg_setPC.trans (getReg_setMem ..)
    have vreg : v.getReg r=u.getReg r:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ hr.symm)
    have ureg : u.getReg r=raw.getReg r:=MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ hr.symm)
    exact sreg.trans (vreg.trans (ureg.trans (writeBits_register ..)))

theorem maskWide (o : Oracle) (s : MachineState) (n a : Nat) (w : Digest)
    (pc : (writeBits s (Z a) w).pc=pcAt n) (ptr : s.getReg .x12=Z a)
    (al : a%8=0) (bound : a+32≤MEMORY_BYTES) (store : Site n (.SH .x12 .x0 30)) :
    ∃ t, Masked o s t a n 1 w (Trunc.padLow w) := by
  let raw:=writeBits s (Z a) w
  let t:=execInstrBr raw (.SH .x12 .x0 30)
  have rptr : raw.getReg .x12=Z a:=(writeBits_register ..).trans ptr
  have pa : raw.getReg .x12+signExtend12 30=Z (a+30):=by rw [rptr];exact (BitVec.ofNat_add ..).symm
  have fits : a+32≤2^64:=bound.trans (by decide)
  have safe : memoryArgumentsValid raw (.SH .x12 .x0 30)=true:=by
    change accessValid _ 2=true
    rw [pa];exact c_accessValid_ofNat _ _ (by omega) (by omega)
  refine ⟨t,⟨DetRun.step1 (store raw pc) (ordinaryStep_SH raw .x12 .x0 30 safe),?_,(congrArg (·+4) pc).trans (pc_succ _).symm,?_⟩⟩
  · change (raw.setHalfword (raw.getReg .x12+signExtend12 30) 0).mem=_
    rw [pa];exact congrArg MachineState.mem (Trunc.clearedReply s a w al fits)
  · intro r hr
    exact (reg_exec_SH raw _ _ _ r).trans (writeBits_register ..)
end CommitGolfCandidate.R4
