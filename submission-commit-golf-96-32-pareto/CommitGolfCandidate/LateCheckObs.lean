import CommitGolfCandidate.LateCheckMicro
import CommitGolfCandidate.LateLeafWrites
import CommitGolfCandidate.LateOpenPathModel

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late.Open (W)

def obs (o : Oracle) (n : Nat) (s : MachineState) : Exit × Nat :=
  let e:=checkEvaluation o (execute checkerImage n s false)
  (e.1.exit,e.2)

def Runs (o : Oracle) (s t : MachineState) (steps q : Nat) : Prop :=
  ∀ fuel, obs o (steps+fuel) s=((obs o fuel t).1,q+(obs o fuel t).2)

def Finishes (o : Oracle) (s : MachineState) (steps q : Nat) (ex : Exit) : Prop :=
  ∀ fuel, obs o (steps+fuel) s=(ex,q)

theorem Runs.trans {o : Oracle} {s t u : MachineState} {a b c d : Nat} (h : Runs o s t a c) (p : Runs o t u b d) :
    Runs o s u (a+b) (c+d) := by intro fuel;rw [Nat.add_assoc,h,p];simp [Nat.add_assoc]

theorem Runs.finish {o : Oracle} {s t : MachineState} {a b c d : Nat} {e : Exit}
    (h : Runs o s t a c) (p : Finishes o t b d e) : Finishes o s (a+b) (c+d) e := by
  intro fuel;rw [Nat.add_assoc,h,p]

theorem deterministic {s t : MachineState} {n c : Nat} (o : Oracle) (pureRun : Micro.Runs s t n c) :
    Runs o s t n 0 := by
  intro fuel
  have run:=pureRun fuel
  change execute (submission.image .check) _ _ _ = (do let r ← execute (submission.image .check) _ _ _;pure _) at run
  rw [checker_image_eq] at run
  simp only [obs,Nat.add_comm n fuel,run,bind_pure_comp,check_evaluation_map,Nat.zero_add]
  rfl

theorem rawBlock {s t : MachineState} {n c : Nat} (o : Oracle)
    (h : ∀ fuel, execute checkerImage (n+fuel) s false=
      (do let r ← execute checkerImage fuel t false;pure (r.charge c 0))) : Runs o s t n 0 := by
  intro fuel;simp only [obs,h,bind_pure_comp,check_evaluation_map,Nat.zero_add];rfl

theorem compBlock {s : MachineState} {op : OracleComp World MachineState} {n c q : Nat} (o : Oracle)
    (step : ∀ fuel, execute checkerImage (n+fuel) s false=
      (do let t ← op;let r ← execute checkerImage fuel t false;pure (r.charge c q))) :
    Runs o s (checkEvaluation o op).1 n (checkEvaluation o op).2 := by
  intro fuel;simp only [obs,step,check_evaluation_bind,bind_pure_comp,check_evaluation_map];rfl

def afterCall (o : Oracle) (s : MachineState) (src dst : Nat) : MachineState :=
  store s dst (o.compression (readBuffer s src 96))

attribute [local irreducible] readBuffer execute checkEvaluation

theorem syscall (o : Oracle) (s : MachineState) (n src dst : Nat) (bound : n<433) (pc : s.pc=pcAt n)
    (encoded : decodeInstruction (Micro.checkWord n)=some (.base .ECALL))
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96)
    (fromPtr : s.getReg .x10=W src) (toPtr : s.getReg .x12=W dst)
    (sr : Open.AddrOK src 96) (dr : Open.AddrOK dst 32) : Runs o s (afterCall o s src dst) 1 1 := by
  have hf := Micro.fetched n bound _ encoded s pc
  change fetch (submission.image .check) s=_ at hf
  rw [checker_image_eq] at hf
  have sw : (s.getReg .x10).toNat=src := by rw [fromPtr,Open.W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];have := sr.2;unfold MEMORY_BYTES at this;omega
  have dw : (s.getReg .x12).toNat=dst := by rw [toPtr,Open.W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];have := dr.2;unfold MEMORY_BYTES at this;omega
  have query : oracleInput s=some (.inl (readBuffer s src 96)) := by
    unfold oracleInput
    generalize hkind : (s.getReg .x13).toNat = tag
    have tagZero : tag=0 := hkind.symm.trans (by rw [kind];rfl)
    rw [tagZero]
    simp [kind,len,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,rangeValid,sw,dw,sr.1,dr.1,sr.2,dr.2]
  intro fuel;unfold obs
  rw [show 1+fuel=fuel+1 by omega,execute,hf,if_pos mode,query,check_evaluation_public_bind]
  simp only [bind_pure_comp,check_evaluation_map,writeOracleAnswer,toPtr]
  rfl

end CommitGolfCandidate.Late.Check.Normal
