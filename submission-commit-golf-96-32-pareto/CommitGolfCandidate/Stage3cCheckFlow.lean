import CommitGolfCandidate.Stage3cCheckEvaluation
import CommitGolfCandidate.Stage3cOperations
import CommitGolfCandidate.Stage3cTrace
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
def observation (o : Oracle) (fuel : Nat) (s : MachineState) : Exit×Nat :=
  let e:=checkEvaluation o (execute (image .check) fuel s false);(e.1.exit,e.2)
def Flow (o : Oracle) (s t : MachineState) (steps calls : Nat) := ∀ fuel,
  observation o (steps+fuel) s=((observation o fuel t).1,calls+(observation o fuel t).2)
theorem Flow.refl (o : Oracle) (s : MachineState) : Flow o s s 0 0:=by intro fuel;simp
theorem Flow.trans {o s t u a b m n} (x : Flow o s t a m) (y : Flow o t u b n) : Flow o s u (a+b) (m+n) := by
  intro fuel;rw [Nat.add_assoc,x,y];simp [Nat.add_assoc]
theorem plain_flow (o : Oracle) {s t : MachineState} {n cycles : Nat} (ok : ∀ fuel,
    execute (image .check) (fuel+n) s false=(do let e←execute (image .check) fuel t false;pure (e.charge cycles 0))) : Flow o s t n 0 := by
  intro fuel; simp only [observation,Nat.add_comm n fuel,ok fuel,bind_pure_comp,check_evaluation_map,Nat.zero_add];rfl
theorem path_flow (o : Oracle) {s : MachineState} {code : PathCode}
    (sites : code.all (matchesWord .check)) (ok : pathReady s code) : Flow o s (pathEnd s code) code.length 0 :=
  plain_flow o (path_run .check false s code sites ok)
theorem one_flow (o : Oracle) {s t : MachineState} {n : Nat} {i : Instr} (ip : s.pc=pcAt n) (code : Site .check n i)
    (ok : ordinaryStep s (.base i)=some t) : Flow o s t 1 0 :=
  plain_flow o (fun fuel=>execute_ordinary_step _ _ _ _ fuel false (code _ ip) ok)
theorem reply_flow (o : Oracle) {s : MachineState} {pc src dst : Nat} (ip : s.pc=pcAt pc) (call : Site .check pc .ECALL)
    (sys : s.getReg .x5=0) (length : s.getReg .x11=96) (kind : s.getReg .x13=0)
    (read : s.getReg .x10=BitVec.ofNat 64 src) (write : s.getReg .x12=BitVec.ofNat 64 dst)
    (rs : src+96≤MEMORY_BYTES) (asrc : src%8=0) (rd : dst+32≤MEMORY_BYTES) (adst : dst%8=0) :
    Flow o s (writeBits s (BitVec.ofNat 64 dst) (o.compression (readBuffer s src 96))) 1 1 := by
  intro fuel
  unfold observation
  rw [Nat.add_comm 1 fuel,hash_run .check false s fuel src dst (call _ ip) sys length kind read write rs asrc rd adst]
  unfold Late.hash
  erw [check_evaluation_public_bind o (.inl (readBuffer s src 96))]
  simp only [bind_pure_comp,check_evaluation_map];rfl

def Finished (o : Oracle) (s : MachineState) (n q : Nat) (ex : Exit) := ∀ fuel,observation o (n+fuel) s=(ex,q)
theorem Flow.finish {o s t n q m k ex} (front : Flow o s t n q) (end_ : Finished o t m k ex) : Finished o s (n+m) (q+k) ex := by
  intro fuel;rw [Nat.add_assoc,front,end_]
theorem known {n op} (good : matchesWord .check (n,op)=true) : Site .check n op := by
  unfold matchesWord at good;split at good
  next h=>exact site h (beq_iff_eq.mp good)
  next=>contradiction

def verdictPC (b : Bool) := if b then 2141 else 2144
theorem verdict (o : Oracle) (s : MachineState) (b : Bool) (pc : s.pc=pcAt (verdictPC b)) :
    Finished o s 3 0 (if b then .success else .failure) := by
  let n:=verdictPC b
  let u:=execInstrBr s (.ADDI .x5 .x0 1)
  let v:=execInstrBr u (.ADDI .x10 .x0 (if b then 0 else 1))
  have pcu : u.pc=pcAt (n+1):=(congrArg (·+4) pc).trans (pc_succ _)
  have pcv : v.pc=pcAt ((n+1)+1):=(congrArg (·+4) pcu).trans (pc_succ _)
  have code : ∀ b : Bool,matchesWord .check (verdictPC b,.ADDI .x5 .x0 1) ∧
    matchesWord .check (verdictPC b+1,.ADDI .x10 .x0 (if b then 0 else 1)) ∧ matchesWord .check (verdictPC b+2,.ECALL) := by decide +kernel
  obtain ⟨a,c,h⟩:=code b
  have first:=one_flow o (t:=u) pc (known a) rfl
  have second:=one_flow o (t:=v) pcu (known c) rfl
  have end_ : Finished o v 1 0 (if b then .success else .failure) := by
    intro fuel
    have halt:=known h v pcv
    have done_ : execute (image .check) (fuel+1) v false=pure ⟨if b then .success else .failure,v,1,0⟩ := by
      rw [execute,halt,show v.getReg .x5=1 by rfl]
      change (pure ⟨if v.getReg .x10=0 then .success else .failure,v,1,0⟩ : OracleComp World Execution)=_
      have arg : v.getReg .x10=(if b then 0 else 1):=by cases b <;> rfl
      rw [arg];cases b <;> rfl
    simp only [observation,Nat.add_comm 1 fuel,done_,check_evaluation_pure]
  exact (first.trans second).finish end_
end CommitGolfCandidate.Chained.BinaryMachine.Check
