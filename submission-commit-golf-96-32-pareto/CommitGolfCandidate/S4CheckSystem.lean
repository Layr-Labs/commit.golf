import CommitGolfCandidate.S4ByteFrame
import CommitGolfCandidate.LateLeafWrites
import CommitGolfCandidate.TruncMask

namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (pcAt pc_succ Digest)

def Finishes (o : Oracle) (s : MachineState) (steps calls : Nat) (ex : Exit) :=
  ∀ fuel,obs o (steps+fuel) s=(ex,calls)

theorem CheckRuns.finish {o : Oracle} {s t : MachineState} {a b m n : Nat} {ex : Exit}
    (x : CheckRuns o s t a m) (y : Finishes o t b n ex) : Finishes o s (a+b) (m+n) ex := by
  intro fuel;rw [Nat.add_assoc,x,y]

def verdictPC : Bool→Nat | true=>4852 | false=>4855
private theorem exitCode (ok : Bool) :
    decodeInstruction (Code.check.word (verdictPC ok))=some (.base (.ADDI .x5 .x0 1)) ∧
    decodeInstruction (Code.check.word (verdictPC ok+1))=some (.base (.ADDI .x10 .x0 (if ok then 0 else 1))) ∧
    decodeInstruction (Code.check.word (verdictPC ok+2))=some (.base .ECALL) := by
  cases ok <;> exact ⟨rfl,rfl,rfl⟩

theorem verdict (ok : Bool) (s : MachineState) (o : Oracle) (pc : s.pc=pcAt (verdictPC ok)) :
    Finishes o s 3 0 (if ok then .success else .failure) := by
  let n:=verdictPC ok
  have nbound : n+3≤Code.check.count:=by cases ok <;> decide
  let t:=execInstrBr s (.ADDI .x5 .x0 1)
  let u:=execInstrBr t (.ADDI .x10 .x0 (if ok then 0 else 1))
  have next : t.pc=pcAt (n+1) := (congrArg (·+4) pc).trans ((pc_succ n).symm)
  have last : u.pc=pcAt (n+2):=(congrArg (·+4) next).trans ((pc_succ (n+1)).symm)
  obtain ⟨first,second,third⟩:=exitCode ok
  have a : Runs .check s t 1 1:=one (by omega) pc _ first rfl
  have b : Runs .check t u 1 1:=one (by omega) next _ second rfl
  have tail : Finishes o u 1 0 (if ok then .success else .failure) := by
    intro fuel;unfold obs
    rw [Nat.add_comm 1 fuel,stop (by omega) last third (by rfl),check_evaluation_pure]
    cases ok <;> rfl
  exact ((ofRuns o a).trans (ofRuns o b)).finish tail

def AddrOK (a n : Nat) := a%8=0 ∧ a+n≤MEMORY_BYTES

theorem call (o : Oracle) {s : MachineState} {n src dst : Nat} (bound : n<Code.check.count)
    (pc : s.pc=pcAt n) (enc : decodeInstruction (Code.check.word n)=some (.base .ECALL))
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96)
    (fromPtr : s.getReg .x10=W src) (toPtr : s.getReg .x12=W dst)
    (sr : AddrOK src 96) (dr : AddrOK dst 32) :
    CheckRuns o s (Late.store s dst (o.compression (readBuffer s src 96))) 1 1 := by
  have hf:=(fetched .check n bound s pc).trans enc
  have sw : (s.getReg .x10).toNat=src := by rw [fromPtr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];have := sr.2;unfold MEMORY_BYTES at this;omega
  have dw : (s.getReg .x12).toNat=dst := by rw [toPtr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];have := dr.2;unfold MEMORY_BYTES at this;omega
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
end CommitGolfCandidate.S4.Machine
