import CommitGolfCandidate.S4Transfer
import CommitGolfCandidate.S4CheckSystem
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ Digest)

def Wrote (s t : MachineState) (a n : Nat) (val : Nat→Byte) := ∀ q,q<2^64 →
  byte t q=if a≤q ∧ q<a+n then val (q-a) else byte s q

theorem storedFlag (s : MachineState) (a : Nat) (v : Byte) (ba : a<2^64) :
    Wrote s (s.setByte (W a) v) a 1 (fun _=>v) := by
  intro q bq;unfold byte;rw [set_byte_read]
  by_cases eqv : q=a
  · subst q;rw [if_pos rfl,if_pos (by omega)]
  · have distinct : W q≠W a:=fun e=>eqv (wordNumber bq ba e)
    rw [if_neg distinct,if_neg (by omega)]

theorem zeroed (s : MachineState) (a : Nat) (ba : a+8≤2^64) (al : a%8=0) :
    Wrote s (s.setMem (W a) 0) a 8 (fun _=>0) := by
  intro q bq;by_cases region : a≤q ∧ q<a+8
  · rw [if_pos region,byteWord,show 8*(q/8)=a by omega,MachineState.getMem_setMem_eq];simp [extractByte]
  · have distinct : W (8*(q/8))≠W a:=by intro eqv;have:=wordNumber (by omega) (by omega) eqv;omega
    rw [if_neg region,byteWord,byteWord s,MachineState.getMem_setMem_ne distinct]

theorem Wrote.away {s t : MachineState} {a n j k : Nat} {v : Nat→Byte} (w : Wrote s t a n v)
    (b : j+k≤2^64) (ext : j+k≤a ∨ a+n≤j) : readBuffer t j k=readBuffer s j k := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl
  intro i bi;have h:=Finset.mem_range.mp bi
  exact congrArg (fun x : Byte=> x.toNat*2^(8*i)) ((w (j+i) (by omega)).trans (if_neg (by omega)))

theorem Wrote.mem {s t t' : MachineState} {a n : Nat} {v : Nat→Byte} (w : Wrote s t a n v)
    (e : t'.mem=t.mem) : Wrote s t' a n v := by
  intro q h;simpa only [byte,MachineState.getByte,MachineState.getMem,e] using w q h

theorem flagRun {c : Code} {n a : Nat} {r v : Reg} {off : BitVec 12} {s : MachineState}
    (limit : n<c.count) (pc : s.pc=pcAt n) (enc : decodeInstruction (c.word n)=some (.base (.SB r v off)))
    (addr : s.getReg r+signExtend12 off=W a) (bound : a+1≤MEMORY_BYTES) :
    let t:=execInstrBr s (.SB r v off)
    Runs c s t 1 1 ∧ t.pc=pcAt (n+1) ∧ (∀ k,t.getReg k=s.getReg k) ∧
      Wrote s t a 1 (fun _=>(s.getReg v).truncate 8) := by
  have ok : memoryArgumentsValid s (.SB r v off)=true:=by
    change accessValid _ 1=true;rw [addr];apply Safe.valid;exact ⟨bound,Nat.mod_one _⟩
  refine ⟨one limit pc _ enc (by simp only [ordinaryStep,if_pos ok]),(congrArg (·+4) pc).trans (pc_succ n).symm,
    fun k=>by cases k <;> rfl,?_⟩
  apply (storedFlag s a ((s.getReg v).truncate 8) (by unfold MEMORY_BYTES at bound;omega)).mem
  simp only [execInstrBr,addr];rfl

theorem zeroRun {c : Code} {n a : Nat} {r : Reg} {off : BitVec 12} {s : MachineState}
    (limit : n<c.count) (pc : s.pc=pcAt n) (enc : decodeInstruction (c.word n)=some (.base (.SD r .x0 off)))
    (addr : s.getReg r+signExtend12 off=W a) (bound : Safe a 8) :
    let t:=execInstrBr s (.SD r .x0 off)
    Runs c s t 1 1 ∧ t.pc=pcAt (n+1) ∧ (∀ k,t.getReg k=s.getReg k) ∧ Wrote s t a 8 (fun _=>0) := by
  have ok : memoryArgumentsValid s (.SD r .x0 off)=true:=by change accessValid _ 8=true;rw [addr];exact bound.valid
  refine ⟨one limit pc _ enc (by simp only [ordinaryStep,if_pos ok]),(congrArg (·+4) pc).trans (pc_succ n).symm,
    fun k=>by cases k <;> rfl,?_⟩
  apply (zeroed s a (bound.1.trans (by decide)) bound.2).mem
  simp only [execInstrBr,addr];rfl

theorem maskedCall (o : Oracle) {s : MachineState} {n src dst : Nat} (bound : n+2≤Code.check.count)
    (pc : s.pc=pcAt n) (enc : decodeInstruction (Code.check.word n)=some (.base .ECALL))
    (cut : decodeInstruction (Code.check.word (n+1))=some (.base (.SH .x12 .x0 30)))
    (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (len : s.getReg .x11=96)
    (fromPtr : s.getReg .x10=W src) (toPtr : s.getReg .x12=W dst)
    (sr : AddrOK src 96) (dr : AddrOK dst 32) :
    let w:=o.compression (readBuffer s src 96)
    CheckRuns o s ((Late.store s dst (Trunc.padLow w)).setPC (pcAt (n+2))) 2 1 := by
  let w:=o.compression (readBuffer s src 96)
  let t:=Late.store s dst w
  have a:=call o (by omega) pc enc mode kind len fromPtr toPtr sr dr
  have next : t.pc=pcAt (n+1):=(congrArg (·+4) pc).trans (pc_succ n).symm
  have result := Trunc.masked_reply_step s dst w toPtr dr.1 (dr.2.trans (by decide))
  rw [toPtr] at result
  have ptr : t.getReg .x12=W dst:=(writeBits_register ..).trans toPtr
  have ok : memoryArgumentsValid t (.SH .x12 .x0 30)=true := by
    change accessValid (t.getReg .x12+W 30) 2=true
    rw [ptr,←BitVec.ofNat_add];exact Safe.valid ⟨by have:=dr.2;omega,by have:=dr.1;omega⟩
  have eqv : s.pc+8=pcAt (n+2) := by rw [pc,pc_succ,pc_succ,BitVec.add_assoc];rfl
  rw [eqv] at result
  have b : Runs .check t _ 1 1:=one (by omega) next _ cut (by simp only [ordinaryStep,if_pos ok];exact congrArg some result)
  exact a.trans (ofRuns o b)
end CommitGolfCandidate.S4.Machine
