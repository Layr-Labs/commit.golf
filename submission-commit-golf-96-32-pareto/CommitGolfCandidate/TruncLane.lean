import CommitGolfCandidate.TruncParentCore
import CommitGolfCandidate.TruncMask
import CommitGolfCandidate.CommitLoop
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 9000
set_option maxHeartbeats 250000

def projectedBank : Bank → Bool | .high | .tail => true | _ => false
def laneState (b : Bank) (s : MachineState) (u : Nat) (value : Digest) :=
  if projectedBank b then (parentCallState s u (padLow value)).setPC (s.pc+16) else parentCallState s u value

theorem laneMem (b : Bank) (s : MachineState) (u : Nat) (v : Digest) :
    (laneState b s u v).mem=(writeBits s (parentOutput s u) (if projectedBank b then padLow v else v)).mem := by
  by_cases h : projectedBank b=true
  · simp only [laneState,if_pos h,MachineState.setPC];exact parent_call_memory s u (padLow v)
  · simp only [laneState,if_neg h];exact parent_call_memory s u v

theorem laneKept (b : Bank) (s : MachineState) (u : Nat) (v : Digest) (r : Reg) (a : r≠.x10) (c : r≠.x12) :
    (laneState b s u v).getReg r=s.getReg r := by
  by_cases h : projectedBank b=true
  · simp only [laneState,if_pos h,MachineState.getReg_setPC];exact parent_call_register s u (padLow v) r a c
  · simp only [laneState,if_neg h];exact parent_call_register s u v r a c

theorem lanePC (b : Bank) (s : MachineState) (u : Nat) (v : Digest) :
    (laneState b s u v).pc=s.pc+(if projectedBank b then 16 else 12) := by
  cases b <;> first | rfl | exact parent_call_pc s u v

private theorem destSetup (s : MachineState) (u : Nat) : (parentSetupState s u).getReg .x12=parentOutput s u := by
  simp [parentSetupState,MachineState.getReg_setPC,MachineState.getReg_setReg_eq]

private theorem storeValid (s : MachineState) (u : Nat) (v : Digest) (valid : ParentCallValid s u) :
    memoryArgumentsValid (parentCallState s u v) (.SH .x12 .x0 30)=true := by
  have h:=valid.2.2.1
  have align:=valid.2.2.2
  simp only [rangeValid,decide_eq_true_eq] at h
  change accessValid ((parentCallState s u v).getReg .x12+signExtend12 30) 2=true
  rw [parentCallState,writeBits_register,destSetup,show signExtend12 30=BitVec.ofNat 64 30 by decide]
  have x:=word_ofNat_toNat (parentOutput s u)
  conv_lhs => lhs;lhs;rw [x]
  rw [← BitVec.ofNat_add]
  have bound : (parentOutput s u).toNat+30<2^64 := by change _+32≤2^36 at h;omega
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨by omega,by omega⟩

theorem afterMask (s : MachineState) (b : Bank) (j : Nat) (hj : inBank b j)
    (on : b=.high ∨ b=.tail) (pc : s.pc=BitVec.ofNat 64 (4096+4*startWord b j))
    (valid : ParentCallValid s (31-j)) (v : Digest) (fuel : Nat) :
    execute (submission.image .commit) (1+fuel) (parentCallState s (31-j) v) true =
      (do let r←execute (submission.image .commit) fuel (laneState b s (31-j) v) true; return r.charge 1 0) := by
  let u:=31-j
  have small := bankBound b hj
  have loc : startWord b j+3<2048 := by cases b <;> simp [startWord] <;> omega
  have npc : (parentCallState s u v).pc=BitVec.ofNat 64 (4096+4*(startWord b j+3)) := by
    rw [parent_call_pc,pc];exact ofNat64_add_eq _ 12 _ (by omega)
  have fetched:=fetchAt (submission.image .commit) (parentCallState s u v) (startWord b j+3) _ loc npc (maskDecode b j hj on)
  have dst:=destSetup s u
  have step := masked_reply_step (parentSetupState s u) (parentOutput s u).toNat v
    (dst.trans (word_ofNat_toNat (parentOutput s u))) valid.2.2.2
    (by have h : (parentOutput s u).toNat+32≤2^36 := of_decide_eq_true valid.2.2.1;omega)
  have same : execInstrBr (parentCallState s u v) (.SH .x12 .x0 30)=laneState b s u v := by
    rw [dst] at step
    have on' : projectedBank b=true := by rcases on with rfl|rfl <;> rfl
    rw [laneState,if_pos on'];unfold parentCallState
    rw [show (parentSetupState s u).pc+8=s.pc+16 by change s.pc+8+8=s.pc+16;rw [BitVec.add_assoc];rfl] at step
    exact step
  have ordinary : ordinaryStep (parentCallState s u v) (.base (.SH .x12 .x0 30))=some (laneState b s u v) := by
    simp only [ordinaryStep,storeValid s u v valid,ite_true,same]
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched ordinary]
  rfl

theorem runLane (s : MachineState) (b : Bank) (j : Nat) (hj : inBank b j)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*startWord b j))
    (r5 : s.getReg .x5=0) (r11 : s.getReg .x11=96) (r13 : s.getReg .x13=0)
    (valid : ParentCallValid s (31-j)) (fuel : Nat) :
    execute (submission.image .commit) ((if projectedBank b then 4 else 3)+fuel) s true =
      (do let v ← World.query (.inr (parentQuery s (31-j)))
          let r ← execute (submission.image .commit) fuel (laneState b s (31-j) v) true
          return r.charge (if projectedBank b then 11 else 10) 1) := by
  by_cases on : b=.high ∨ b=.tail
  · have h : projectedBank b=true := by rcases on with rfl|rfl <;> rfl
    rw [if_pos h,show 4+fuel=3+(1+fuel) by omega,rawLane s b j hj pc r5 r11 r13 valid]
    apply bind_congr;intro v
    change Digest at v
    rw [afterMask s b j hj on pc valid v fuel]
    simp [bind_assoc,pure_bind,Execution.charge,if_pos h,← Nat.add_assoc]
  · have h : projectedBank b=false := by cases b <;> simp_all [projectedBank]
    simpa only [h,Bool.false_eq_true,ite_false,laneState] using rawLane s b j hj pc r5 r11 r13 valid fuel
end CommitGolfCandidate.Trunc
