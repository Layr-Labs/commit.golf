import CommitGolfCandidate.LateOpenCapEnd
import CommitGolfCandidate.LateOpenPrefix

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def outputSize (k : Nat) := if k=128 then 72704 else 792*k
def cycles (k : Nat) := if k=128 then 45875 else if k=0 then 25 else 28+478*k
def steps (k : Nat) := if k=128 then 45875 else if k=0 then 22 else 25+478*k

def lastState (s : MachineState) (k : Nat) :=
  if k=128 then Part.batchExit.after (finalCap (afterRecords s k))
  else Part.normalExit.after (afterRecords s k)

def payload (t : Levels) (salt : SaltTape) (xs : List Index) :=
  if xs.length=128 then prefixBytes t salt xs ++ capBytes t xs else prefixBytes t salt xs

theorem payload_eq (t : Levels) (salt : SaltTape) (p : Positions) :
    payload t salt (indices p) = opening t salt p := by
  simp only [payload,prefixBytes,capBytes,opening,indices,Finset.length_sort,depth,BATCH,LOG_LENGTH]
  split <;> simp_all

theorem output_length (t : Levels) (salt : SaltTape) (xs : List Index) :
    (payload t salt xs).length=outputSize xs.length := by
  by_cases batch : xs.length=128
  · simp [payload,batch,outputSize,prefix_len,depth,recordSize,capBytes,List.length_flatMap,bytes,List.sum_replicate]
  · simp only [payload,outputSize,if_neg batch,prefix_len,depth,recordSize]

structure Ready (s : MachineState) (k : Nat) : Prop where
  run : Runs s (lastState s k) (steps k-1) (cycles k-1)
  pc : (lastState s k).pc=pcAt (if k=128 then 134 else 139)
  mode : (lastState s k).getReg .x5=1
  success : (lastState s k).getReg .x10=0
  len : (lastState s k).getReg .x11=W (outputSize k)

theorem opening_ready (s : MachineState) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (abi : ABI s xs.length) (size : xs.length≤LENGTH) (src : Sources s xs tree salt) :
    Ready s xs.length ∧ HasBytes (lastState s xs.length) proofBase (payload tree salt xs) := by
  let k := xs.length
  let a := afterRecords s k
  have pre := open_prefix s xs tree salt abi size src
  by_cases batch : xs.length=128
  · have pc : a.pc=pcAt 62 := by simpa only [if_pos batch] using pre.pc
    have bytesEq : (prefixBytes tree salt xs).length=68608 := by rw [prefix_len,batch];decide
    have inputA := src.after size proofBase _ pre.bytes.outside le_rfl (by decide) (by rw [bytesEq] <;> decide)
    have cap := cap_run a inputA batch pc (pre.cap batch)
    let b := finalCap a
    have done := no_load .batchExit b cap.pc rfl
    have eq : lastState s k=Part.batchExit.after b := by simp only [lastState,show k=128 from batch,if_true,b,a]
    have allRun := (pre.run.trans cap.run).trans done.runs
    have endmem : (Part.batchExit.after b).mem=b.mem := done.mem
    have caplen : (capBytes tree xs).length=4096 := by simp [capBytes,List.length_flatMap,bytes,List.sum_replicate]
    have keep := pre.bytes.data.after_outside cap.bytes.outside (by decide) (by rw [caplen] <;> decide)
      (by rw [bytesEq] <;> decide) (Or.inl (by rw [bytesEq];exact le_rfl))
    have rest : HasBytes b (proofBase+(prefixBytes tree salt xs).length) (capBytes tree xs) := by rw [bytesEq];exact cap.bytes.data
    have out := keep.append rest
    constructor
    · constructor
      · rw [eq]
        have sc : prefixCost k+4120+5=steps k-1 := by rw [show k=128 from batch];decide
        have cc : prefixCost k+4120+5=cycles k-1 := by rw [show k=128 from batch];decide
        exact sc ▸ cc ▸ allRun
      · rw [if_pos batch,eq];exact done.pc
      · rw [eq];exact done.regs .x5
      · rw [eq];exact done.regs .x10
      · rw [outputSize,if_pos batch,eq];exact done.regs .x11
    · rw [payload,if_pos batch,eq]
      intro j hj
      simpa only [byteAt,MachineState.getByte,MachineState.getMem,endmem] using out j hj
  · have pc : a.pc=pcAt 135 := by simpa only [if_neg batch] using pre.pc
    have done := no_load .normalExit a pc rfl
    have eq : lastState s k=Part.normalExit.after a := by simp only [lastState,if_neg (show k≠128 from batch),a]
    have len := done.regs .x11
    change _ = a.getReg .x16 * 792 at len
    rw [pre.count] at len
    constructor
    · constructor
      · rw [eq]
        have sc : prefixCost k+4=steps k-1 := by
          unfold prefixCost steps depth;rw [if_neg (show k≠128 from batch)];by_cases z:k=0 <;> simp [z,batch,k,Nat.mul_comm] <;> omega
        have cc : prefixCost k+7=cycles k-1 := by
          unfold prefixCost cycles depth;rw [if_neg (show k≠128 from batch)];by_cases z:k=0 <;> simp [z,batch,k,Nat.mul_comm] <;> omega
        exact sc ▸ cc ▸ pre.run.trans done.runs
      · rw [if_neg batch,eq];exact done.pc
      · rw [eq];exact done.regs .x5
      · rw [eq];exact done.regs .x10
      · rw [eq,outputSize,if_neg batch]
        exact len.trans ((BitVec.ofNat_mul k 792).symm.trans (congrArg W (Nat.mul_comm ..)))
    · rw [eq,payload,if_neg batch]
      intro j hj
      have m : (Part.normalExit.after a).mem=(afterRecords s xs.length).mem := done.mem
      simpa only [byteAt,MachineState.getByte,MachineState.getMem,m] using pre.bytes.data j hj

end CommitGolfCandidate.Late.Open
