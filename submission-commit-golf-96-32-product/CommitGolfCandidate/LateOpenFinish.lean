import CommitGolfCandidate.LateOpenCapEnd
import CommitGolfCandidate.LateOpenPrefix
import CommitGolfCandidate.OPBatchCap

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def outputSize (k : Nat) := if k=128 then 69120 else 792*k
def cycles (k : Nat) := if k=128 then 100017 else if k=0 then 25 else 28+478*k
def steps (k : Nat) := if k=128 then 100017 else if k=0 then 22 else 25+478*k

def lastState (s : MachineState) (k : Nat) :=
  if k=128 then Part.bBatchExit.after (finalCapB (runRecordsB 128 (jumped s)))
  else Part.normalExit.after (afterRecords s k)

def payload (t : Levels) (salt : SaltTape) (xs : List Index) :=
  if xs.length=128 then xs.flatMap (batchRecord t salt) ++ capBytesB t xs else prefixBytes t salt xs

theorem payload_eq (t : Levels) (salt : SaltTape) (p : Positions) :
    payload t salt (indices p) = opening t salt p := by
  simp only [payload,prefixBytes,capBytesB,opening,indices,Finset.length_sort,depth,BATCH,LOG_LENGTH]
  split <;> simp_all

structure Ready (s : MachineState) (k : Nat) : Prop where
  run : Runs s (lastState s k) (steps k-1) (cycles k-1)
  pc : (lastState s k).pc=pcAt (if k=128 then 405 else 139)
  mode : (lastState s k).getReg .x5=1
  success : (lastState s k).getReg .x10=0
  len : (lastState s k).getReg .x11=W (outputSize k)

theorem opening_ready (s : MachineState) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (abi : ABI s xs.length) (size : xs.length≤LENGTH) (src : Sources s xs tree salt) :
    Ready s xs.length ∧ HasBytes (lastState s xs.length) proofBase (payload tree salt xs) := by
  let k := xs.length
  by_cases batch : xs.length=128
  · have abi' : ABI s 128 := batch ▸ abi
    obtain ⟨st,stpc,anchor,stmem⟩ := start_batch s abi'
    let t := jumped s
    have srcT := src.same_mem stmem
    have recs := records_b t tree salt xs 0 128 (by simpa using stpc) anchor (by decide) batch srcT
    let R := runRecordsB 128 t
    have rpc : R.pc = pcAt 265 := by simpa using recs.pc
    have rdst : R.getReg .x25 = W capBaseB := recs.anchor.dest.trans (congrArg W (by unfold bRecAddr capBaseB; omega))
    have srcR := srcT.afterB size _ _ recs.data.outside (by unfold bRecAddr; omega)
    have cap := cap_b R srcR batch rpc rdst
    let F := finalCapB R
    have done := no_load .bBatchExit F cap.pc rfl
    have eq : lastState s k=Part.bBatchExit.after F := by simp only [lastState,show k=128 from batch,if_true,F,R,t]
    have allRun := ((st.trans recs.run).trans cap.run).trans done.runs
    have endmem : (Part.bBatchExit.after F).mem=F.mem := done.mem
    have recLen : (recordsB tree salt xs 0 128).length = 65280 := by rw [recordsB_len]
    have recData : BWritten t R proofBase (recordsB tree salt xs 0 128) := by
      have := recs.data; simpa only [bRecAddr,Nat.mul_zero,Nat.add_zero] using this
    have capData : BWritten R F (proofBase+(recordsB tree salt xs 0 128).length) (capBytesB tree xs) := by
      rw [recLen]; exact cap.bytes
    have whole := recData.append capData (by rw [recLen]; unfold proofBase MEMORY_BYTES; omega)
    have allRec : recordsB tree salt xs 0 128 = xs.flatMap (batchRecord tree salt) := by
      rw [← all_recordsB, batch]
    constructor
    · constructor
      · rw [eq]
        have sc : 19+703*128+10008+5=steps k-1 := by rw [show k=128 from batch];decide
        have cc : 19+703*128+10008+5=cycles k-1 := by rw [show k=128 from batch];decide
        exact sc ▸ cc ▸ allRun
      · rw [if_pos batch,eq];exact done.pc
      · rw [eq];exact done.regs .x5
      · rw [eq];exact done.regs .x10
      · rw [outputSize,if_pos batch,eq];exact done.regs .x11
    · rw [payload,if_pos batch,eq,← allRec]
      intro j hj
      simpa only [byteAt,MachineState.getByte,MachineState.getMem,endmem] using whole.data j hj
  · let a := afterRecords s k
    have pre := open_prefix s xs tree salt abi size src batch
    have pc : a.pc=pcAt 135 := pre.pc
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
