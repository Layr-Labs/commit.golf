import CommitGolfCandidate.LateOpenCapMemory
import CommitGolfCandidate.LateOpenRecords
import CommitGolfCandidate.LateOpenStart

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def beforeMode (s : MachineState) (k : Nat) :=
  if k=0 then dispatch s else runRecords (depth k) k (begun s k)

def gate (s : MachineState) := Test.batch.after (Part.mode.after s)
def afterRecords (s : MachineState) (k : Nat) := gate (beforeMode s k)

def prefixCost (k : Nat) := if k=0 then 17 else 18+(22+19*depth k)*k+2

private theorem mode_run (s : MachineState) (k : Nat) (pc : s.pc=pcAt 60) (count : s.getReg .x16=W k)
    (small : k≤LENGTH) :
    Runs s (gate s) 2 2 ∧ (gate s).pc=pcAt (if k=128 then 62 else 135) ∧ (gate s).mem=s.mem ∧
    (gate s).getReg .x16=W k ∧ (gate s).getReg .x25=s.getReg .x25 := by
  have b := no_load .mode s pc rfl
  let a := Part.mode.after s
  have c : a.getReg .x16=W k := (b.keep _ rfl).trans count
  have const : a.getReg .x6=W 128 := b.regs .x6
  have taken : Test.batch.taken a=decide (k≠128) := by
    change (a.getReg .x16 != a.getReg .x6)=_
    rw [c,const];change (!(W k == W 128))=_
    rw [eq_test k 128 (by change k≤16777216 at small;omega) (by decide)]
    by_cases e:k=128 <;> simp [e]
  refine ⟨b.runs.trans (test_run .batch a b.pc),?_,b.mem,MachineState.getReg_setPC.trans c,
    MachineState.getReg_setPC.trans (b.keep _ rfl)⟩
  change pcAt (if Test.batch.taken a then _ else _) = _
  rw [taken];by_cases e : k=128 <;> simp [e,Test.start,Test.target]

def prefixBytes (tree : Levels) (salts : SaltTape) (xs : List Index) :=
  xs.flatMap (record tree salts (depth xs.length))

structure PrefixResult (s : MachineState) (xs : List Index) (tree : Levels) (salts : SaltTape) : Prop where
  run : Runs s (afterRecords s xs.length) (prefixCost xs.length) (prefixCost xs.length)
  pc : (afterRecords s xs.length).pc=pcAt 135
  count : (afterRecords s xs.length).getReg .x16=W xs.length
  bytes : Written s (afterRecords s xs.length) proofBase (prefixBytes tree salts xs)

theorem open_prefix (s : MachineState) (xs : List Index) (tree : Levels) (salts : SaltTape)
    (abi : ABI s xs.length) (size : xs.length≤LENGTH) (src : Sources s xs tree salts) (normal : xs.length≠128) :
    PrefixResult s xs tree salts := by
  by_cases empty : xs=[]
  · subst xs
    obtain ⟨head,pc,c,mem⟩ := start_empty s abi
    obtain ⟨tail,fin,stay,cnt,_⟩ := mode_run (dispatch s) 0 pc c (by decide)
    refine ⟨head.trans tail,fin.trans (by rfl),cnt,?_⟩
    exact (Written.empty s proofBase).congr_mem rfl (stay.trans mem)
  · have pos : 0<xs.length := List.length_pos_iff.mpr empty
    let k := xs.length
    let d := depth k
    let a := begun s k
    let b := runRecords d k a
    have dpos : 0<d := by dsimp [d,depth];split <;> decide
    have bound : d≤LOG_LENGTH := by dsimp [d,depth];split <;> decide
    have later := start_records s k pos size abi normal
    obtain ⟨head,pc,fr,mem⟩ := later
    have r := records_run a tree salts xs d 0 k (by simpa only [if_pos pos] using pc) fr
      (by simp [k]) dpos bound size (src.same_mem mem)
    have finishPC : b.pc=pcAt 60 := by
      change (runRecords d k a).pc=_
      simpa only [Nat.zero_add,lt_self_iff_false,if_false,k] using r.pc
    have total := mode_run b k finishPC r.frame.count size
    obtain ⟨tail,fin,stay,cnt,ptr⟩ := total
    have done : afterRecords s k=gate b := by simp only [afterRecords,beforeMode,if_neg (show k≠0 by omega),b,a,d]
    refine ⟨?_,?_,?_,?_⟩
    · rw [done];unfold prefixCost;rw [if_neg (by omega : k≠0)]
      exact (head.trans r.run).trans tail
    · have e : (if k=128 then 62 else 135) = 135 := if_neg normal
      rw [done];rw [e] at fin;exact fin
    · rw [done];exact cnt
    · rw [done]
      have seq := r.data.congr_mem mem.symm stay
      rw [all_records_eq] at seq
      exact seq

theorem prefix_len (tree : Levels) (s : SaltTape) (xs : List Index) :
    (prefixBytes tree s xs).length=recordSize (depth xs.length)*xs.length := by
  rw [prefixBytes,←all_records_eq,records_len]

end CommitGolfCandidate.Late.Open
