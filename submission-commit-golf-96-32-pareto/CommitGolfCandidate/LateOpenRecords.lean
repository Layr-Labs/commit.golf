import CommitGolfCandidate.LateFormat
import CommitGolfCandidate.LateOpenRecord

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def runRecords (d : Nat) : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => runRecords d n (recordStep s d)

def records (tree : Levels) (salt : SaltTape) (xs : List Index) (d r n : Nat) : Proof :=
  (List.range' r n).flatMap fun j => record tree salt d (ix xs j)

theorem record_cons (tree : Levels) (salt : SaltTape) (xs : List Index) (d r n : Nat) :
    records tree salt xs d r (n+1) =
      record tree salt d (ix xs r) ++ records tree salt xs d (r+1) n := by
  simp only [records,List.range'_succ,List.flatMap_cons]

theorem records_len (tree : Levels) (salt : SaltTape) (xs : List Index) (d r n : Nat) :
    (records tree salt xs d r n).length=recordSize d*n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [record_cons,List.length_append,record_size,ih,Nat.mul_succ];exact Nat.add_comm _ _

theorem all_records_eq (tree : Levels) (salt : SaltTape) (xs : List Index) (d : Nat) :
    records tree salt xs d 0 xs.length=xs.flatMap (record tree salt d) := by
  have xsEq : (List.range xs.length).map (ix xs)=xs := by
    apply List.ext_getElem
    · simp
    · intro k _ hk; simp only [List.getElem_map,List.getElem_range,ix,List.getElem?_eq_getElem hk,Option.getD_some]
  unfold records
  rw [←List.range_eq_range',←List.flatMap_map, xsEq]

structure RecordsResult (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (d r n : Nat) : Prop where
  run : Runs s (runRecords d n s) ((22+19*d)*n) ((22+19*d)*n)
  pc : (runRecords d n s).pc=pcAt (if r+n<xs.length then 19 else 60)
  frame : RecordFrame (runRecords d n s) xs.length d (r+n)
  data : Written s (runRecords d n s) (recordAddr d r) (records tree salts xs d r n)

theorem records_run (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (d r n : Nat)
    (pc : s.pc=pcAt (if r<xs.length then 19 else 60)) (fr : RecordFrame s xs.length d r)
    (inside : r+n≤xs.length) (pos : 0<d) (depth : d≤LOG_LENGTH) (size : xs.length≤LENGTH)
    (src : Sources s xs tree salts) : RecordsResult s tree salts xs d r n := by
  induction n generalizing r s with
  | zero => exact ⟨Runs.refl _,by simpa only [runRecords,Nat.add_zero] using pc,fr,Written.empty _ _⟩
  | succ n ih =>
    have lt : r<xs.length := by omega
    rw [if_pos lt] at pc
    have h := full_record s tree salts xs d r pc fr lt pos depth size src
    let bs := record tree salts d (ix xs r)
    have len : bs.length=recordSize d := record_size .. 
    have high : proofBase≤recordAddr d r := by unfold recordAddr;omega
    have al : bs.length%8=0 := by rw [len];unfold recordSize;omega
    have tail := ih (recordStep s d) (r+1) h.pc h.frame (by omega)
      (src.after size _ _ h.data.outside high (record_aligned d r) al)
    have plus : r+1+n=r+(n+1) := by omega
    have next : recordAddr d r+bs.length=recordAddr d (r+1) := by
      rw [len];unfold recordAddr;rw [Nat.mul_succ];omega
    have endBound := record_fits d r depth (by omega)
    have later : Written (recordStep s d) (runRecords d n (recordStep s d))
        (recordAddr d r+bs.length) (records tree salts xs d (r+1) n) := next.symm ▸ tail.data
    refine ⟨?_,by simpa only [runRecords,plus] using tail.pc,by simpa only [runRecords,plus] using tail.frame,?_⟩
    · exact (show (22+19*d)+(22+19*d)*n=(22+19*d)*(n+1) by rw [Nat.mul_succ,Nat.add_comm]) ▸ h.runs.trans tail.run
    · rw [record_cons]
      exact h.data.append later (next.symm ▸ record_aligned d (r+1))
        (by rw [records_len]; simp [recordSize,Nat.mul_mod,Nat.add_mod]) (by rw [len]; exact endBound)

end CommitGolfCandidate.Late.Open
