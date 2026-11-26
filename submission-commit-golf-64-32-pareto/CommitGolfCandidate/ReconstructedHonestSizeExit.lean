import CommitGolfCandidate.ReconstructedHonestCapComplete
import CommitGolfCandidate.ReconstructedHonestFinishes
import CommitGolfCandidate.ReconstructedHonestSizeSchedule

namespace CommitGolfCandidate.Reconstruction.HonestSizeExit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFinishes HonestCapState
open HonestCapPlan HonestCapInvariant HonestSizeSchedule

def Good (s : MachineState) := (s.getReg .x11).toNat≤65544

/-- A successful halted run is preserved verbatim under arbitrary additional fuel. -/
theorem extend (im : Image) (s : MachineState) (coins : Bool) (fuel extra : Nat) (r : Execution)
    (run : r∈support (execute im fuel s coins)) (success : r.exit=.success) :
    r∈support (execute im (fuel+extra) s coins) := by
  rw [execute_add,mem_support_bind_iff]
  exact ⟨r,run,by simp only [resume,success,reduceCtorEq,ite_false,support_pure,Set.mem_singleton_iff]⟩

theorem finish {f : Nat→Bool} {v : Node} {s : MachineState} (known : Matches v s) (ext : Extra v s)
    (endPhase : v.phase=.returned) (size : (s.getReg .x7).toNat+future f v=3633*128+total f 9)
    (few : population f 9≤128) : SuccessPost image true Good s := by
  have pcEnd : s.pc=10660 := by
    have hp := known.atPc; rw [endPhase] at hp; exact hp
  have small := HonestSizeSchedule.cap_bound f few
  simp only [future,endPhase,Nat.add_zero] at size
  have saved := ext.frozen 68719476328 (by decide +kernel)
  change HonestRanges.Contains (HonestRecordMemory.constant 4176) (s.getMem 68719476328) at saved
  have ret : s.getMem 68719476328=4176 := BitVec.eq_of_toNat_eq (Nat.le_antisymm saved.2 saved.1)
  intro fuel r run success
  have longer := extend _ _ _ fuel 23 r run success
  obtain ⟨t,exec,length⟩ := Return.execute_return s pcEnd ext.stack ret (by omega) fuel
  rw [Nat.add_comm fuel 23,exec,support_pure,Set.mem_singleton_iff] at longer
  subst r
  change (t.getReg .x11).toNat≤65544
  rw [length]; unfold alignedBytes; omega

end CommitGolfCandidate.Reconstruction.HonestSizeExit
