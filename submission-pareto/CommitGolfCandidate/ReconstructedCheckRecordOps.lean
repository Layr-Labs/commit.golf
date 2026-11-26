import CommitGolfCandidate.ReconstructedCheckRecordSpec
import CommitGolfCandidate.ReconstructedCheckMemoryOps

namespace CommitGolfCandidate.Reconstruction.CheckRecordOps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

def listed (pc : Nat) : List Op→Bool
  | []=>true
  | x::xs=>CheckMemoryOps.word pc (OpeningStraight.actualForm x.instr) && listed (pc+1) xs

theorem image (pc : Nat) (ops : List Op) (h : listed pc ops=true) : CheckStraight.Listed pc (ops.map Op.instr) := by
  induction ops generalizing pc with
  | nil=>trivial
  | cons a rest ih=>
    simp only [listed,Bool.and_eq_true,CheckMemoryOps.word] at h
    exact ⟨CheckDecode.same_sound h.1.2,ih (pc+1) h.2⟩

def dest : Op→List Reg
  | .reg r _ | .ld r ..=>[r]
  | .sd ..=>[]

theorem untouched (m : Model) (ops : List Op) (r : Reg) (h : r∉ops.flatMap dest) :
    (ops.foldl (fun a i=>i.apply a) m).reg r=m.reg r := by
  induction ops generalizing m with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.flatMap_cons,List.mem_append,not_or] at h
    rw [List.foldl_cons,ih _ h.2]
    cases x with
    | reg d e=>
      have nr : d≠r:=fun e=>h.1 (by simp [dest,e])
      simp [Op.apply,Model.set,nr]
    | ld d a i w=>
      have nr : d≠r:=fun e=>h.1 (by simp [dest,e])
      simp [Op.apply,Model.set,nr]
    | sd => rfl

theorem physical {s t : MachineState} {m : Model} (ops : List Op)
    (h : Fits t (ops.foldl (fun a i=>i.apply a) m)) (initial : Fits s m) (r : Reg) (free : r∉ops.flatMap dest) :
    t.getReg r=s.getReg r := (h.registers r).trans ((untouched m ops r free).trans (initial.registers r).symm)

end CommitGolfCandidate.Reconstruction.CheckRecordOps
