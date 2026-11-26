import CommitGolfCandidate.ReconstructedCheckDecode
import CommitGolfCandidate.ReconstructedOpeningStraight

namespace CommitGolfCandidate.Reconstruction.CheckStraight
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine LeafModel LeafSteps OpeningOps CheckRecorded CommitBlocks
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer execute ArtifactEncoding.decode

def actualAt (i : Nat) := decodeInstruction (Artifact.checkCode.get 32 ⟨i%796,by omega⟩)
def Listed : Nat→List Instr→Prop
  | _,[]=>True
  | pc,i::rest=>actualAt pc=some (OpeningStraight.actualForm i) ∧ Listed (pc+1) rest

theorem present (pc : Nat) (i : Instruction) (h : pc<796) (ok : actualAt pc=some i) (s : MachineState)
    (entry : s.pc=addr pc) : fetch image s=some i := by
  rw [fetch_packed image Artifact.checkCode rfl pc h (by omega) s entry]
  simpa only [actualAt,Nat.mod_eq_of_lt h] using ok

private theorem same (s : MachineState) (op : Instr) :
    ordinaryStep s (OpeningStraight.actualForm op)=ordinaryStep s (.base op) := by cases op <;> rfl

private theorem segment (o : Oracle) (ops : List Instr) (s t : MachineState) (run : Run o ops s t)
    (noQuery : ∀ i∈ops,i≠.ECALL) (pc : Nat) (bound : pc+ops.length≤796) (atPc : s.pc=addr pc) (listed : Listed pc ops) :
    Segment o ops.length s t [] := by
  induction run generalizing pc with
  | nil=>exact empty _ _
  | @cons op ops s t u step rest ih=>
    obtain ⟨head,tail⟩:=listed
    simp only [List.length_cons] at bound
    have f:=present pc _ (by omega) head s atPc
    have one : Segment o 1 s t [] := by
      cases step with
      | ordinary _ _ _ h _=>exact plain _ _ _ _ f ((same ..).trans h)
      | permute =>exact False.elim (noQuery _ List.mem_cons_self rfl)
    have loc:=(step.advance.trans (congrArg (·+4) atPc)).trans (addr_next pc).symm
    have more:=ih (fun j mem=>noQuery j (List.mem_cons_of_mem _ mem)) (pc+1) (by omega) loc tail
    simpa only [List.length_cons,Nat.add_comm 1,List.nil_append] using compose one more

theorem block (o : Oracle) (m : Model) (ops : List OpeningOps.Op) (pc : Nat) (bound : pc+ops.length≤796)
    (table : Listed pc (ops.map OpeningOps.Op.instr)) (ok : Checked m ops) (s : MachineState)
    (entry : s.pc=addr pc) (fits : Fits s m) :
    ∃ t, Segment o ops.length s t [] ∧ t.pc=addr (pc+ops.length) ∧ Fits t (ops.foldl (fun a i=>i.apply a) m) := by
  obtain ⟨t,run,ht⟩:=checked_run o m ops ok s fits
  have noQuery : ∀ i∈(ops.map OpeningOps.Op.instr),i≠.ECALL := by
    intro i mem
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp mem
    cases a with
    | reg rd e=>cases e <;> simp [OpeningOps.Op.instr,OpeningOps.Expr.instr]
    | ld | sd=>simp [OpeningOps.Op.instr]
  have sg:=segment o _ s t run noQuery pc (by simpa using bound) entry table
  exact ⟨t,by simpa only [List.length_map] using sg,by simpa only [List.length_map] using run.next_pc pc entry,ht⟩

end CommitGolfCandidate.Reconstruction.CheckStraight
