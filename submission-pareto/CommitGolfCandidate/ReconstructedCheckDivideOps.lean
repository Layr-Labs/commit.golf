import CommitGolfCandidate.ReconstructedCheckStraight
import CommitGolfCandidate.ReconstructedHonestDivision

namespace CommitGolfCandidate.Reconstruction.CheckDivideOps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine LeafModel CheckRecorded CommitBlocks
set_option maxRecDepth 12000
set_option maxHeartbeats 1100000

inductive Op where
  | normal (a : OpeningOps.Op)
  | div (rd rs rt : Reg)

def Op.instr : Op→Instr
  | .normal a=>a.instr
  | .div rd rs rt=>.DIVU rd rs rt

def Op.apply (m : Model) : Op→Model
  | .normal a=>a.apply m
  | .div rd rs rt=>m.set rd (rv64_divu (m.reg rs) (m.reg rt))

def Valid (m : Model) : List Op→Prop
  | []=>True
  | a::rest=>(match a with | .normal op=>op.Valid m | .div ..=>True) ∧ Valid (a.apply m) rest

theorem block (o : Oracle) (m : Model) (ops : List Op) (pc : Nat) (bound : pc+ops.length≤796)
    (listed : CheckStraight.Listed pc (ops.map Op.instr)) (good : Valid m ops) (s : MachineState)
    (entry : s.pc=addr pc) (fits : Fits s m) :
    ∃ t, Segment o ops.length s t [] ∧ t.pc=addr (pc+ops.length) ∧ Fits t (ops.foldl (fun a i=>i.apply a) m) := by
  induction ops generalizing pc m s with
  | nil=>exact ⟨s,empty o s,by simpa using entry,fits⟩
  | cons op tail ih=>
    obtain ⟨word,rest⟩:=listed;obtain ⟨ok,valid⟩:=good
    simp only [List.length_cons] at bound
    have step : ∃ u,Segment o 1 s u [] ∧ u.pc=addr (pc+1) ∧ Fits u (op.apply m) := by
      cases op with
      | normal a=>exact CheckStraight.block o m [a] pc (by change pc+1≤796;omega) ⟨word,True.intro⟩ ⟨ok,True.intro⟩ s entry fits
      | div rd rs rt=>
        let u:=(s.setReg rd (rv64_divu (m.reg rs) (m.reg rt))).setPC (s.pc+4)
        have f:=CheckStraight.present pc _ (by omega) word s entry
        have single : ordinaryStep s (.base (.DIVU rd rs rt))=some u := by
          simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,u,fits.registers]
        exact ⟨u,plain _ _ _ _ f single,(congrArg (·+4) entry).trans (addr_next pc).symm,(fits.reg rd _).pc _⟩
    obtain ⟨u,one,pos,obj⟩:=step
    obtain ⟨t,more,done,h⟩:=ih (op.apply m) (pc+1) (by omega) rest valid u pos obj
    exact ⟨t,by simpa only [List.length_cons,Nat.add_comm 1,List.nil_append] using compose one more,
      by convert done using 2 <;> simp <;> omega,h⟩

end CommitGolfCandidate.Reconstruction.CheckDivideOps
