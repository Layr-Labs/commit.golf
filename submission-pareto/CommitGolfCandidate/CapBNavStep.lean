import CommitGolfCandidate.CapBFlowWords
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Opening (getReg_setReg)
open TwoPermutationPrototype.GroupedOpening (openingImage)
set_option maxRecDepth 12000
attribute [local irreducible] execute openingImage

theorem assignNav (s : MachineState) (w : Nat) (inst : Instr) (d : Reg) (v : Word)
    (here : s.pc=pc w) (small : w<2^40) (code : (openingImage.code[w]?).bind decodeInstruction=some (.base inst))
    (ok : ordinaryStep s (.base inst)=some (execInstrBr s inst)) (cost : instructionCycles (.base inst)=1)
    (effect : execInstrBr s inst=(s.setReg d v).setPC (s.pc+4)) (nz : d≠.x0) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=pc (w+1) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if d=r then v else s.getReg r) := by
  have h:=one small here code ok
  rw [cost,effect] at h
  refine ⟨_,h,?_,?_,?_⟩
  · exact (congrArg (fun a : Word=>a+4) here).trans (pc_add w)
  · cases d <;> rfl
  · intro r;simp [getReg_setReg,nz]

theorem branchNav (s : MachineState) (w d : Nat) (inst : Instr) (flag : Bool)
    (here : s.pc=pc w) (small : w<2^40) (code : (openingImage.code[w]?).bind decodeInstruction=some (.base inst))
    (ok : ordinaryStep s (.base inst)=some (execInstrBr s inst)) (cost : instructionCycles (.base inst)=1)
    (effect : execInstrBr s inst=s.setPC (if flag then pc d else pc (w+1))) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if flag then pc d else pc (w+1)) ∧ t.mem=s.mem ∧ ∀r,t.getReg r=s.getReg r := by
  have h:=one small here code ok;rw [cost,effect] at h
  exact ⟨_,h,rfl,rfl,fun _=>rfl⟩

theorem jumpNav (s : MachineState) (w : Nat) (inst : Instr) (dest : Word)
    (here : s.pc=pc w) (small : w<2^40) (code : (openingImage.code[w]?).bind decodeInstruction=some (.base inst))
    (ok : ordinaryStep s (.base inst)=some (execInstrBr s inst)) (cost : instructionCycles (.base inst)=1)
    (effect : execInstrBr s inst=s.setPC dest) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=dest ∧ t.mem=s.mem ∧ ∀r,t.getReg r=s.getReg r := by
  have h:=one small here code ok;rw [cost,effect] at h;exact ⟨_,h,rfl,rfl,fun _=>rfl⟩

end CommitGolfCandidate.CapB
