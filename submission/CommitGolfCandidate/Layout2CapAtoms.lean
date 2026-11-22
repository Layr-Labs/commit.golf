import CommitGolfCandidate.Layout2CapCode
import CommitGolfCandidate.Layout2Views
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Layout2.Quartet (checkImage run_control)
open TwoPermutationPrototype.Opening (getReg_setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 1300000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
attribute [local simp] zero mem_pc pc_pc mem_reg pc_ite reg_ite mem_ite
attribute [local irreducible] execute checkImage

private theorem jump_control (s : MachineState) (w d : Nat) (rd : Reg) (off : BitVec 21)
    (here : s.pc=pc w) (valid : w<2^40) (code : (checkImage.code[w]?).bind decodeInstruction=some (.base (.JAL rd off)))
    (delta : pc w+signExtend21 off=pc d) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc d ∧ u.mem=s.mem ∧
      ∀ r,u.getReg r=(if rd=r ∧ rd≠.x0 then pc (w+1) else s.getReg r) := by
  let u:=execInstrBr s (.JAL rd off)
  refine ⟨u,run_control _ _ _ _ _ valid here code rfl rfl,?_,?_,?_⟩
  · change s.pc+signExtend21 off=pc d;rw [here];exact delta
  · simp only [u,execInstrBr,mem_pc,mem_reg]
  · intro r;simp only [u,execInstrBr,MachineState.getReg_setPC,getReg_setReg,here,pc_next]

theorem atom0 (s : MachineState) (here : s.pc=pc 0) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1002) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  simpa using jump_control s 0 1002 .x0 4008 here (by decide) capCode0 (by decide +kernel)

theorem atom1002 (s : MachineState) (here : s.pc=pc 1002) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1003) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then 534#64 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x6 .x0 534)
  have ok : memoryArgumentsValid s (.ADDI .x6 .x0 534)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1002<2^40) here capCode1002 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1003 (s : MachineState) (here : s.pc=pc 1003) :
    ∃ u, Runs checkImage s u 1 4 ∧ u.pc=(pc 1004) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then ((s.getReg .x16)*(s.getReg .x6)) else s.getReg r) := by
  let u:=execInstrBr s (.MUL .x6 .x16 .x6)
  have ok : memoryArgumentsValid s (.MUL .x6 .x16 .x6)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1003<2^40) here capCode1003 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1004 (s : MachineState) (here : s.pc=pc 1004) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if BitVec.ult (s.getReg .x17) (s.getReg .x6) then pc 364 else pc 1005) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BLTU .x17 .x6 5632)
  have ok : memoryArgumentsValid s (.BLTU .x17 .x6 5632)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1004<2^40) here capCode1004 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1005 (s : MachineState) (here : s.pc=pc 1005) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x16) == 0#64 then pc 1154 else pc 1006) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BEQ .x16 .x0 596)
  have ok : memoryArgumentsValid s (.BEQ .x16 .x0 596)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1005<2^40) here capCode1005 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1006 (s : MachineState) (here : s.pc=pc 1006) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1007) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x8=r then ((s.getReg .x15)+(s.getReg .x6)) else s.getReg r) := by
  let u:=execInstrBr s (.ADD .x8 .x15 .x6)
  have ok : memoryArgumentsValid s (.ADD .x8 .x15 .x6)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1006<2^40) here capCode1006 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1007 (s : MachineState) (here : s.pc=pc 1007) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1008) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x9=r then ((s.getReg .x17)-(s.getReg .x6)) else s.getReg r) := by
  let u:=execInstrBr s (.SUB .x9 .x17 .x6)
  have ok : memoryArgumentsValid s (.SUB .x9 .x17 .x6)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1007<2^40) here capCode1007 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1008 (s : MachineState) (here : s.pc=pc 1008) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1009) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x20=r then 952#64 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x20 .x0 952)
  have ok : memoryArgumentsValid s (.ADDI .x20 .x0 952)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1008<2^40) here capCode1008 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1009 (s : MachineState) (here : s.pc=pc 1009) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1010) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x21=r then 8#64 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x21 .x0 8)
  have ok : memoryArgumentsValid s (.ADDI .x21 .x0 8)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1009<2^40) here capCode1009 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1010 (s : MachineState) (here : s.pc=pc 1010) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if BitVec.ult (s.getReg .x9) (s.getReg .x20) then pc 1019 else pc 1011) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BLTU .x9 .x20 36)
  have ok : memoryArgumentsValid s (.BLTU .x9 .x20 36)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1010<2^40) here capCode1010 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1011 (s : MachineState) (here : s.pc=pc 1011) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1012) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x18=r then 952#64 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x18 .x0 952)
  have ok : memoryArgumentsValid s (.ADDI .x18 .x0 952)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1011<2^40) here capCode1011 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1012 (s : MachineState) (here : s.pc=pc 1012) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1013) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then 86016#64 else s.getReg r) := by
  let u:=execInstrBr s (.LUI .x19 21)
  have ok : memoryArgumentsValid s (.LUI .x19 21)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1012<2^40) here capCode1012 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1013 (s : MachineState) (here : s.pc=pc 1013) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1014) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then ((s.getReg .x19)+(signExtend12 3776)) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x19 .x19 3776)
  have ok : memoryArgumentsValid s (.ADDI .x19 .x19 3776)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1013<2^40) here capCode1013 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1014 (s : MachineState) (here : s.pc=pc 1014) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1015) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then ((s.getReg .x19)+(s.getReg .x2)) else s.getReg r) := by
  let u:=execInstrBr s (.ADD .x19 .x19 .x2)
  have ok : memoryArgumentsValid s (.ADD .x19 .x19 .x2)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1014<2^40) here capCode1014 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1015 (s : MachineState) (here : s.pc=pc 1015) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 759) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x31=r then (pc 1016) else s.getReg r) := by
  simpa using jump_control s 1015 759 .x31 2096128 here (by decide) capCode1015 (by decide +kernel)

theorem atom1016 (s : MachineState) (here : s.pc=pc 1016) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1017) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x8=r then ((s.getReg .x8)+952#64) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x8 .x8 952)
  have ok : memoryArgumentsValid s (.ADDI .x8 .x8 952)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1016<2^40) here capCode1016 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1017 (s : MachineState) (here : s.pc=pc 1017) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1018) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x9=r then ((s.getReg .x9)+(signExtend12 3144)) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x9 .x9 3144)
  have ok : memoryArgumentsValid s (.ADDI .x9 .x9 3144)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1017<2^40) here capCode1017 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1018 (s : MachineState) (here : s.pc=pc 1018) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1010) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  simpa using jump_control s 1018 1010 .x0 2097120 here (by decide) capCode1018 (by decide +kernel)

theorem atom1019 (s : MachineState) (here : s.pc=pc 1019) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1020) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then ((s.getReg .x9)+6#64) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x5 .x9 6)
  have ok : memoryArgumentsValid s (.ADDI .x5 .x9 6)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1019<2^40) here capCode1019 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1020 (s : MachineState) (here : s.pc=pc 1020) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1021) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then 30#64 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x6 .x0 30)
  have ok : memoryArgumentsValid s (.ADDI .x6 .x0 30)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1020<2^40) here capCode1020 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1021 (s : MachineState) (here : s.pc=pc 1021) :
    ∃ u, Runs checkImage s u 1 4 ∧ u.pc=(pc 1022) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then (rv64_divu (s.getReg .x5) (s.getReg .x6)) else s.getReg r) := by
  let u:=execInstrBr s (.DIVU .x5 .x5 .x6)
  have ok : memoryArgumentsValid s (.DIVU .x5 .x5 .x6)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1021<2^40) here capCode1021 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1022 (s : MachineState) (here : s.pc=pc 1022) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1023) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then ((s.getReg .x5) <<< (3:Nat)) else s.getReg r) := by
  let u:=execInstrBr s (.SLLI .x5 .x5 3)
  have ok : memoryArgumentsValid s (.SLLI .x5 .x5 3)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1022<2^40) here capCode1022 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1023 (s : MachineState) (here : s.pc=pc 1023) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1024) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then 86016#64 else s.getReg r) := by
  let u:=execInstrBr s (.LUI .x19 21)
  have ok : memoryArgumentsValid s (.LUI .x19 21)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1023<2^40) here capCode1023 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1024 (s : MachineState) (here : s.pc=pc 1024) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1025) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then ((s.getReg .x19)+(signExtend12 3520)) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x19 .x19 3520)
  have ok : memoryArgumentsValid s (.ADDI .x19 .x19 3520)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1024<2^40) here capCode1024 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1025 (s : MachineState) (here : s.pc=pc 1025) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1026) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then ((s.getReg .x19)+(s.getReg .x2)) else s.getReg r) := by
  let u:=execInstrBr s (.ADD .x19 .x19 .x2)
  have ok : memoryArgumentsValid s (.ADD .x19 .x19 .x2)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1025<2^40) here capCode1025 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1026 (s : MachineState) (here : s.pc=pc 1026) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1027) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then ((s.getReg .x19)+(s.getReg .x5)) else s.getReg r) := by
  let u:=execInstrBr s (.ADD .x19 .x19 .x5)
  have ok : memoryArgumentsValid s (.ADD .x19 .x19 .x5)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1026<2^40) here capCode1026 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1027 (s : MachineState) (here : s.pc=pc 1027) (valid : accessValid (s.getReg .x19) 2=true) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1028) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then ((s.getHalfword (s.getReg .x19)).zeroExtend 64) else s.getReg r) := by
  let u:=execInstrBr s (.LHU .x6 .x19 0)
  have ok : memoryArgumentsValid s (.LHU .x6 .x19 0)=true := by simpa [memoryArgumentsValid,memAccess,signExtend12] using valid
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1027<2^40) here capCode1027 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1028 (s : MachineState) (here : s.pc=pc 1028) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x6) != (s.getReg .x9) then pc 364 else pc 1029) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BNE .x6 .x9 5536)
  have ok : memoryArgumentsValid s (.BNE .x6 .x9 5536)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1028<2^40) here capCode1028 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1029 (s : MachineState) (here : s.pc=pc 1029) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x9) == 0#64 then pc 1034 else pc 1030) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BEQ .x9 .x0 20)
  have ok : memoryArgumentsValid s (.BEQ .x9 .x0 20)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1029<2^40) here capCode1029 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1030 (s : MachineState) (here : s.pc=pc 1030) (valid : accessValid ((s.getReg .x19)+4#64) 4=true) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1031) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then ((s.getWord32 ((s.getReg .x19)+4#64)).zeroExtend 64) else s.getReg r) := by
  let u:=execInstrBr s (.LWU .x6 .x19 4)
  have ok : memoryArgumentsValid s (.LWU .x6 .x19 4)=true := by simpa [memoryArgumentsValid,memAccess,signExtend12] using valid
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1030<2^40) here capCode1030 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1031 (s : MachineState) (here : s.pc=pc 1031) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1032) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then ((s.getReg .x2)+(s.getReg .x6)) else s.getReg r) := by
  let u:=execInstrBr s (.ADD .x19 .x2 .x6)
  have ok : memoryArgumentsValid s (.ADD .x19 .x2 .x6)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1031<2^40) here capCode1031 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1032 (s : MachineState) (here : s.pc=pc 1032) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1033) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x18=r then (s.getReg .x9) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x18 .x9 0)
  have ok : memoryArgumentsValid s (.ADDI .x18 .x9 0)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1032<2^40) here capCode1032 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1033 (s : MachineState) (here : s.pc=pc 1033) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 759) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x31=r then (pc 1034) else s.getReg r) := by
  simpa using jump_control s 1033 759 .x31 2096056 here (by decide) capCode1033 (by decide +kernel)

theorem atom1153 (s : MachineState) (here : s.pc=pc 1153) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1001) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  simpa using jump_control s 1153 1001 .x0 2096544 here (by decide) capCode1153 (by decide +kernel)

theorem atom1154 (s : MachineState) (here : s.pc=pc 1154) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x17) != 0#64 then pc 364 else pc 1155) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BNE .x17 .x0 5032)
  have ok : memoryArgumentsValid s (.BNE .x17 .x0 5032)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1154<2^40) here capCode1154 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl
theorem atom1155 (s : MachineState) (here : s.pc=pc 1155) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1001) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  simpa using jump_control s 1155 1001 .x0 2096536 here (by decide) capCode1155 (by decide +kernel)

end CommitGolfCandidate.Layout2.Cap
