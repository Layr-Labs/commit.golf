import CommitGolfCandidate.Layout2QuartetCode
import CommitGolfCandidate.Layout2Views

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Opening (getReg_setReg)
set_option maxRecDepth 8000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
attribute [local simp] zero mem_pc pc_pc mem_reg pc_ite reg_ite mem_ite
attribute [local irreducible] execute checkImage
private theorem jump (s : MachineState) (w toWord : Nat) (off : BitVec 21)
    (small : w<2^40) (here : s.pc=pc w) (code : (checkImage.code[w]?).bind decodeInstruction=some (.base (.JAL .x0 off)))
    (target : pc w+signExtend21 off=pc toWord) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=pc toWord ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=s.getReg r := by
  let t:=execInstrBr s (.JAL .x0 off)
  refine ⟨t,run_control _ _ _ _ _ small here code rfl rfl,?_,?_,?_⟩
  · change s.pc+signExtend21 off=pc toWord;exact (congrArg (fun a : Word=>a+signExtend21 off) here).trans target
  · rfl
  · intro r;rfl

theorem atom998 (s : MachineState) (here : s.pc=pc 998) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 999) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then (s.getReg .x19) + signExtend12 1 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x19 .x19 1)
  have ok : memoryArgumentsValid s (.ADDI .x19 .x19 1)=true := by rfl
  refine ⟨u,run_control checkImage s 998 (.ADDI .x19 .x19 1) 1 (by decide) here code998 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom999 (s : MachineState) (here : s.pc=pc 999) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 1000) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then (s.getReg .x19) &&& signExtend12 3 else s.getReg r) := by
  let u:=execInstrBr s (.ANDI .x19 .x19 3)
  have ok : memoryArgumentsValid s (.ANDI .x19 .x19 3)=true := by rfl
  refine ⟨u,run_control checkImage s 999 (.ANDI .x19 .x19 3) 1 (by decide) here code999 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

private theorem jump1000 : pc 1000+signExtend21 2096332=pc 795 := by decide +kernel
theorem atom1000 (s : MachineState) (here : s.pc=pc 1000) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 795) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  exact jump s 1000 795 2096332 (by decide) here code1000 (by decide +kernel)

theorem atom997 (s : MachineState) (here : s.pc=pc 997) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 998) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x8=r then (s.getReg .x8) + signExtend12 4088 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x8 .x8 4088)
  have ok : memoryArgumentsValid s (.ADDI .x8 .x8 4088)=true := by rfl
  refine ⟨u,run_control checkImage s 997 (.ADDI .x8 .x8 4088) 1 (by decide) here code997 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom800 (s : MachineState) (here : s.pc=pc 800) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 801) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then (s.getReg .x5) + signExtend12 4095 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x5 .x5 4095)
  have ok : memoryArgumentsValid s (.ADDI .x5 .x5 4095)=true := by rfl
  refine ⟨u,run_control checkImage s 800 (.ADDI .x5 .x5 4095) 1 (by decide) here code800 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom801 (s : MachineState) (here : s.pc=pc 801) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x5) == 0#64 then pc 898 else pc 802) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BEQ .x5 .x0 388)
  have ok : memoryArgumentsValid s (.BEQ .x5 .x0 388)=true := by rfl
  refine ⟨u,run_control checkImage s 801 (.BEQ .x5 .x0 388) 1 (by decide) here code801 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom944 (s : MachineState) (here : s.pc=pc 944) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 992) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  exact jump s 944 992 192 (by decide) here code944 (by decide +kernel)

theorem atom992 (s : MachineState) (here : s.pc=pc 992) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 993) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x18=r then (s.getReg .x18) + signExtend12 4095 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x18 .x18 4095)
  have ok : memoryArgumentsValid s (.ADDI .x18 .x18 4095)=true := by rfl
  refine ⟨u,run_control checkImage s 992 (.ADDI .x18 .x18 4095) 1 (by decide) here code992 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom993 (s : MachineState) (here : s.pc=pc 993) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x18) == 0#64 then pc 786 else pc 994) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BEQ .x18 .x0 7364)
  have ok : memoryArgumentsValid s (.BEQ .x18 .x0 7364)=true := by rfl
  refine ⟨u,run_control checkImage s 993 (.BEQ .x18 .x0 7364) 1 (by decide) here code993 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom802 (s : MachineState) (here : s.pc=pc 802) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 803) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then (s.getReg .x5) + signExtend12 4095 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x5 .x5 4095)
  have ok : memoryArgumentsValid s (.ADDI .x5 .x5 4095)=true := by rfl
  refine ⟨u,run_control checkImage s 802 (.ADDI .x5 .x5 4095) 1 (by decide) here code802 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom803 (s : MachineState) (here : s.pc=pc 803) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 945) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  exact jump s 803 945 568 (by decide) here code803 (by decide +kernel)

theorem atom991 (s : MachineState) (here : s.pc=pc 991) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 992) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  exact jump s 991 992 4 (by decide) here code991 (by decide +kernel)

theorem atom795 (s : MachineState) (here : s.pc=pc 795) (valid : accessValid (s.getReg .x9) 8=true) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 796) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then s.getMem (s.getReg .x9) else s.getReg r) := by
  let u:=execInstrBr s (.LD .x5 .x9 0)
  have ok : memoryArgumentsValid s (.LD .x5 .x9 0)=true := by simpa [memoryArgumentsValid,memAccess,signExtend12] using valid
  refine ⟨u,run_control checkImage s 795 (.LD .x5 .x9 0) 1 (by decide) here code795 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,signExtend12] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,signExtend12] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,signExtend12] <;> try rfl

theorem atom796 (s : MachineState) (here : s.pc=pc 796) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 797) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then (s.getReg .x5) &&& signExtend12 3 else s.getReg r) := by
  let u:=execInstrBr s (.ANDI .x5 .x5 3)
  have ok : memoryArgumentsValid s (.ANDI .x5 .x5 3)=true := by rfl
  refine ⟨u,run_control checkImage s 796 (.ANDI .x5 .x5 3) 1 (by decide) here code796 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom797 (s : MachineState) (here : s.pc=pc 797) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x5) == 0#64 then pc 804 else pc 798) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BEQ .x5 .x0 28)
  have ok : memoryArgumentsValid s (.BEQ .x5 .x0 28)=true := by rfl
  refine ⟨u,run_control checkImage s 797 (.BEQ .x5 .x0 28) 1 (by decide) here code797 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom994 (s : MachineState) (here : s.pc=pc 994) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 995) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x9=r then (s.getReg .x9) + signExtend12 8 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x9 .x9 8)
  have ok : memoryArgumentsValid s (.ADDI .x9 .x9 8)=true := by rfl
  refine ⟨u,run_control checkImage s 994 (.ADDI .x9 .x9 8) 1 (by decide) here code994 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom995 (s : MachineState) (here : s.pc=pc 995) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 996) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x8=r then (s.getReg .x8) + signExtend12 536 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x8 .x8 536)
  have ok : memoryArgumentsValid s (.ADDI .x8 .x8 536)=true := by rfl
  refine ⟨u,run_control checkImage s 995 (.ADDI .x8 .x8 536) 1 (by decide) here code995 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom996 (s : MachineState) (here : s.pc=pc 996) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x19) != 0#64 then pc 998 else pc 997) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BNE .x19 .x0 8)
  have ok : memoryArgumentsValid s (.BNE .x19 .x0 8)=true := by rfl
  refine ⟨u,run_control checkImage s 996 (.BNE .x19 .x0 8) 1 (by decide) here code996 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom798 (s : MachineState) (here : s.pc=pc 798) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 799) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x5=r then (s.getReg .x5) + signExtend12 4095 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x5 .x5 4095)
  have ok : memoryArgumentsValid s (.ADDI .x5 .x5 4095)=true := by rfl
  refine ⟨u,run_control checkImage s 798 (.ADDI .x5 .x5 4095) 1 (by decide) here code798 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom799 (s : MachineState) (here : s.pc=pc 799) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x5) == 0#64 then pc 851 else pc 800) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BEQ .x5 .x0 208)
  have ok : memoryArgumentsValid s (.BEQ .x5 .x0 208)=true := by rfl
  refine ⟨u,run_control checkImage s 799 (.BEQ .x5 .x0 208) 1 (by decide) here code799 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom897 (s : MachineState) (here : s.pc=pc 897) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 992) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  exact jump s 897 992 380 (by decide) here code897 (by decide +kernel)

theorem atom850 (s : MachineState) (here : s.pc=pc 850) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 992) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  exact jump s 850 992 568 (by decide) here code850 (by decide +kernel)

theorem atom0 (s : MachineState) (here : s.pc=pc 1001) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 787) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  exact jump s 1001 787 2096296 (by decide) here code0 (by decide +kernel)

theorem atom787 (s : MachineState) (here : s.pc=pc 787) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 788) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then 0#64 + signExtend12 534 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x6 .x0 534)
  have ok : memoryArgumentsValid s (.ADDI .x6 .x0 534)=true := by rfl
  refine ⟨u,run_control checkImage s 787 (.ADDI .x6 .x0 534) 1 (by decide) here code787 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom788 (s : MachineState) (here : s.pc=pc 788) :
    ∃ u, Runs checkImage s u 1 4 ∧ u.pc=(pc 789) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then (s.getReg .x16) * (s.getReg .x6) else s.getReg r) := by
  let u:=execInstrBr s (.MUL .x6 .x16 .x6)
  have ok : memoryArgumentsValid s (.MUL .x6 .x16 .x6)=true := by rfl
  refine ⟨u,run_control checkImage s 788 (.MUL .x6 .x16 .x6) 4 (by decide) here code788 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom789 (s : MachineState) (here : s.pc=pc 789) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if BitVec.ult (s.getReg .x17) (s.getReg .x6) then pc 364 else pc 790) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BLTU .x17 .x6 6492)
  have ok : memoryArgumentsValid s (.BLTU .x17 .x6 6492)=true := by rfl
  refine ⟨u,run_control checkImage s 789 (.BLTU .x17 .x6 6492) 1 (by decide) here code789 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom790 (s : MachineState) (here : s.pc=pc 790) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x16) == 0#64 then pc 786 else pc 791) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(s.getReg r) := by
  let u:=execInstrBr s (.BEQ .x16 .x0 8176)
  have ok : memoryArgumentsValid s (.BEQ .x16 .x0 8176)=true := by rfl
  refine ⟨u,run_control checkImage s 790 (.BEQ .x16 .x0 8176) 1 (by decide) here code790 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom791 (s : MachineState) (here : s.pc=pc 791) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 792) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x8=r then (s.getReg .x15) + signExtend12 0 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x8 .x15 0)
  have ok : memoryArgumentsValid s (.ADDI .x8 .x15 0)=true := by rfl
  refine ⟨u,run_control checkImage s 791 (.ADDI .x8 .x15 0) 1 (by decide) here code791 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom792 (s : MachineState) (here : s.pc=pc 792) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 793) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x9=r then (s.getReg .x13) + signExtend12 0 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x9 .x13 0)
  have ok : memoryArgumentsValid s (.ADDI .x9 .x13 0)=true := by rfl
  refine ⟨u,run_control checkImage s 792 (.ADDI .x9 .x13 0) 1 (by decide) here code792 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom793 (s : MachineState) (here : s.pc=pc 793) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 794) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x18=r then (s.getReg .x16) + signExtend12 0 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x18 .x16 0)
  have ok : memoryArgumentsValid s (.ADDI .x18 .x16 0)=true := by rfl
  refine ⟨u,run_control checkImage s 793 (.ADDI .x18 .x16 0) 1 (by decide) here code793 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

theorem atom794 (s : MachineState) (here : s.pc=pc 794) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(pc 795) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x19=r then 0#64 + signExtend12 0 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x19 .x0 0)
  have ok : memoryArgumentsValid s (.ADDI .x19 .x0 0)=true := by rfl
  refine ⟨u,run_control checkImage s 794 (.ADDI .x19 .x0 0) 1 (by decide) here code794 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc,imm12_0] <;> try rfl

end CommitGolfCandidate.Layout2.Quartet
