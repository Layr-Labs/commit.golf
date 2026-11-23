import CommitGolfCandidate.CapBNavStep
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening (openingImage)
set_option maxRecDepth 12000
set_option maxHeartbeats 900000
theorem leaf661 (s : MachineState) (here : s.pc=pc 661) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 662) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x16=r then ((s.getReg .x6) <<< (3:Nat)) else s.getReg r) := by
  apply assignNav s 661 (.SLLI .x16 .x6 3) .x16 (((s.getReg .x6) <<< (3:Nat))) here (by decide) word661 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf662 (s : MachineState) (here : s.pc=pc 662) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 663) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then ((s.getReg .x26)+(s.getReg .x16)) else s.getReg r) := by
  apply assignNav s 662 (.ADD .x7 .x26 .x16) .x7 (((s.getReg .x26)+(s.getReg .x16))) here (by decide) word662 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf663 (s : MachineState) (here : s.pc=pc 663) (valid : accessValid (s.getReg .x7) 8=true) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 664) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x28=r then (s.getMem (s.getReg .x7)) else s.getReg r) := by
  have ok : ordinaryStep s (.base (.LD .x28 .x7 0))=some (execInstrBr s (.LD .x28 .x7 0)) := by
    have a : memoryArgumentsValid s (.LD .x28 .x7 0)=true := by simpa [memoryArgumentsValid,memAccess,signExtend12] using valid
    simp only [ordinaryStep,a,ite_true]
  apply assignNav s 663 (.LD .x28 .x7 0) .x28 ((s.getMem (s.getReg .x7))) here (by decide) word663 ok rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf664 (s : MachineState) (here : s.pc=pc 664) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x28) == 0#64 then pc 702 else pc 665) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 664 702 (.BEQ .x28 .x0 152) ((s.getReg .x28) == 0#64) here (by decide) word664 rfl rfl
  have yes : s.pc+signExtend13 152=pc 702 := (congrArg (fun a : Word=>a+signExtend13 152) here).trans (by decide +kernel)
  have no : s.pc+4=pc 665 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 664)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf665 (s : MachineState) (here : s.pc=pc 665) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if !(BitVec.ult (s.getReg .x16) (s.getReg .x27)) then pc 708 else pc 666) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 665 708 (.BGEU .x16 .x27 172) (!(BitVec.ult (s.getReg .x16) (s.getReg .x27))) here (by decide) word665 rfl rfl
  have yes : s.pc+signExtend13 172=pc 708 := (congrArg (fun a : Word=>a+signExtend13 172) here).trans (by decide +kernel)
  have no : s.pc+4=pc 666 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 665)
  simp only [execInstrBr,yes,no,Bool.not_eq_true',Bool.eq_false_iff ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf666 (s : MachineState) (here : s.pc=pc 666) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 667) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6) <<< (1:Nat)) else s.getReg r) := by
  apply assignNav s 666 (.SLLI .x6 .x6 1) .x6 (((s.getReg .x6) <<< (1:Nat))) here (by decide) word666 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf667 (s : MachineState) (here : s.pc=pc 667) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 661) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply jumpNav s 667 (.JAL .x0 2097128) (pc 661) here (by decide) word667 rfl rfl
  have eq : s.pc+signExtend21 2097128=pc 661 := (congrArg (fun v : Word=>v+signExtend21 2097128) here).trans (by decide +kernel)
  change s.setPC _=s.setPC _;rw [eq]

theorem leaf708 (s : MachineState) (here : s.pc=pc 708) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 8192) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply jumpNav s 708 (.JAL .x0 29936) (pc 8192) here (by decide) word708 rfl rfl
  have eq : s.pc+signExtend21 29936=pc 8192 := (congrArg (fun v : Word=>v+signExtend21 29936) here).trans (by decide +kernel)
  change s.setPC _=s.setPC _;rw [eq]

theorem leaf8192 (s : MachineState) (here : s.pc=pc 8192) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 8193) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x28=r then ((s.getReg .x28) <<< (6:Nat)) else s.getReg r) := by
  apply assignNav s 8192 (.SLLI .x28 .x28 6) .x28 (((s.getReg .x28) <<< (6:Nat))) here (by decide) word8192 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf8193 (s : MachineState) (here : s.pc=pc 8193) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 8194) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x11=r then 36864#64 else s.getReg r) := by
  apply assignNav s 8193 (.LUI .x11 9) .x11 (36864#64) here (by decide) word8193 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf8194 (s : MachineState) (here : s.pc=pc 8194) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 8195) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x11=r then ((s.getReg .x11)+(s.getReg .x28)) else s.getReg r) := by
  apply assignNav s 8194 (.ADD .x11 .x11 .x28) .x11 (((s.getReg .x11)+(s.getReg .x28))) here (by decide) word8194 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf8195 (s : MachineState) (here : s.pc=pc 8195) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(((s.getReg .x11)+128#64) &&& ~~~1#64) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply jumpNav s 8195 (.JALR .x0 .x11 128) _ here (by decide) word8195 rfl rfl
  simp [execInstrBr,signExtend12,MachineState.setReg]

theorem leaf703 (s : MachineState) (here : s.pc=pc 703) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 704) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then ((s.getReg .x6) &&& 1#64) else s.getReg r) := by
  apply assignNav s 703 (.ANDI .x7 .x6 1) .x7 (((s.getReg .x6) &&& 1#64)) here (by decide) word703 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf704 (s : MachineState) (here : s.pc=pc 704) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x7) == 0#64 then pc 660 else pc 705) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 704 660 (.BEQ .x7 .x0 8016) ((s.getReg .x7) == 0#64) here (by decide) word704 rfl rfl
  have yes : s.pc+signExtend13 8016=pc 660 := (congrArg (fun a : Word=>a+signExtend13 8016) here).trans (by decide +kernel)
  have no : s.pc+4=pc 705 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 704)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf660 (s : MachineState) (here : s.pc=pc 660) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 661) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6)+1#64) else s.getReg r) := by
  apply assignNav s 660 (.ADDI .x6 .x6 1) .x6 (((s.getReg .x6)+1#64)) here (by decide) word660 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf705 (s : MachineState) (here : s.pc=pc 705) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 706) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6) >>> (1:Nat)) else s.getReg r) := by
  apply assignNav s 705 (.SRLI .x6 .x6 1) .x6 (((s.getReg .x6) >>> (1:Nat))) here (by decide) word705 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf706 (s : MachineState) (here : s.pc=pc 706) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x6) != (s.getReg .x23) then pc 703 else pc 707) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 706 703 (.BNE .x6 .x23 8180) ((s.getReg .x6) != (s.getReg .x23)) here (by decide) word706 rfl rfl
  have yes : s.pc+signExtend13 8180=pc 703 := (congrArg (fun a : Word=>a+signExtend13 8180) here).trans (by decide +kernel)
  have no : s.pc+4=pc 707 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 706)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf707 (s : MachineState) (here : s.pc=pc 707) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6656) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply jumpNav s 707 (.JAL .x0 23796) (pc 6656) here (by decide) word707 rfl rfl
  have eq : s.pc+signExtend21 23796=pc 6656 := (congrArg (fun v : Word=>v+signExtend21 23796) here).trans (by decide +kernel)
  change s.setPC _=s.setPC _;rw [eq]

theorem leaf7155 (s : MachineState) (here : s.pc=pc 7155) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 7156) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then 1#64 else s.getReg r) := by
  apply assignNav s 7155 (.ADDI .x6 .x0 1) .x6 (1#64) here (by decide) word7155 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf7156 (s : MachineState) (here : s.pc=pc 7156) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 7157) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x19=r then 28672#64 else s.getReg r) := by
  apply assignNav s 7156 (.LUI .x19 7) .x19 (28672#64) here (by decide) word7156 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf7157 (s : MachineState) (here : s.pc=pc 7157) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 7158) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x24=r then (s.getReg .x19) else s.getReg r) := by
  apply assignNav s 7157 (.ADDI .x24 .x19 0) .x24 ((s.getReg .x19)) here (by decide) word7157 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf7158 (s : MachineState) (here : s.pc=pc 7158) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 7159) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x14=r then ((s.getReg .x21) &&& 7#64) else s.getReg r) := by
  apply assignNav s 7158 (.ANDI .x14 .x21 7) .x14 (((s.getReg .x21) &&& 7#64)) here (by decide) word7158 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf7159 (s : MachineState) (here : s.pc=pc 7159) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x14) == 0#64 then pc 7162 else pc 7160) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 7159 7162 (.BEQ .x14 .x0 12) ((s.getReg .x14) == 0#64) here (by decide) word7159 rfl rfl
  have yes : s.pc+signExtend13 12=pc 7162 := (congrArg (fun a : Word=>a+signExtend13 12) here).trans (by decide +kernel)
  have no : s.pc+4=pc 7160 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 7159)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf7160 (s : MachineState) (here : s.pc=pc 7160) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 7161) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x14=r then (s.getReg .x21) else s.getReg r) := by
  apply assignNav s 7160 (.ADDI .x14 .x21 0) .x14 ((s.getReg .x21)) here (by decide) word7160 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf7161 (s : MachineState) (here : s.pc=pc 7161) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 7162) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x21=r then 12288#64 else s.getReg r) := by
  apply assignNav s 7161 (.LUI .x21 3) .x21 (12288#64) here (by decide) word7161 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf7162 (s : MachineState) (here : s.pc=pc 7162) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 661) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply jumpNav s 7162 (.JAL .x0 2071148) (pc 661) here (by decide) word7162 rfl rfl
  have eq : s.pc+signExtend21 2071148=pc 661 := (congrArg (fun v : Word=>v+signExtend21 2071148) here).trans (by decide +kernel)
  change s.setPC _=s.setPC _;rw [eq]

theorem leaf6656 (s : MachineState) (here : s.pc=pc 6656) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x19) == (s.getReg .x24) then pc 6662 else pc 6657) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 6656 6662 (.BEQ .x19 .x24 24) ((s.getReg .x19) == (s.getReg .x24)) here (by decide) word6656 rfl rfl
  have yes : s.pc+signExtend13 24=pc 6662 := (congrArg (fun a : Word=>a+signExtend13 24) here).trans (by decide +kernel)
  have no : s.pc+4=pc 6657 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 6656)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf6657 (s : MachineState) (here : s.pc=pc 6657) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6658) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x19)-(s.getReg .x24)) else s.getReg r) := by
  apply assignNav s 6657 (.SUB .x6 .x19 .x24) .x6 (((s.getReg .x19)-(s.getReg .x24))) here (by decide) word6657 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6658 (s : MachineState) (here : s.pc=pc 6658) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6659) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6) >>> (1:Nat)) else s.getReg r) := by
  apply assignNav s 6658 (.SRLI .x6 .x6 1) .x6 (((s.getReg .x6) >>> (1:Nat))) here (by decide) word6658 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6659 (s : MachineState) (here : s.pc=pc 6659) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6660) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then 32768#64 else s.getReg r) := by
  apply assignNav s 6659 (.LUI .x7 8) .x7 (32768#64) here (by decide) word6659 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6660 (s : MachineState) (here : s.pc=pc 6660) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6661) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then ((s.getReg .x7)+(s.getReg .x6)) else s.getReg r) := by
  apply assignNav s 6660 (.ADD .x7 .x7 .x6) .x7 (((s.getReg .x7)+(s.getReg .x6))) here (by decide) word6660 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6661 (s : MachineState) (here : s.pc=pc 6661) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(((s.getReg .x7)+(signExtend12 2144)) &&& ~~~1#64) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply jumpNav s 6661 (.JALR .x0 .x7 2144) _ here (by decide) word6661 rfl rfl
  simp [execInstrBr,signExtend12,MachineState.setReg]

theorem leaf6662 (s : MachineState) (here : s.pc=pc 6662) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x14) == 0#64 then pc 6671 else pc 6663) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 6662 6671 (.BEQ .x14 .x0 36) ((s.getReg .x14) == 0#64) here (by decide) word6662 rfl rfl
  have yes : s.pc+signExtend13 36=pc 6671 := (congrArg (fun a : Word=>a+signExtend13 36) here).trans (by decide +kernel)
  have no : s.pc+4=pc 6663 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 6662)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf6663 (s : MachineState) (here : s.pc=pc 6663) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6664) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then 12288#64 else s.getReg r) := by
  apply assignNav s 6663 (.LUI .x6 3) .x6 (12288#64) here (by decide) word6663 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6664 (s : MachineState) (here : s.pc=pc 6664) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x6) == (s.getReg .x21) then pc 6670 else pc 6665) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 6664 6670 (.BEQ .x6 .x21 24) ((s.getReg .x6) == (s.getReg .x21)) here (by decide) word6664 rfl rfl
  have yes : s.pc+signExtend13 24=pc 6670 := (congrArg (fun a : Word=>a+signExtend13 24) here).trans (by decide +kernel)
  have no : s.pc+4=pc 6665 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 6664)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf6665 (s : MachineState) (here : s.pc=pc 6665) (valid : accessValid (s.getReg .x6) 1=true) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6666) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then ((s.getByte (s.getReg .x6)).zeroExtend 64) else s.getReg r) := by
  have ok : ordinaryStep s (.base (.LBU .x7 .x6 0))=some (execInstrBr s (.LBU .x7 .x6 0)) := by
    have a : memoryArgumentsValid s (.LBU .x7 .x6 0)=true := by simpa [memoryArgumentsValid,memAccess,signExtend12] using valid
    simp only [ordinaryStep,a,ite_true]
  apply assignNav s 6665 (.LBU .x7 .x6 0) .x7 (((s.getByte (s.getReg .x6)).zeroExtend 64)) here (by decide) word6665 ok rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6666 (s : MachineState) (here : s.pc=pc 6666) (valid : accessValid (s.getReg .x14) 1=true) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6667) ∧ t.mem=(s.setByte (s.getReg .x14) ((s.getReg .x7).truncate 8)).mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  have ok : ordinaryStep s (.base (.SB .x14 .x7 0))=some (execInstrBr s (.SB .x14 .x7 0)) := by
    have a : memoryArgumentsValid s (.SB .x14 .x7 0)=true := by simpa [memoryArgumentsValid,memAccess,signExtend12] using valid
    simp only [ordinaryStep,a,ite_true]
  let t:=execInstrBr s (.SB .x14 .x7 0);exact ⟨t,one (by decide : 6666<2^40) here word6666 ok,(congrArg (fun v : Word=>v+4) here).trans (pc_add 6666),by simp [t,execInstrBr,signExtend12,MachineState.setPC],by intro r;cases r <;> rfl⟩

theorem leaf6667 (s : MachineState) (here : s.pc=pc 6667) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6668) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6)+1#64) else s.getReg r) := by
  apply assignNav s 6667 (.ADDI .x6 .x6 1) .x6 (((s.getReg .x6)+1#64)) here (by decide) word6667 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6668 (s : MachineState) (here : s.pc=pc 6668) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6669) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x14=r then ((s.getReg .x14)+1#64) else s.getReg r) := by
  apply assignNav s 6668 (.ADDI .x14 .x14 1) .x14 (((s.getReg .x14)+1#64)) here (by decide) word6668 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6669 (s : MachineState) (here : s.pc=pc 6669) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x6) != (s.getReg .x21) then pc 6665 else pc 6670) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 6669 6665 (.BNE .x6 .x21 8176) ((s.getReg .x6) != (s.getReg .x21)) here (by decide) word6669 rfl rfl
  have yes : s.pc+signExtend13 8176=pc 6665 := (congrArg (fun a : Word=>a+signExtend13 8176) here).trans (by decide +kernel)
  have no : s.pc+4=pc 6670 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 6669)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf6670 (s : MachineState) (here : s.pc=pc 6670) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 6671) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x21=r then (s.getReg .x14) else s.getReg r) := by
  apply assignNav s 6670 (.ADDI .x21 .x14 0) .x21 ((s.getReg .x14)) here (by decide) word6670 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf6671 (s : MachineState) (here : s.pc=pc 6671) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 12320) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply jumpNav s 6671 (.JAL .x0 22596) (pc 12320) here (by decide) word6671 rfl rfl
  have eq : s.pc+signExtend21 22596=pc 12320 := (congrArg (fun v : Word=>v+signExtend21 22596) here).trans (by decide +kernel)
  change s.setPC _=s.setPC _;rw [eq]

theorem leaf709 (s : MachineState) (here : s.pc=pc 709) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 710) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x11=r then ((s.getReg .x21)-(s.getReg .x20)) else s.getReg r) := by
  apply assignNav s 709 (.SUB .x11 .x21 .x20) .x11 (((s.getReg .x21)-(s.getReg .x20))) here (by decide) word709 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf710 (s : MachineState) (here : s.pc=pc 710) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 711) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x5=r then 1#64 else s.getReg r) := by
  apply assignNav s 710 (.ADDI .x5 .x0 1) .x5 (1#64) here (by decide) word710 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf711 (s : MachineState) (here : s.pc=pc 711) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 712) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x10=r then 0#64 else s.getReg r) := by
  apply assignNav s 711 (.ADDI .x10 .x0 0) .x10 (0#64) here (by decide) word711 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

end CommitGolfCandidate.CapB
