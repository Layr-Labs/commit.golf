import CommitGolfCandidate.CapBFlow
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.GroupedOpening (openingImage)
set_option maxRecDepth 30000
set_option maxHeartbeats 1100000

/-! One-byte search, opener side (Opus): the length guard at words 12320..12328, reached from the cap stage's return
`jal` at 6671. It computes `a1 = s5 - s4`, drops the final proof byte exactly when the copy destination `x14` is 0
(k % 4 = 0) and the length is 72,160, and HALTs with `a0 = 0`. -/

theorem word12320 : (openingImage.code[12320]?).bind decodeInstruction=some (.base (.SUB .x11 .x21 .x20)) := rfl
theorem word12321 : (openingImage.code[12321]?).bind decodeInstruction=some (.base (.BNE .x14 .x0 20)) := rfl
theorem word12322 : (openingImage.code[12322]?).bind decodeInstruction=some (.base (.LUI .x7 18)) := rfl
theorem word12323 : (openingImage.code[12323]?).bind decodeInstruction=some (.base (.ADDI .x7 .x7 2528)) := rfl
theorem word12324 : (openingImage.code[12324]?).bind decodeInstruction=some (.base (.BNE .x11 .x7 8)) := rfl
theorem word12325 : (openingImage.code[12325]?).bind decodeInstruction=some (.base (.ADDI .x11 .x11 4095)) := rfl
theorem word12326 : (openingImage.code[12326]?).bind decodeInstruction=some (.base (.ADDI .x5 .x0 1)) := rfl
theorem word12327 : (openingImage.code[12327]?).bind decodeInstruction=some (.base (.ADDI .x10 .x0 0)) := rfl
theorem word12328 : (openingImage.code[12328]?).bind decodeInstruction=some (.base .ECALL) := rfl

theorem leaf12320 (s : MachineState) (here : s.pc=pc 12320) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 12321) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x11=r then ((s.getReg .x21)-(s.getReg .x20)) else s.getReg r) := by
  apply assignNav s 12320 (.SUB .x11 .x21 .x20) .x11 (((s.getReg .x21)-(s.getReg .x20))) here (by decide) word12320 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf12321 (s : MachineState) (here : s.pc=pc 12321) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x14) != 0#64 then pc 12326 else pc 12322) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 12321 12326 (.BNE .x14 .x0 20) ((s.getReg .x14) != 0#64) here (by decide) word12321 rfl rfl
  have yes : s.pc+signExtend13 20=pc 12326 := (congrArg (fun a : Word=>a+signExtend13 20) here).trans (by decide +kernel)
  have no : s.pc+4=pc 12322 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 12321)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf12322 (s : MachineState) (here : s.pc=pc 12322) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 12323) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then 73728#64 else s.getReg r) := by
  apply assignNav s 12322 (.LUI .x7 18) .x7 (73728#64) here (by decide) word12322 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf12323 (s : MachineState) (here : s.pc=pc 12323) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 12324) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then ((s.getReg .x7)+(signExtend12 2528)) else s.getReg r) := by
  apply assignNav s 12323 (.ADDI .x7 .x7 2528) .x7 (((s.getReg .x7)+(signExtend12 2528))) here (by decide) word12323 rfl rfl _ (by decide)
  simp only [execInstrBr] <;> rfl

theorem leaf12324 (s : MachineState) (here : s.pc=pc 12324) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x11) != (s.getReg .x7) then pc 12326 else pc 12325) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  apply branchNav s 12324 12326 (.BNE .x11 .x7 8) ((s.getReg .x11) != (s.getReg .x7)) here (by decide) word12324 rfl rfl
  have yes : s.pc+signExtend13 8=pc 12326 := (congrArg (fun a : Word=>a+signExtend13 8) here).trans (by decide +kernel)
  have no : s.pc+4=pc 12325 := (congrArg (fun a : Word=>a+4) here).trans (pc_add 12324)
  simp only [execInstrBr,yes,no ,show s.getReg .x0=0#64 from rfl] <;> split <;> simp_all

theorem leaf12325 (s : MachineState) (here : s.pc=pc 12325) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 12326) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x11=r then ((s.getReg .x11)+(signExtend12 4095)) else s.getReg r) := by
  apply assignNav s 12325 (.ADDI .x11 .x11 4095) .x11 (((s.getReg .x11)+(signExtend12 4095))) here (by decide) word12325 rfl rfl _ (by decide)
  simp only [execInstrBr] <;> rfl

theorem leaf12326 (s : MachineState) (here : s.pc=pc 12326) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 12327) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x5=r then 1#64 else s.getReg r) := by
  apply assignNav s 12326 (.ADDI .x5 .x0 1) .x5 (1#64) here (by decide) word12326 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

theorem leaf12327 (s : MachineState) (here : s.pc=pc 12327) :
    ∃ t,Run openingImage s t 1 1 ∧ t.pc=(pc 12328) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x10=r then 0#64 else s.getReg r) := by
  apply assignNav s 12327 (.ADDI .x10 .x0 0) .x10 (0#64) here (by decide) word12327 rfl rfl _ (by decide)
  simp only [execInstrBr,show signExtend12 0=0#64 from rfl,BitVec.add_zero] <;> rfl

/-- Whether the guard drops the final byte. -/
def dropsByte (s : MachineState) : Prop :=
  s.getReg .x14=0#64 ∧ (s.getReg .x21)-(s.getReg .x20)=72160#64

instance (s : MachineState) : Decidable (dropsByte s) := by unfold dropsByte; infer_instance

/-- Cycles of the guard and its HALT: 9 with the drop, 8 aligned without it, 5 unaligned. -/
def guardCost (s : MachineState) : Nat :=
  if s.getReg .x14 ≠ 0#64 then 5 else if dropsByte s then 9 else 8

theorem guard_cost_le (s : MachineState) : guardCost s ≤ 9 := by
  unfold guardCost; split_ifs <;> omega

private theorem sign2528 : signExtend12 2528=(18446744073709550048#64 : Word) := by decide
private theorem sign4095 : signExtend12 4095=(18446744073709551615#64 : Word) := by decide
private theorem const72160 : (73728#64 : Word)+18446744073709550048#64=72160#64 := by decide
private theorem minus_one (x : Word) : x+18446744073709551615#64=x-1#64 := by rw [BitVec.sub_eq_add_neg];rfl

/-- The guard from word 12320 to the successful HALT: `x11` is the length, less one when the byte is dropped. -/
theorem guard_run (s : MachineState) (here : s.pc=pc 12320) :
    ∃ t,(∀ surplus,execute openingImage (guardCost s+surplus) s true=pure ⟨.success,t,guardCost s,0⟩) ∧
      t.getReg .x11=(if dropsByte s then (s.getReg .x21)-(s.getReg .x20)-1#64 else (s.getReg .x21)-(s.getReg .x20)) ∧
      t.mem=s.mem := by
  obtain ⟨a,ra,pa,ma,rA⟩:=leaf12320 s here
  have halt (u : MachineState) (pcU : u.pc=pc 12328) (x5 : u.getReg .x5=1#64) (x10 : u.getReg .x10=0#64) :
      ∀ surplus,execute openingImage (1+surplus) u true=pure ⟨.success,u,1,0⟩ := by
    have fetch:=wide_image_fetch openingImage u 12328 Instr.ECALL (by decide) pcU (by rfl)
    intro fuel;rw [Nat.add_comm 1,execute,fetch];simp [x5,x10]
  obtain ⟨b,rb,pb,mb,rB⟩:=leaf12321 a pa
  by_cases aligned : s.getReg .x14=0#64
  · have notTaken : (a.getReg .x14 != 0#64)=false := by simp [rA,aligned]
    rw [notTaken] at pb;simp only [Bool.false_eq_true,ite_false] at pb
    obtain ⟨c,rc,pc_,mc,rC⟩:=leaf12322 b pb
    obtain ⟨d,rd,pd,md,rD⟩:=leaf12323 c pc_
    have d7 : d.getReg .x7=72160#64 := by rw [rD, if_pos rfl, rC, if_pos rfl]; decide
    obtain ⟨e,re,pe,me,rE⟩:=leaf12324 d pd
    have d11 : d.getReg .x11=(s.getReg .x21)-(s.getReg .x20) := by simp [rD,rC,rB,rA]
    by_cases long : (s.getReg .x21)-(s.getReg .x20)=72160#64
    · have drop : dropsByte s := ⟨aligned,long⟩
      have equal : (d.getReg .x11 != d.getReg .x7)=false := by simp [d11,d7,long]
      rw [equal] at pe;simp only [Bool.false_eq_true,ite_false] at pe
      obtain ⟨f,rf,pf,mf,rF⟩:=leaf12325 e pe
      obtain ⟨g,rg,pg,mg,rG⟩:=leaf12326 f pf
      obtain ⟨t,rt,pt,mt,rT⟩:=leaf12327 g pg
      have cost : guardCost s=9 := by unfold guardCost;simp [aligned,drop]
      refine ⟨t,?_,?_,?_⟩
      · intro fuel;rw [cost]
        have joint:=((((((((ra.thenDo rb).thenDo rc).thenDo rd).thenDo re).thenDo rf).thenDo rg).thenDo rt))
        rw [show 9+fuel=(1+1+1+1+1+1+1+1)+(1+fuel) by omega,joint,halt t pt (by simp [rT,rG]) (by simp [rT])];rfl
      · rw [if_pos drop];simp [rT,rG,rF,rE,d11,sign4095,minus_one]
        generalize s.getReg .x21 - s.getReg .x20 = x
        rw [BitVec.sub_eq_add_neg]
        congr 1
        all_goals decide
      · rw [mt,mg,mf,me,md,mc,mb,ma]
    · have drop : ¬dropsByte s := fun h=>long h.2
      have differ : (d.getReg .x11 != d.getReg .x7)=true := by simp [d11,d7,long]
      rw [differ] at pe;simp only [ite_true] at pe
      obtain ⟨g,rg,pg,mg,rG⟩:=leaf12326 e pe
      obtain ⟨t,rt,pt,mt,rT⟩:=leaf12327 g pg
      have cost : guardCost s=8 := by unfold guardCost;simp [aligned,drop]
      refine ⟨t,?_,?_,?_⟩
      · intro fuel;rw [cost]
        have joint:=(((((((ra.thenDo rb).thenDo rc).thenDo rd).thenDo re).thenDo rg).thenDo rt))
        rw [show 8+fuel=(1+1+1+1+1+1+1)+(1+fuel) by omega,joint,halt t pt (by simp [rT,rG]) (by simp [rT])];rfl
      · rw [if_neg drop];simp [rT,rG,rE,d11]
      · rw [mt,mg,me,md,mc,mb,ma]
  · have taken : (a.getReg .x14 != 0#64)=true := by simp [rA,aligned]
    rw [taken] at pb;simp only [ite_true] at pb
    obtain ⟨g,rg,pg,mg,rG⟩:=leaf12326 b pb
    obtain ⟨t,rt,pt,mt,rT⟩:=leaf12327 g pg
    have drop : ¬dropsByte s := fun h=>aligned h.1
    have cost : guardCost s=5 := by unfold guardCost;simp [aligned]
    refine ⟨t,?_,?_,?_⟩
    · intro fuel;rw [cost]
      have joint:=(((ra.thenDo rb).thenDo rg).thenDo rt)
      rw [show 5+fuel=(1+1+1+1)+(1+fuel) by omega,joint,halt t pt (by simp [rT,rG]) (by simp [rT])];rfl
    · rw [if_neg drop];simp [rT,rG,rB,rA]
    · rw [mt,mg,mb,ma]

end CommitGolfCandidate.CapB
