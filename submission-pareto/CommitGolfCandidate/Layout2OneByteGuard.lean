import CommitGolfCandidate.Layout2CapControl
import CommitGolfCandidate.Layout2QuartetInput
import CommitGolfCandidate.Layout2CapInput

/-! One-byte search, checker entry (Opus). Word 0 jumps to the guard at 1156..1162: when k = 128 (`a6`) and the
proof length (`a7`) is 72,159, the guard sets `a7 = 72160`, so the checker reads the proof as 72,160 bytes whose final
byte is the zeroed buffer's 0; then it continues at V2b's entry 1002. `effective i` is the input the rest of the
checker sees, and its initial memory is `i`'s (`initial_mem_effective`). -/
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Layout2.Quartet (checkImage run_control)
open TwoPermutationPrototype.Opening (getReg_setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 1300000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem guardCode0 : (checkImage.code[0]?).bind decodeInstruction=some (.base (.JAL .x0 4624)) := rfl
theorem guardCode1156 : (checkImage.code[1156]?).bind decodeInstruction=some (.base (.ADDI .x6 .x0 128)) := rfl
theorem guardCode1157 : (checkImage.code[1157]?).bind decodeInstruction=some (.base (.BNE .x16 .x6 20)) := rfl
theorem guardCode1158 : (checkImage.code[1158]?).bind decodeInstruction=some (.base (.LUI .x7 18)) := rfl
theorem guardCode1159 : (checkImage.code[1159]?).bind decodeInstruction=some (.base (.ADDI .x7 .x7 2527)) := rfl
theorem guardCode1160 : (checkImage.code[1160]?).bind decodeInstruction=some (.base (.BNE .x17 .x7 8)) := rfl
theorem guardCode1161 : (checkImage.code[1161]?).bind decodeInstruction=some (.base (.ADDI .x17 .x17 1)) := rfl
theorem guardCode1162 : (checkImage.code[1162]?).bind decodeInstruction=some (.base (.JAL .x0 2096512)) := rfl

attribute [local simp] zero mem_pc pc_pc mem_reg pc_ite reg_ite mem_ite
attribute [local irreducible] execute checkImage

private theorem gjump (s : MachineState) (w d : Nat) (rd : Reg) (off : BitVec 21)
    (here : s.pc=pc w) (valid : w<2^40) (code : (checkImage.code[w]?).bind decodeInstruction=some (.base (.JAL rd off)))
    (delta : pc w+signExtend21 off=pc d) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc d ∧ u.mem=s.mem ∧
      ∀ r,u.getReg r=(if rd=r ∧ rd≠.x0 then pc (w+1) else s.getReg r) := by
  let u:=execInstrBr s (.JAL rd off)
  refine ⟨u,run_control _ _ _ _ _ valid here code rfl rfl,?_,?_,?_⟩
  · change s.pc+signExtend21 off=pc d;rw [here];exact delta
  · simp only [u,execInstrBr,mem_pc,mem_reg]
  · intro r;simp only [u,execInstrBr,MachineState.getReg_setPC,getReg_setReg,here,pc_next]

theorem gatom0 (s : MachineState) (here : s.pc=pc 0) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc 1156 ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=s.getReg r := by
  simpa using gjump s 0 1156 .x0 4624 here (by decide) guardCode0 (by decide +kernel)

theorem gatom1156 (s : MachineState) (here : s.pc=pc 1156) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc 1157 ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x6=r then 128#64 else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x6 .x0 128)
  have ok : memoryArgumentsValid s (.ADDI .x6 .x0 128)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1156<2^40) here guardCode1156 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl

theorem gatom1157 (s : MachineState) (here : s.pc=pc 1157) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x16) != (s.getReg .x6) then pc 1162 else pc 1158) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=s.getReg r := by
  let u:=execInstrBr s (.BNE .x16 .x6 20)
  have ok : memoryArgumentsValid s (.BNE .x16 .x6 20)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1157<2^40) here guardCode1157 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl

theorem gatom1158 (s : MachineState) (here : s.pc=pc 1158) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc 1159 ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x7=r then 73728#64 else s.getReg r) := by
  let u:=execInstrBr s (.LUI .x7 18)
  have ok : memoryArgumentsValid s (.LUI .x7 18)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1158<2^40) here guardCode1158 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl

theorem gatom1159 (s : MachineState) (here : s.pc=pc 1159) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc 1160 ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x7=r then ((s.getReg .x7)+signExtend12 2527) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x7 .x7 2527)
  have ok : memoryArgumentsValid s (.ADDI .x7 .x7 2527)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1159<2^40) here guardCode1159 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,here,pc] <;> rfl

theorem gatom1160 (s : MachineState) (here : s.pc=pc 1160) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=(if (s.getReg .x17) != (s.getReg .x7) then pc 1162 else pc 1161) ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=s.getReg r := by
  let u:=execInstrBr s (.BNE .x17 .x7 8)
  have ok : memoryArgumentsValid s (.BNE .x17 .x7 8)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1160<2^40) here guardCode1160 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl

theorem gatom1161 (s : MachineState) (here : s.pc=pc 1161) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc 1162 ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=(if .x17=r then ((s.getReg .x17)+1#64) else s.getReg r) := by
  let u:=execInstrBr s (.ADDI .x17 .x17 1)
  have ok : memoryArgumentsValid s (.ADDI .x17 .x17 1)=true := by rfl
  refine ⟨u,run_control _ _ _ _ _ (by decide : 1161<2^40) here guardCode1161 (by simp only [ordinaryStep,ok,ite_true]) rfl,?_,?_,?_⟩
  · simp [u,execInstrBr,here,pc,signExtend13] <;> rfl
  · simp [u,execInstrBr] <;> rfl
  · intro r;simp [u,execInstrBr,getReg_setReg,signExtend12,here,pc] <;> rfl

theorem gatom1162 (s : MachineState) (here : s.pc=pc 1162) :
    ∃ u, Runs checkImage s u 1 1 ∧ u.pc=pc 1002 ∧ u.mem=s.mem ∧ ∀ r,u.getReg r=s.getReg r := by
  simpa using gjump s 1162 1002 .x0 2096512 here (by decide) guardCode1162 (by decide +kernel)

/-- Whether the entry guard extends the length: k = 128 and length 72,159. -/
def guardFires (s : MachineState) : Prop := s.getReg .x16=128#64 ∧ s.getReg .x17=72159#64
instance (s : MachineState) : Decidable (guardFires s) := by unfold guardFires; infer_instance

private theorem const72159 : (73728#64 : Word)+signExtend12 2527=72159#64 := by decide

/-- From word 0 to V2b's entry 1002: memory unchanged, `x6`/`x7` clobbered, `x17` incremented exactly when the
guard fires. -/
theorem entry_guard (s : MachineState) (here : s.pc=pc 0) :
    ∃ t h c, Runs checkImage s t h c ∧ h≤8 ∧ c≤8 ∧ t.pc=pc 1002 ∧ t.mem=s.mem ∧
      (∀ r,r≠.x6 → r≠.x7 → r≠.x17 → t.getReg r=s.getReg r) ∧
      t.getReg .x17=(if guardFires s then 72160#64 else s.getReg .x17) := by
  obtain ⟨a,ra,pa,ma,rA⟩:=gatom0 s here
  obtain ⟨b,rb,pb,mb,rB⟩:=gatom1156 a pa
  obtain ⟨c,rc,pc_,mc,rC⟩:=gatom1157 b pb
  by_cases k : s.getReg .x16=128#64
  · have nt : (b.getReg .x16 != b.getReg .x6)=false := by simp [rB,rA,k]
    rw [nt] at pc_;simp only [Bool.false_eq_true,ite_false] at pc_
    obtain ⟨d,rd,pd,md,rD⟩:=gatom1158 c pc_
    obtain ⟨e,re,pe,me,rE⟩:=gatom1159 d pd
    have e7 : e.getReg .x7=72159#64 := by simp [rE,rD]; decide
    obtain ⟨f,rf,pf,mf,rF⟩:=gatom1160 e pe
    have e17 : e.getReg .x17=s.getReg .x17 := by simp [rE,rD,rC,rB,rA]
    by_cases len : s.getReg .x17=72159#64
    · have fires : guardFires s := ⟨k,len⟩
      have eq : (e.getReg .x17 != e.getReg .x7)=false := by simp [e17,e7,len]
      rw [eq] at pf;simp only [Bool.false_eq_true,ite_false] at pf
      obtain ⟨g,rg,pg,mg,rG⟩:=gatom1161 f pf
      obtain ⟨t,rt,pt,mt,rT⟩:=gatom1162 g pg
      refine ⟨t,_,_,(((((((ra.thenDo rb).thenDo rc).thenDo rd).thenDo re).thenDo rf).thenDo rg).thenDo rt),by omega,by omega,pt,
        by rw [mt,mg,mf,me,md,mc,mb,ma],?_,?_⟩
      · intro r a6 a7 a17;simp [rT,rG,rF,rE,rD,rC,rB,rA,Ne.symm a6,Ne.symm a7,Ne.symm a17]
      · rw [if_pos fires];simp [rT,rG,rF,e17,len] <;> decide
    · have nf : ¬guardFires s := fun h=>len h.2
      have ne : (e.getReg .x17 != e.getReg .x7)=true := by simp [e17,e7,len]
      rw [ne] at pf;simp only [ite_true] at pf
      obtain ⟨t,rt,pt,mt,rT⟩:=gatom1162 f pf
      refine ⟨t,_,_,((((((ra.thenDo rb).thenDo rc).thenDo rd).thenDo re).thenDo rf).thenDo rt),by omega,by omega,pt,
        by rw [mt,mf,me,md,mc,mb,ma],?_,?_⟩
      · intro r a6 a7 a17;simp [rT,rF,rE,rD,rC,rB,rA,Ne.symm a6,Ne.symm a7,Ne.symm a17]
      · rw [if_neg nf];simp [rT,rF,e17]
  · have nf : ¬guardFires s := fun h=>k h.1
    have t_ : (b.getReg .x16 != b.getReg .x6)=true := by simp [rB,rA,k]
    rw [t_] at pc_;simp only [ite_true] at pc_
    obtain ⟨t,rt,pt,mt,rT⟩:=gatom1162 c pc_
    refine ⟨t,_,_,(((ra.thenDo rb).thenDo rc).thenDo rt),by omega,by omega,pt,by rw [mt,mc,mb,ma],?_,?_⟩
    · intro r a6 a7 a17;simp [rT,rC,rB,rA,Ne.symm a6,Ne.symm a7,Ne.symm a17]
    · rw [if_neg nf];simp [rT,rC,rB,rA]

/-! ### The effective input -/

/-- The checker reads a k = 128 proof of 72,159 bytes as the 72,160-byte proof with a final 0. -/
def fires (i : CheckInput) : Prop := i.positions.card=128 ∧ i.proof.length=72159
instance (i : CheckInput) : Decidable (fires i) := by unfold fires; infer_instance
def pad (i : CheckInput) : CheckInput := { i with proof := i.proof ++ [0] }
def effective (i : CheckInput) : CheckInput := { i with proof := if fires i then i.proof ++ [0] else i.proof }
theorem effective_fires (i : CheckInput) (h : fires i) : effective i = pad i := by
  unfold effective pad; rw [if_pos h]
theorem effective_not (i : CheckInput) (h : ¬ fires i) : effective i = i := by
  unfold effective; rw [if_neg h]
theorem effective_positions (i : CheckInput) : (effective i).positions=i.positions := rfl
theorem effective_length (i : CheckInput) :
    (effective i).proof.length=if fires i then 72160 else i.proof.length := by
  by_cases h : fires i
  · rw [effective_fires i h, if_pos h]; simp [pad, h.2]
  · rw [effective_not i h, if_neg h]
/-- Byte loader of the check input: the buffer containing the address, else the image data, else 0. -/
private def loadByte (c : Submission) (i : CheckInput) (address : Nat) : Byte :=
  match (c.inputBuffers .check i).find? (fun b => decide (b.address ≤ address ∧ address < b.address + b.length)) with
  | some b => b.byteAt (address - b.address)
  | none => if Riscv.dataBase (c.image .check) ≤ address then
      (c.image .check).data[address - Riscv.dataBase (c.image .check)]?.getD 0 else 0

private theorem initial_mem_load (c : Submission) (i : CheckInput) :
    (c.initialState .check i).mem=fun address => BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (loadByte c i (address.toNat+j)).toNat * 2^(8*j)) := rfl

/-- The padded input loads the same bytes: the extra byte is 0, and outside the old proof the zeroed memory is 0. -/
theorem find_last {α : Type} (P : α → Bool) (x1 x2 x3 y y' : α) (py : P y = false) (py' : P y' = false) :
    [x1, x2, x3, y].find? P = [x1, x2, x3, y'].find? P := by
  simp only [List.find?_cons, py, py', List.find?_nil]

theorem find_first3 {α : Type} (P : α → Bool) (x1 x2 x3 y : α) (p1 : P x1 = false) (p2 : P x2 = false)
    (p3 : P x3 = false) : [x1, x2, x3, y].find? P = if P y then some y else none := by
  simp only [List.find?_cons, p1, p2, p3, List.find?_nil]
  cases P y <;> rfl

private theorem load_pad (c : Submission) (i : CheckInput) (address : Nat)
    (gap : c.layout.proof+i.proof.length < Riscv.dataBase (c.image .check))
    (low : c.layout.commitment+32 ≤ c.layout.proof ∧ c.layout.indices+8*i.positions.card ≤ c.layout.proof ∧
      c.layout.values+(LEAF_SIZE/8)*i.positions.card ≤ c.layout.proof) :
    loadByte c (pad i) address=loadByte c i address := by
  have card : (i.positions.sort (· ≤ ·)).length=i.positions.card := Finset.length_sort _
  have vcard : (i.positions.attach.sort (fun a b => a.val ≤ b.val)).length=i.positions.card := by
    rw [Finset.length_sort, Finset.card_attach]
  let P := fun (b : InputBuffer) => decide (b.address ≤ address ∧ address < b.address + b.length)
  have shape (x : CheckInput) : c.inputBuffers .check x = [fixedBuffer c.layout.commitment x.commitment,
      positionsBuffer c.layout.indices x.positions, valuesBuffer c.layout.values x.positions x.values,
      ⟨c.layout.proof, x.proof.length, fun j => x.proof[j]?.getD 0⟩] := rfl
  have shapePad : c.inputBuffers .check (pad i) = [fixedBuffer c.layout.commitment i.commitment,
      positionsBuffer c.layout.indices i.positions, valuesBuffer c.layout.values i.positions i.values,
      ⟨c.layout.proof, (i.proof ++ [0]).length, fun j => (i.proof ++ [0])[j]?.getD 0⟩] := rfl
  unfold loadByte
  rw [shapePad, shape]
  by_cases below : address < c.layout.proof
  · rw [find_last P _ _ _ _ ⟨c.layout.proof, i.proof.length, fun j => i.proof[j]?.getD 0⟩
      (by simp [P]; omega) (by simp [P]; omega)]
  · have f1 : P (fixedBuffer c.layout.commitment i.commitment) = false := by
      simp [P, fixedBuffer, DIGEST_BITS, DIGEST_BYTES]; omega
    have f2 : P (positionsBuffer c.layout.indices i.positions) = false := by
      simp [P, positionsBuffer, card]; omega
    have f3 : P (valuesBuffer c.layout.values i.positions i.values) = false := by
      simp [P, valuesBuffer, vcard]; omega
    rw [find_first3 P _ _ _ _ f1 f2 f3, find_first3 P _ _ _ _ f1 f2 f3]
    simp only [P, List.length_append, List.length_singleton]
    by_cases inside : address < c.layout.proof + i.proof.length
    · simp [show c.layout.proof ≤ address by omega, inside, show address < c.layout.proof + (i.proof.length + 1) by omega]
      rw [List.getElem?_append_left (by omega)]
    · by_cases last : address = c.layout.proof + i.proof.length
      · simp [show c.layout.proof ≤ address by omega, inside, show address < c.layout.proof + (i.proof.length + 1) by omega,
          show ¬ Riscv.dataBase (c.image .check) ≤ address by omega]
        rw [List.getElem?_append_right (by omega)]
        simp [show address - c.layout.proof - i.proof.length = 0 by omega]
      · simp [inside, show ¬ address < c.layout.proof + (i.proof.length + 1) by omega]

theorem initial_mem_pad (c : Submission) (i : CheckInput)
    (gap : c.layout.proof+i.proof.length < Riscv.dataBase (c.image .check))
    (low : c.layout.commitment+32 ≤ c.layout.proof ∧ c.layout.indices+8*i.positions.card ≤ c.layout.proof ∧
      c.layout.values+(LEAF_SIZE/8)*i.positions.card ≤ c.layout.proof) :
    (c.initialState .check (pad i)).mem=(c.initialState .check i).mem := by
  rw [initial_mem_load, initial_mem_load]
  funext address
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [load_pad c i _ gap low]

theorem getReg_mem (s : MachineState) (m : Word → Word) (r : Reg) : ({ s with mem := m }).getReg r = s.getReg r := by
  cases r <;> rfl

theorem pad_reg (c : Submission) (i : CheckInput) (r : Reg) (r17 : r≠.x17) :
    (c.initialState .check (pad i)).getReg r=(c.initialState .check i).getReg r := by
  unfold Submission.initialState
  simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r17)]
  by_cases r16 : r = .x16
  · subst r16
    simp only [MachineState.getReg_setReg_eq (show Reg.x16 ≠ .x0 by decide)]
    rfl
  · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r16)]
    by_cases r15 : r = .x15
    · subst r15; simp only [MachineState.getReg_setReg_eq (show Reg.x15 ≠ .x0 by decide)]
    · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r15)]
      by_cases r14 : r = .x14
      · subst r14; simp only [MachineState.getReg_setReg_eq (show Reg.x14 ≠ .x0 by decide)]
      · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r14)]
        by_cases r13 : r = .x13
        · subst r13; simp only [MachineState.getReg_setReg_eq (show Reg.x13 ≠ .x0 by decide)]
        · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r13)]
          by_cases r12 : r = .x12
          · subst r12; simp only [MachineState.getReg_setReg_eq (show Reg.x12 ≠ .x0 by decide)]
          · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r12)]
            by_cases r11 : r = .x11
            · subst r11; simp only [MachineState.getReg_setReg_eq (show Reg.x11 ≠ .x0 by decide)]
            · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r11)]
              by_cases r10 : r = .x10
              · subst r10; simp only [MachineState.getReg_setReg_eq (show Reg.x10 ≠ .x0 by decide)]
              · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r10)]
                by_cases r2 : r = .x2
                · subst r2; simp only [MachineState.getReg_setReg_eq (show Reg.x2 ≠ .x0 by decide)]
                · simp only [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm r2)]
                  simp only [MachineState.getReg]

theorem pad_x17 (c : Submission) (i : CheckInput) :
    (c.initialState .check (pad i)).getReg .x17=addr (i.proof.length+1) := by
  change BitVec.ofNat 64 (i.proof ++ [0]).length=_;simp [addr]

theorem initial_x17 (c : Submission) (i : CheckInput) :
    (c.initialState .check i).getReg .x17=addr i.proof.length := rfl
theorem initial_x16 (c : Submission) (i : CheckInput) :
    (c.initialState .check i).getReg .x16=addr i.positions.card := rfl

end CommitGolfCandidate.Layout2.Cap
