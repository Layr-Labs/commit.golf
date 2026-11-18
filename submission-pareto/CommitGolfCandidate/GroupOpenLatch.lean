import CommitGolfCandidate.GroupOpenSelect

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Grouped (rank)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set open_zero
attribute [local simp] mem_of_reg MachineState.getMem_setPC MachineState.getMem_setReg

def finalPC (left : Nat) := if left=1 then address 15 else address 739
def advanced (s : MachineState) (left : Nat) := walkRows s (nextRows (decide (left=1)))

private theorem decremented (left : Nat) (l : 0<left) :
    countWord left+signExtend12 (-1)=countWord (left-1) := by
  have sub := BitVec.ofNat_sub_ofNat_of_le (w:=64) left 1 (by decide) l
  rw [BitVec.sub_eq_add_neg] at sub
  exact sub

private theorem counter_zero (left : Nat) (l : 0<left) (small : left≤16777216) :
    countWord (left-1)=0#64 ↔ left=1 := by
  constructor
  · intro h;have z:=congrArg BitVec.toNat h
    change (left-1)%2^64=0 at z;omega
  · intro h;subst left;rfl

private theorem index_bump (ord : Nat) : indexAt ord+signExtend12 8=indexAt (ord+1) := by
  change BitVec.ofNat 64 _+BitVec.ofNat 64 8=_
  rw [←BitVec.ofNat_add];unfold indexAt;congr 1 <;> omega

private def bump (s : MachineState) :=
  execInstrBr (execInstrBr s (.ADDI .x14 .x14 8)) (.ADDI .x17 .x17 (-1))

private theorem bump_info (s : MachineState) (ord left : Nat) (l : 0<left)
    (pc : s.pc=address 758) (idx : s.getReg .x14=indexAt ord) (count : s.getReg .x17=countWord left) :
    (bump s).pc=address 760 ∧ (bump s).getReg .x14=indexAt (ord+1) ∧
    (bump s).getReg .x17=countWord (left-1) ∧ (bump s).mem=s.mem := by
  refine ⟨?_,?_,?_,?_⟩
  · change s.pc+4+4=_;rw [pc];rfl
  · change s.getReg .x14+signExtend12 8=_;rw [idx];exact index_bump ord
  · change s.getReg .x17+signExtend12 (-1)=_;rw [count];exact decremented left l
  · rfl

private theorem back (s : MachineState) (pc : s.pc=address 760) (nz : s.getReg .x17≠0#64) :
    execInstrBr s (.BNE .x17 .x0 8108)=s.setPC (address 739) := by
  have yes : (s.getReg .x17 != s.getReg .x0)=true := by simp [open_zero,nz]
  simp only [execInstrBr,yes,ite_true,pc]
  exact congrArg s.setPC (by decide : address 760+signExtend13 8108=address 739)

private theorem fall (s : MachineState) (pc : s.pc=address 760) (z : s.getReg .x17=0#64) :
    execInstrBr s (.BNE .x17 .x0 8108)=s.setPC (address 761) := by
  simp only [execInstrBr,open_zero,z,beq_self_eq_true,ite_true,pc]
  exact congrArg s.setPC (by decide : address 760+4=address 761)

private theorem exit_jump (s : MachineState) (pc : s.pc=address 761) :
    execInstrBr s (.JAL .x0 2094168)=s.setPC (address 15) := by
  change s.setPC (s.pc+signExtend21 2094168)=_
  rw [pc];exact congrArg s.setPC (by decide : address 761+signExtend21 2094168=address 15)

private def firstMoves : List Row := [(758,.ADDI .x14 .x14 8),(759,.ADDI .x17 .x17 (-1))]
private def lastMoves (last : Bool) : List Row := if last then [(760,.BNE .x17 .x0 8108),(761,.JAL .x0 2094168)]
  else [(760,.BNE .x17 .x0 8108)]

private theorem next_parts (last : Bool) : nextRows last=firstMoves++lastMoves last := by cases last <;> rfl
private theorem first_value (s : MachineState) : walkRows s firstMoves=bump s := rfl
private theorem first_legal (s : MachineState) (pc : s.pc=address 758) : legal firstMoves s := by
  refine ⟨pc,rfl,?_,rfl,trivial⟩
  change s.pc+4=_
  rw [pc];rfl

private theorem last_done (s : MachineState) (pc : s.pc=address 760) (z : s.getReg .x17=0#64) :
    legal (lastMoves true) s ∧ walkRows s (lastMoves true)=s.setPC (address 15) := by
  have first:=fall s pc z
  have atJump:=congrArg MachineState.pc first
  refine ⟨⟨pc,rfl,atJump,rfl,trivial⟩,?_⟩
  simp only [lastMoves,ite_true,walkRows,List.foldl_cons,List.foldl_nil,first,exit_jump _ (show (s.setPC (address 761)).pc=address 761 from rfl)]
  rfl

private theorem last_again (s : MachineState) (pc : s.pc=address 760) (z : s.getReg .x17≠0#64) :
    legal (lastMoves false) s ∧ walkRows s (lastMoves false)=s.setPC (address 739) :=
  ⟨⟨pc,rfl,trivial⟩,back s pc z⟩

private theorem walk_join (s : MachineState) (xs ys : List Row) :
    walkRows s (xs++ys)=walkRows (walkRows s xs) ys := by
  simp only [walkRows,List.foldl_append]

private theorem next_value (s : MachineState) (last : Bool) :
    walkRows s (nextRows last)=walkRows (bump s) (lastMoves last) := by
  rw [next_parts,walk_join,first_value]

private theorem next_legal (s : MachineState) (last : Bool) (pc : s.pc=address 758)
    (good : legal (lastMoves last) (bump s)) : legal (nextRows last) s := by
  rw [next_parts];apply legal_append _ _ _ (first_legal s pc);rw [first_value];exact good

attribute [local irreducible] bump walkRows nextRows

theorem next_ok (s : MachineState) (ord left : Nat) (pc : s.pc=address 758) (l : 0<left) (hi : left≤16777216)
    (index : s.getReg .x14=indexAt ord) (counter : s.getReg .x17=countWord left) :
    legal (nextRows (decide (left=1))) s ∧ (advanced s left).pc=finalPC left ∧
      (advanced s left).getReg .x14=indexAt (ord+1) ∧ (advanced s left).getReg .x17=countWord (left-1) ∧
      (advanced s left).mem=s.mem := by
  have br:=bump_info s ord left l pc index counter
  have test : (bump s).getReg .x17=0#64 ↔ left=1 := br.2.2.1 ▸ counter_zero left l hi
  by_cases last : left=1
  · have d:=last_done (bump s) br.1 (test.mpr last)
    rw [decide_eq_true last,advanced,decide_eq_true last,next_value,d.2,finalPC,if_pos last]
    exact ⟨next_legal s true pc d.1,rfl,br.2.1,br.2.2.1,br.2.2.2⟩
  · have d:=last_again (bump s) br.1 (mt test.mp last)
    rw [decide_eq_false last,advanced,decide_eq_false last,next_value,d.2,finalPC,if_neg last]
    exact ⟨next_legal s false pc d.1,rfl,br.2.1,br.2.2.1,br.2.2.2⟩

attribute [local semireducible] walkRows nextRows

private theorem rows_preserve (rows : List Row) (s : MachineState) (r : Reg)
    (each : ∀ p∈rows, ∀ st : MachineState, (execInstrBr st p.2).getReg r=st.getReg r) :
    (walkRows s rows).getReg r=s.getReg r := by
  induction rows generalizing s with
  | nil => unfold walkRows;rfl
  | cons p rest ih => unfold walkRows;exact (ih (execInstrBr s p.2) (fun t h => each t (List.mem_cons_of_mem _ h))).trans (each p (by simp) s)

private theorem branch_reg (u : MachineState) (r : Reg) (imm : BitVec 13) :
    (execInstrBr u (.BNE .x17 .x0 imm)).getReg r=u.getReg r := by
  change (if (u.getReg .x17 != u.getReg .x0) then u.setPC (u.pc+signExtend13 imm) else u.setPC (u.pc+4)).getReg r=_
  split <;> exact MachineState.getReg_setPC ..

private theorem jump_reg (u : MachineState) (r : Reg) (imm : BitVec 21) :
    (execInstrBr u (.JAL .x0 imm)).getReg r=u.getReg r := MachineState.getReg_setPC ..

theorem next_keeps (s : MachineState) (left : Nat) (r : Reg) (a : r≠.x14) (b : r≠.x17) :
    (advanced s left).getReg r=s.getReg r := by
  unfold advanced;apply rows_preserve;intro p h u
  unfold nextRows at h;cases tag : (decide (left=1)) <;>
    simp only [tag,Bool.false_eq_true,ite_false,ite_true,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
  · rcases h with h|h|h <;> subst p <;> first | exact branch_reg u r _ | simp [execInstrBr,Ne.symm a,Ne.symm b]
  · rcases h with h|h|h|h <;> subst p
    all_goals first | exact branch_reg u r _ | exact jump_reg u r _ |
      simp [execInstrBr,Ne.symm a,Ne.symm b]

def receives (s : MachineState) (y : BitVec 1600) := writeBits (beforeCall s) (wordAddress 192) y
def finishOne (s : MachineState) (i : Index) (left : Nat) (y : BitVec 1600) :=
  advanced (copied (choose (receives s y) i)) left

def perTrace (s : MachineState) (i : Index) (left : Nat) : OracleComp World MachineState := do
  let y ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView (beforeCall s)) 128)))))
  return finishOne s i left y

def perSteps (i : Index) (left : Nat) := 21+(if rank i.val=0 then 1 else 0)+(if left=1 then 1 else 0)
def perCycles (i : Index) (left : Nat) := perSteps i left+10

theorem per_run (s : MachineState) (i : Index) (ord left fuel : Nat) (l : 0<left) (hi : left≤16777216)
    (r : Input s i ord left) : execute openingImage (perSteps i left+fuel) s true =
      (do let t ← perTrace s i left; let z ← execute openingImage fuel t true; return z.charge (perCycles i left) 1) := by
  let rows:=postRows (Direct i) (decide (left=1))
  have lengths : perSteps i left=7+1+rows.length ∧ perCycles i left=10+8+price rows := by
    dsimp [rows,Direct,perSteps,perCycles,postRows,price]
    by_cases z : rank i.val=0 <;> by_cases x : left=1 <;> simp [z,x,instructionCycles]
  obtain ⟨pr,idx,sub,pc,_⟩:=before_regs s i ord left r
  have fetch : fetch openingImage (beforeCall s)=some (.base .ECALL) :=
    packed_fetch_base _ 746 _ (by decide) pc (by decide +kernel)
  have call:=execute_permutation_call openingImage (rows.length+fuel) (beforeCall s) true 128 192
    (by decide) (by decide) pr.input pr.output pr.selector pr.width pr.primitive fetch
  rw [show perSteps i left+fuel=7+((rows.length+fuel)+1) by omega,pre_run i s ord left _ r]
  rw [call];simp only [perTrace,bind_assoc,pure_bind]
  apply bind_congr; intro y
  let w:=receives s y
  let a:=choose w i
  let b:=copied a
  have regs (k : Reg) : w.getReg k=(beforeCall s).getReg k := writeBits_register ..
  have wp : w.pc=address 747 := by rw [show w.pc=(beforeCall s).pc+4 from written_pc ..,pc];rfl
  have chooseOk:=choose_legal w i wp ((regs _).trans sub)
  obtain ⟨ap,ar,ad⟩:=chosen w i wp ((regs _).trans idx) ((regs _).trans sub) ((regs _).trans pr.output) ((regs _).trans pr.salt)
  have keep (k : Reg) (h7 : k≠.x7 :=by decide) (h30 : k≠.x30 :=by decide) (h31 : k≠.x31 :=by decide) :
      b.getReg k=(beforeCall s).getReg k :=
    (copied_keeps a k h31).trans ((choose_keeps w i k h7 h30).trans (regs k))
  have t:=next_ok b ord left (copied_pc a ap) l hi ((keep .x14).trans pr.index) ((keep .x17).trans pr.leftReg)
  have ok : legal rows w := by
    rw [show rows=selectRows (Direct i)++copyRows++nextRows (decide (left=1)) from post_parts ..]
    apply legal_append
    · exact legal_append w _ _ chooseOk (copy_legal a i ap ar ad)
    · simpa only [b,a,copied,choose,walkRows,List.foldl_append] using t.1
  change (do let z ← execute openingImage (rows.length+fuel) w true;return (z.charge 8 1).charge 10 0)=_
  rw [walk_rows_run w rows ok (post_row_fetch (Direct i) (decide (left=1))) fuel true]
  have same : walkRows w rows=finishOne s i left y := by
    rw [show rows=selectRows (Direct i)++copyRows++nextRows (decide (left=1)) from post_parts ..]
    simp only [finishOne,advanced,copied,choose,walkRows,List.foldl_append];rfl
  rw [same,lengths.2];simp only [bind_assoc,pure_bind]
  apply bind_congr;intro z;apply congrArg pure;cases z;simp [Execution.charge,Nat.add_assoc] <;> omega

end TwoPermutationPrototype.GroupedOpening
