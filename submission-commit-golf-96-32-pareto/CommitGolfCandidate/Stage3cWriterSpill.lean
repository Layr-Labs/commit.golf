import CommitGolfCandidate.Stage3cSpillParts
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem glue (s : MachineState) (xs ys : PathCode) (good : pathReady s xs) (next : pathReady (pathEnd s xs) ys) :
    pathReady s (xs++ys) ∧ pathEnd s (xs++ys)=pathEnd (pathEnd s xs) ys := by
  induction xs generalizing s with
  | nil=>exact ⟨next,rfl⟩
  | cons v xs ih=>
    obtain ⟨ok,eq⟩:=ih _ good.2.2.2 next
    exact ⟨⟨good.1,good.2.1,good.2.2.1,ok⟩,eq⟩

attribute [local irreducible] atTest afterTest tailEnd
theorem spill_ready (s : MachineState) (pc : s.pc=pcAt 32) (valid : accessValid (s.getReg .x19) 8=true)
    (b : Bool) (fit : ((s.getReg .x24+signExtend12 4032)==0)=b) :
    pathReady s (spill b) ∧
    let t:=pathEnd s (spill b)
    t.pc=pcAt 21 ∧ t.getReg .x19=s.getReg .x19+8 ∧ t.getReg .x24=s.getReg .x24+signExtend12 4032 ∧
    t.getReg .x23=(if b then 0 else s.getReg .x28 >>> ((s.getReg .x31-(s.getReg .x24+signExtend12 4032)).toNat%64)) ∧
    t.mem=(s.setMem (s.getReg .x19) (s.getReg .x23)).mem := by
  let u:=atTest s
  let v:=afterTest u
  obtain ⟨ok,ip⟩:=prefix_ready s pc valid
  have tv : v=u.setPC (pcAt (if b then 39 else 36)) := tested _ ip b (by rw [prefix_count];exact fit)
  obtain ⟨ready,back,ptr,cnt,buf,mem⟩:=tail_state b v (by rw [tv];rfl)
  let branch : Nat × Instr := (35,.BEQ .x24 .x0 16)
  have cont : pathReady u (branch::shiftTail b) := ⟨ip,rfl,rfl,by simpa only [v,afterTest] using ready⟩
  have layout : spill b = storePrefix++(branch::shiftTail b) := by cases b <;> rfl
  rw [layout]
  obtain ⟨validAll,last⟩:=glue s storePrefix (branch::shiftTail b) ok (by simpa only [u,atTest] using cont)
  have eq : pathEnd s (storePrefix++branch::shiftTail b)=tailEnd b v := by
    rw [last];simp only [tailEnd,v,u,atTest,afterTest,branch,pathEnd]
  dsimp only
  rw [eq]
  refine ⟨validAll,back,ptr.trans ?_,cnt.trans ?_,buf.trans ?_,mem.trans ?_⟩
  · rw [tv];exact prefix_ptr s
  · rw [tv];exact prefix_count s
  · rw [tv];simp only [MachineState.getReg_setPC,u,prefix_count,prefix_width,prefix_word]
  · rw [tv];exact prefix_mem s
end CommitGolfCandidate.Chained.BinaryMachine.Writer
