import CommitGolfCandidate.TwoPermutationWideLeafRun

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
private theorem reg_store (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem first_reg_frame (s : MachineState) (slot : Fin 256) (reg : Reg)
    (out : Reg.x12 ≠ reg) (tmp : Reg.x31 ≠ reg) :
    (preparedA s slot).getReg reg = s.getReg reg := by
  simp only [preparedA,firstInstructions,wideFirstOps,List.foldl_cons,List.foldl_nil,execInstrBr,
    MachineState.getReg_setPC,reg_store,MachineState.getReg_setReg_ne _ _ _ _ out,
    MachineState.getReg_setReg_ne _ _ _ _ tmp]

theorem finished_reg_frame (s : MachineState) (slot : Fin 256) (start dst : Nat)
    (a b : BitVec 1600) (reg : Reg) (src : Reg.x10 ≠ reg) (out : Reg.x12 ≠ reg) (tmp : Reg.x31 ≠ reg) :
    (finishedLeaf s slot start dst a b).getReg reg = s.getReg reg := by
  simp only [finishedLeaf,repliedB,preparedB,secondInstructions,wideSecondOps,List.foldl_cons,List.foldl_nil,
    execInstrBr,MachineState.getReg_setPC,reg_store,MachineState.getReg_setReg_ne _ _ _ _ src,
    MachineState.getReg_setReg_ne _ _ _ _ out,MachineState.getReg_setReg_ne _ _ _ _ tmp,
    CommitGolfCandidate.writeBits_register,repliedA,first_reg_frame s slot reg out tmp]

def idx (g : Nat) (u : Fin 256) := 256*g+u.val
def heapBase (g pos : Nat) := leafDest (256*g+64*(pos/64))
def nonceBase (g pos : Nat) := leafSalt (256*g+128*(pos/128))

structure Regs (s : MachineState) (g pos : Nat) : Prop where
  source : s.getReg .x10=wordAddress (leafStart (256*g+pos)+4)
  heap : s.getReg .x20=wordAddress (heapBase g pos)
  salts : s.getReg .x22=wordAddress (nonceBase g pos)
  stride : s.getReg .x7=2048
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  pc : s.pc=wideLeafPC pos 0

theorem ready_slot (s : MachineState) (g : Nat) (u : Fin 256) (bound : g<2^16) (r : Regs s g u.val) :
    LeafReady s u (leafStart (idx g u)) (idx g u) (leafDest (idx g u)) (nonceBase g u.val) := by
  have h := u.isLt
  refine ⟨r.source,?_,r.salts,?_,?_,?_,?_,?_,r.selector,r.size,r.primitive,by unfold leafStart;omega⟩
  · rw [r.heap,wordAddress,wordAddress,←BitVec.ofNat_add]
    congr 1;unfold heapBase leafDest idx;omega
  · rw [commit_tag_address,wordAddress];congr 1;unfold leafStart;omega
  all_goals simp only [leafStart,leafDest,nonceBase,leafSalt,idx] <;> omega

structure RawRegs (s : MachineState) (g : Nat) (u : Fin 256) : Prop where
  source : s.getReg .x10=wordAddress (leafStart (idx g u+1)+4)
  dest : s.getReg .x12=wordAddress (leafDest (idx g u))
  heap : s.getReg .x20=wordAddress (heapBase g u.val)
  salts : s.getReg .x22=wordAddress (nonceBase g u.val)
  stride : s.getReg .x7=2048
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  pc : s.pc=leafPC u 12

/-- Register and PC projections of the second reply and final ordinary instruction. -/
private theorem endFields (s : MachineState) (dst : Nat) (b : BitVec 1600) :
    let w := writeBits s (wordAddress dst) b
    let t := execInstrBr w (.ADDI .x10 .x10 192)
    t.getReg .x10=s.getReg .x10+192 ∧ t.getReg .x12=s.getReg .x12 ∧ t.pc=s.pc+8 := by
  dsimp only
  have nx : ∀ w : MachineState,
      (execInstrBr w (.ADDI .x10 .x10 192)).getReg .x10 = w.getReg .x10+192 := by intro w; rfl
  have out : ∀ w : MachineState,
      (execInstrBr w (.ADDI .x10 .x10 192)).getReg .x12=w.getReg .x12 := by intro w; rfl
  have step : ∀ w : MachineState,
      (execInstrBr w (.ADDI .x10 .x10 192)).pc=w.pc+4 := by intro w; rfl
  rw [nx,out,step,CommitGolfCandidate.writeBits_register,CommitGolfCandidate.writeBits_register,written_pc,
    BitVec.add_assoc]
  exact ⟨rfl,rfl,rfl⟩

theorem post_slot (s : MachineState) (g : Nat) (u : Fin 256) (bound : g<2^16) (r : Regs s g u.val)
    (a b : BitVec 1600) :
    let i := idx g u
    RawRegs (finishedLeaf s u (leafStart i) (leafDest i) a b) g u := by
  let i := idx g u
  let start := leafStart i
  let dst := leafDest i
  have ready := ready_slot s g u bound r
  have pc : s.pc=leafPC u 0 := r.pc
  have prev := after_a_control _ _ _ _ _ _ ready pc a
  have src := after_a_input_cursor _ _ _ _ _ _ ready a
  let p := repliedA s u start a
  have second := second_execution p u
  have x : (preparedB s u start a).getReg .x10=wordAddress (start+4)+64 := second.2.1.trans (congrArg (·+64) src)
  have cursor : (preparedB s u start a).getReg .x12=wordAddress dst := by
    rw [preparedB,second.2.2.1,show p.getReg .x20=s.getReg .x20 from prev.2.2.2.1,ready.destination]
  have here : (preparedB s u start a).pc=leafPC u 10 := by
    change ((secondInstructions u).foldl execInstrBr p).pc=_
    rw [second.2.2.2.2.2.2,show p.pc=leafPC u 3 from prev.2.2.2.2];exact leaf_pc_add u 3 7
  have endState := endFields (preparedB s u start a) dst b
  change (finishedLeaf s u start dst a b).getReg .x10 = _ ∧ (finishedLeaf s u start dst a b).getReg .x12 = _ ∧ (finishedLeaf s u start dst a b).pc = _ at endState
  have hold := finished_reg_frame s u start dst a b
  refine ⟨?_,?_,(hold .x20 (by decide) (by decide) (by decide)).trans r.heap,
    (hold .x22 (by decide) (by decide) (by decide)).trans r.salts,
    (hold .x7 (by decide) (by decide) (by decide)).trans r.stride,
    (hold .x5 (by decide) (by decide) (by decide)).trans r.selector,
    (hold .x11 (by decide) (by decide) (by decide)).trans r.size,
    (hold .x13 (by decide) (by decide) (by decide)).trans r.primitive,?_⟩
  · rw [endState.1,x,BitVec.add_assoc]
    change wordAddress (leafStart i+4)+wordAddress 32=_
    rw [←wordAddress_add];congr 1 <;> unfold leafStart <;> omega
  · exact endState.2.1.trans cursor
  · rw [endState.2.2,here]
    exact leaf_pc_add u 10 2

end TwoPermutationPrototype.RV64.WideLeaves
