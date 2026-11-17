import CommitGolfCandidate.TwoPermutationWideLeafRun

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
private theorem reg_store (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem first_reg_frame (s : MachineState) (slot : Fin 256) (reg : Reg)
    (out : Reg.x12 ≠ reg) (tmp : Reg.x31 ≠ reg) :
    (preparedA s slot).getReg reg = s.getReg reg := by
  simp only [preparedA,firstInstructions,List.foldl_cons,List.foldl_nil,execInstrBr,
    MachineState.getReg_setPC,reg_store,MachineState.getReg_setReg_ne _ _ _ _ out,
    MachineState.getReg_setReg_ne _ _ _ _ tmp]

theorem finished_reg_frame (s : MachineState) (slot : Fin 256) (start dst : Nat)
    (a b : BitVec 1600) (reg : Reg) (src : Reg.x10 ≠ reg) (out : Reg.x12 ≠ reg) (tmp : Reg.x31 ≠ reg) :
    (finishedLeaf s slot start dst a b).getReg reg = s.getReg reg := by
  simp only [finishedLeaf,repliedB,preparedB,secondInstructions,List.foldl_cons,List.foldl_nil,
    execInstrBr,MachineState.getReg_setPC,reg_store,MachineState.getReg_setReg_ne _ _ _ _ src,
    MachineState.getReg_setReg_ne _ _ _ _ out,MachineState.getReg_setReg_ne _ _ _ _ tmp,
    CommitGolfCandidate.writeBits_register,repliedA,first_reg_frame s slot reg out tmp]

def idx (g : Nat) (u : Fin 256) := 256*g+u.val
def heapBase (g pos : Nat) := leafDest (256*g+64*(pos/64))
def nonceBase (g pos : Nat) := leafSalt (256*g+128*(pos/128))

structure Regs (s : MachineState) (g pos : Nat) : Prop where
  source : s.getReg .x10=wordAddress (leafStart (256*g+pos))
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
  refine ⟨r.source,?_,r.salts,?_,?_,?_,?_,?_,r.selector,r.size,r.primitive⟩
  · rw [r.heap,wordAddress,wordAddress,←BitVec.ofNat_add]
    congr 1;unfold heapBase leafDest idx;omega
  · rw [commit_tag_address,wordAddress];congr 1;unfold leafStart;omega
  all_goals simp only [leafStart,leafDest,nonceBase,leafSalt,idx] <;> omega

structure RawRegs (s : MachineState) (g : Nat) (u : Fin 256) : Prop where
  source : s.getReg .x10=wordAddress (leafStart (idx g u+1))
  dest : s.getReg .x12=wordAddress (leafDest (idx g u))
  heap : s.getReg .x20=wordAddress (heapBase g u.val)
  salts : s.getReg .x22=wordAddress (nonceBase g u.val)
  stride : s.getReg .x7=2048
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  pc : s.pc=leafPC u 14

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
  have x : (preparedB s u start a).getReg .x10=wordAddress start+96 := second.2.1.trans (congrArg (·+96) src)
  have cursor : (preparedB s u start a).getReg .x12=wordAddress dst := by
    rw [preparedB,second.2.2.1,show p.getReg .x20=s.getReg .x20 from prev.2.2.2.1,ready.destination]
  have here : (preparedB s u start a).pc=leafPC u 12 := by
    change ((secondInstructions u).foldl execInstrBr p).pc=_
    rw [second.2.2.2.2.2.2,show p.pc=leafPC u 9 from prev.2.2.2.2];exact leaf_pc_add u 9 3
  have hold := finished_reg_frame s u start dst a b
  refine ⟨?_,?_,(hold .x20 (by decide) (by decide) (by decide)).trans r.heap,
    (hold .x22 (by decide) (by decide) (by decide)).trans r.salts,
    (hold .x7 (by decide) (by decide) (by decide)).trans r.stride,
    (hold .x5 (by decide) (by decide) (by decide)).trans r.selector,
    (hold .x11 (by decide) (by decide) (by decide)).trans r.size,
    (hold .x13 (by decide) (by decide) (by decide)).trans r.primitive,?_⟩
  · change (repliedB s u start dst a b).getReg .x10+160=_
    rw [repliedB,CommitGolfCandidate.writeBits_register,x,BitVec.add_assoc]
    change wordAddress (leafStart i)+wordAddress 32=_
    rw [←wordAddress_add];congr 1 <;> unfold leafStart <;> omega
  · change (writeBits (preparedB s u start a) (wordAddress dst) b).getReg .x12=_
    rw [CommitGolfCandidate.writeBits_register,cursor]
  · change (preparedB s u start a).pc+4+4=_
    rw [here,BitVec.add_assoc];exact leaf_pc_add u 12 2


end TwoPermutationPrototype.RV64.WideLeaves
