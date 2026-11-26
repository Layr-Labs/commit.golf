import CommitGolfCandidate.ReconstructedCheckMemoryOps
import CommitGolfCandidate.ReconstructedCheckCapScanData
import CommitGolfCandidate.ReconstructedCheckCapCopy

namespace CommitGolfCandidate.Reconstruction.CheckCapLowStore
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps CheckRecorded CommitBlocks
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open CheckCapScanData (W cap scratch)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

def cell (id : Nat) := cap/8+4*id
def copy (m : Memory) (a : Nat) (x y z h : Word) :=
  writeWord (writeWord (writeWord (writeWord m a x) (a+1) y) (a+2) z) (a+3) h

def ops (a : Nat) : List Op := [.reg .x6 (.slli .x6 5),.reg .x6 (.add .x6 .x23),.reg .x29 (.and .x29 .x14),
  .sd .x6 .x5 0 a,.sd .x6 .x7 8 (a+1),.sd .x6 .x28 16 (a+2),.sd .x6 .x29 24 (a+3),
  .reg .x16 (.addi .x16 4),.reg .x24 (.add .x24 .x15)]
def final (m : Model) (a : Nat) := (ops a).foldl (fun n op=>op.apply n) m

private theorem listed (a : Nat) : CheckStraight.Listed 485 ((ops a).map Op.instr) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,trivial⟩

private theorem physical (id : Fin 1024) : (W id.val <<< (5:Nat))+W cap=wordAddress (cell id.val) :=
  (by decide +kernel : ∀ j : Fin 1024,(W j.val <<< (5:Nat))+W cap=wordAddress (cell j.val)) id

private theorem valid (m : Model) (id : Fin 1024) (v : m.reg .x6=W id.val) (base : m.reg .x23=W cap) :
    Checked m (ops (cell id.val)) := by
  have hi:=id.isLt
  have bound : cell id.val+4<2^33:=by unfold cell cap;omega
  simp only [ops,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩,⟨by omega,?_⟩⟩
  all_goals change ((m.reg .x6 <<< (5:Nat))+m.reg .x23)+signExtend12 _=wordAddress _
  all_goals rw [v,base,physical]
  · exact BitVec.add_zero _
  · exact (wordAddress_add _ 1).symm
  · exact (wordAddress_add _ 2).symm
  · exact (wordAddress_add _ 3).symm

theorem stored (s : MachineState) (m : Model) (id : Fin 1024) (fit : Fits s m)
    (address : m.reg .x6=W id.val) (base : m.reg .x23=W cap) (pc : s.pc=addr 485) (o : Oracle) :
    ∃ t,Segment o 9 s t [] ∧ t.pc=addr 494 ∧
      (∀ j, j<2^33→memoryView t j=copy m.mem (cell id.val) (m.reg .x5) (m.reg .x7) (m.reg .x28)
        (m.reg .x29 &&& m.reg .x14) j) ∧
      t.getReg .x16=m.reg .x16+4 ∧ t.getReg .x24=m.reg .x24+m.reg .x15 ∧
      ∀ q∉[Reg.x6,.x29,.x16,.x24],t.getReg q=m.reg q := by
  obtain ⟨t,sg,pos,h⟩:=CheckStraight.block o m (ops (cell id.val)) 485 (by change 485+9≤796;decide)
    (listed _) (valid m id address base) s pc fit
  have ty : Fits t (final m (cell id.val)):=h
  have memory : (final m (cell id.val)).mem=copy m.mem (cell id.val) (m.reg .x5) (m.reg .x7) (m.reg .x28)
      (m.reg .x29 &&& m.reg .x14) := rfl
  refine ⟨t,sg,pos,fun j hj=>(ty.memory j hj).trans (congrFun memory j),ty.registers _,ty.registers _,?_⟩
  intro q fresh;rw [ty.registers];unfold final
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at fresh
  simp [ops,Op.apply,Model.set,Model.store,Ne.symm fresh.1,Ne.symm fresh.2.1,Ne.symm fresh.2.2.1,Ne.symm fresh.2.2.2]

theorem load (o : Oracle) (s : MachineState) (id : Fin 1024) (i : Nat) (index : i<512) (pc : s.pc=addr 484)
    (ptr : s.getReg .x16=CheckCapSlots.address scratch i)
    (seen : CheckCapSlots.read (memoryView s) scratch i=BitVec.ofNat 32 id.val) :
    Segment o 1 s ((s.setReg .x6 (W id.val)).setPC (addr 485)) [] := by
  have step:=CheckMemoryOps.loadU32 o s 484 .x6 .x16 _ (by decide) pc ptr
    (CheckCapSlots.valid scratch i (by decide) (by change 68719473368+4*i+4≤68719476736;omega))
  rw [CheckCapSlots.load_id s scratch i (by decide),seen] at step
  have extend : (BitVec.ofNat 32 id.val).zeroExtend 64=W id.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat];have h:=id.isLt;omega
  rw [extend] at step;exact step

end CommitGolfCandidate.Reconstruction.CheckCapLowStore
