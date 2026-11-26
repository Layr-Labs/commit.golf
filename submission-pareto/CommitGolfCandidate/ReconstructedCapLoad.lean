import CommitGolfCandidate.ReconstructedCapEntry
import CommitGolfCandidate.ReconstructedCapSlots
import CommitGolfCandidate.ReconstructedOpeningHeaderAddress

namespace CommitGolfCandidate.Reconstruction.CapLoad
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 LeafModel OpeningOps
open CommitBlocks (addr)
open HonestCapTables (addrSlot)
open OpeningCursor (W)
open OpeningQuery (after)
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

abbrev heap := 4294971424
def word (d id k : Nat) := heap/8+4*(d+id)+k

theorem address (d id k : Nat) : wordAddress (word d id k)=W (CommitParents.addr d id+8*k) := by
  apply congrArg W
  unfold word heap CommitParents.addr;omega

theorem index_shift (n : Nat) (lim : n<1034) :
    (W n <<< (32:Nat)) >>> (27:Nat) = W (32*n) := by
  exact (by decide +kernel : ∀ i : Fin 1034, (W i.val <<< (32:Nat)) >>> (27:Nat) = W (32*i.val)) ⟨n,lim⟩

theorem loaded (s : MachineState) (m : Model) (fits : Fits s m) (idx : Fin 512) (ids : List Nat)
    (slot : idx.val < ids.length) (stored : CapSlots.Contains m.mem ids) (id : Nat)
    (which : ids[idx.val]=id) (small : id<1024) :
    (s.getWord32 (addrSlot idx.val)).signExtend 64=W id := by
  have atSlot := stored ⟨idx.val,slot⟩
  have wr := fits.memory (CapSlots.cell idx.val) (by have bound := idx.isLt;change 8589934272+idx.val/2<2^33;omega)
  rw [CapSlots.load_id]
  change (extractWord32 (memoryView s (CapSlots.cell idx.val)) (CapSlots.half idx.val)).signExtend 64=_
  rw [wr]
  change (CapSlots.read m.mem idx.val).signExtend 64=_
  rw [atSlot,which]
  exact (by decide +kernel : ∀ i : Fin 1024, (BitVec.ofNat 32 i.val).signExtend 64=W i.val) ⟨id,small⟩

theorem first (o : Oracle) (s : MachineState) (m : Model) (fits : Fits s m) (idx : Fin 512)
    (rd rs : Reg) (pc : Nat) (loc : s.pc=addr pc) (inside : pc<1660)
    (listed : OpeningStraight.actualAt pc=some (.base (.LW rd rs 0))) (ptr : m.reg rs=addrSlot idx.val)
    (id : Nat) (value : (s.getWord32 (addrSlot idx.val)).signExtend 64=W id) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 1 s t ∧ t.pc=addr (pc+1) ∧ Fits t (m.set rd (W id)) := by
  let t := (s.setReg rd (W id)).setPC (s.pc+4)
  have valid : ordinaryStep s (.base (.LW rd rs 0))=some t := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,fits.registers,ptr,
      show signExtend12 0=0#64 from rfl,BitVec.add_zero,CapSlots.valid idx,ite_true,value,t]
  exact ⟨t,CommitExact.plain _ _ _ _ _ (OpeningStraight.fetched pc _ inside listed s loc) valid,
    by change s.pc+4=_;rw [loc];exact (CommitBlocks.addr_next pc).symm,(fits.reg rd _).pc _⟩

def ops (d id : Nat) : List Op := [
  .reg .x14 (.add .x14 .x10),.reg .x14 (.slli .x14 32),.reg .x14 (.srli .x14 27),.reg .x15 (.add .x14 .x5),
  .ld .x14 .x15 0 (word d id 0),.ld .x1 .x15 8 (word d id 1),.ld .x16 .x15 16 (word d id 2),
  .ld .x27 .x15 24 (word d id 3)]

theorem checks (m : Model) (d id : Nat) (depth : d≤9) (small : id<1024)
    (dep : m.reg .x10=W d) (key : m.reg .x14=W id) (base : m.reg .x5=W heap) :
    Checked m (ops d id) := by
  have ptr : (((m.reg .x14+m.reg .x10) <<< (32:Nat)) >>> (27:Nat))+m.reg .x5=wordAddress (word d id 0) := by
    rw [key,dep,base,←BitVec.ofNat_add,index_shift _ (by omega),←BitVec.ofNat_add]
    apply congrArg W
    unfold word heap;omega
  have disp (k : Fin 4) : wordAddress (word d id 0) + signExtend12 (BitVec.ofNat 12 (8*k.val)) =
      wordAddress (word d id k.val) := by
    have offset : ∀ i : Fin 4, signExtend12 (BitVec.ofNat 12 (8*i.val))=W (8*i.val) := by decide
    rw [offset];unfold wordAddress;rw [←BitVec.ofNat_add];apply congrArg W
    unfold word;omega
  simp only [ops,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  all_goals first | (unfold word heap;omega) | skip
  all_goals change (((m.reg .x14+m.reg .x10) <<< (32:Nat)) >>> (27:Nat))+m.reg .x5+_ = _
  all_goals rw [ptr]
  · exact disp 0
  · exact disp 1
  · exact disp 2
  · exact disp 3

def finish (m : Model) (d id : Nat) := after (m.set .x14 (W id)) (ops d id)

theorem words (m : Model) (d id : Nat) :
    let t := finish m d id
    t.reg .x14=m.mem (word d id 0) ∧ t.reg .x1=m.mem (word d id 1) ∧
    t.reg .x16=m.mem (word d id 2) ∧ t.reg .x27=m.mem (word d id 3) ∧
    t.mem=m.mem ∧ ∀ r, r≠.x14 → r≠.x15 → r≠.x1 → r≠.x16 → r≠.x27 → t.reg r=m.reg r := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro r a b c e f
  simp [finish,after,ops,Op.apply,Model.set,a.symm,b.symm,c.symm,e.symm,f.symm]

theorem run (o : Oracle) (s : MachineState) (m : Model) (pc : s.pc=addr 1512) (h : Fits s m)
    (idx : Fin 512) (ids : List Nat) (slot : idx.val < ids.length) (stored : CapSlots.Contains m.mem ids)
    (d id : Nat) (which : ids[idx.val]=id) (small : id<1024) (depth : d≤9)
    (ptr : m.reg .x24=addrSlot idx.val) (dep : m.reg .x10=W d) (base : m.reg .x5=W heap) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 9 s t ∧ t.pc=addr 1521 ∧ Fits t (finish m d id) := by
  have v := loaded s m h idx ids slot stored id which small
  obtain ⟨u,r,loc,fit⟩ := first o s m h idx .x14 .x24 1512 pc (by decide) rfl ptr id v
  obtain ⟨t,endRun,endPc,endFit⟩ := OpeningStraight.block o (m.set .x14 (W id)) (ops d id) 1513
    (by change 1513+8≤1660;decide) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
    (checks _ _ _ depth small dep rfl base) u loc fit
  exact ⟨t,CommitExact.compose r endRun,endPc,endFit⟩

end CommitGolfCandidate.Reconstruction.CapLoad
