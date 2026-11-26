import CommitGolfCandidate.ReconstructedCapWordStep
import CommitGolfCandidate.ReconstructedCapEmitNode

namespace CommitGolfCandidate.Reconstruction.CapHeaderDigit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
open HonestCapTables (addrSlot scratch)
set_option maxRecDepth 16000
set_option maxHeartbeats 1900000

def neg (n : Nat) : Word := 0-W n
def addressOps : List Op := [.reg .x12 (.slli .x25 32),.reg .x12 (.srli .x12 30),.reg .x12 (.add .x9 .x12)]
def digitOps (d id : Nat) : List Op := [.reg .x12 (.add .x12 .x10),.reg .x12 (.slli .x12 32),
  .reg .x12 (.srli .x12 27),.reg .x12 (.add .x12 .x18),.ld .x12 .x12 0 (CapLoad.word d id 3),
  .reg .x16 (.mul .x16 .x31),.reg .x12 (.and .x23 .x12),.reg .x12 (.srli .x12 32),.reg .x16 (.add .x12 .x16)]
def decOps : List Op := [.reg .x25 (.addi .x25 4095)]

theorem slot_ptr (m : Model) (j : Fin 512) (counter : m.reg .x25=W j.val) (base : m.reg .x9=W scratch) :
    (after m addressOps).reg .x12=addrSlot j.val := by
  change m.reg .x9+((m.reg .x25 <<< (32:Nat)) >>> (30:Nat))=_
  rw [base,counter]
  exact (by decide +kernel : ∀ i : Fin 512, W scratch+((W i.val <<< (32:Nat)) >>> (30:Nat)) = addrSlot i.val) j

theorem checks (m : Model) (d id : Nat) (small : d≤9) (hi : id<1024) (node : m.reg .x12=W id)
    (depth : m.reg .x10=W d) (heap : m.reg .x18=W (CapLoad.heap+24)) : Checked m (digitOps d id) := by
  simp only [digitOps,Checked,Op.Valid,Op.apply,true_and,and_true]
  refine ⟨by unfold CapLoad.word CapLoad.heap;omega,?_⟩
  change (((m.reg .x12+m.reg .x10) <<< (32:Nat)) >>> (27:Nat))+m.reg .x18+0#64=_
  rw [BitVec.add_zero,node,depth,heap,←BitVec.ofNat_add,CapLoad.index_shift _ (by omega),←BitVec.ofNat_add]
  apply congrArg W;unfold CapLoad.word CapLoad.heap;omega

theorem next_counter (n : Fin 5) (pos : 0<n.val) : CapWordStep.imm (neg n.val) 1=neg (n.val-1) := by
  exact (by decide : ∀ i : Fin 5,0 < i.val → CapWordStep.imm (neg i.val) 1=neg (i.val-1)) n pos

abbrev keep : List Reg := [.x2,.x5,.x7,.x8,.x9,.x10,.x11,.x13,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x26,.x28,.x29,.x31]

structure Result (m t : Model) (digit accumulator j rem : Nat) : Prop where
  value : t.reg .x16=W (digit+211*accumulator)
  counter : t.reg .x30=neg (rem-1)
  previous : t.reg .x25=W j-1
  memory : t.mem=m.mem
  frame : ∀ r∈keep, t.reg r=m.reg r

theorem run (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1610) (fit : Fits s m)
    (d : Fin 10) (id : Nat) (j : Fin 512) (xs : List Nat) (inList : j.val < xs.length)
    (stored : CapSlots.Contains m.mem xs) (which : xs[j.val]=id) (hi : id<1024) (rem : Fin 5) (positive : 0<rem.val)
    (acc digit : Nat) (counter : m.reg .x25=W j.val) (base : m.reg .x9=W scratch)
    (depth : m.reg .x10=W d.val) (heap : m.reg .x18=W (CapLoad.heap+24)) (value : m.reg .x16=W acc)
    (radix : m.reg .x31=W 211) (remaining : m.reg .x30=neg rem.val)
    (word : ((m.reg .x23 &&& m.mem (CapLoad.word d.val id 3)) >>> (32:Nat)).toNat=digit) :
    ∃ t out, CommitExact.Segment o OpeningStraight.image 15 s t ∧ t.pc=addr 1625 ∧ Fits t out ∧
      Result m out digit acc j.val rem.val := by
  let a := after m addressOps
  obtain ⟨u,p,loc,f⟩ := OpeningStraight.block o m addressOps 1610 (by decide) ⟨rfl,rfl,rfl,True.intro⟩
    (by simp [addressOps,Checked,Op.Valid]) s pc fit
  have read := CapLoad.loaded u a f j xs inList stored id which hi
  obtain ⟨v,q,locV,fv⟩ := CapLoad.first o u a f j .x12 .x12 1613 loc (by decide) rfl (slot_ptr m j counter base) id read
  let b := a.set .x12 (W id)
  let g := after b (digitOps d.val id)
  have bound := d.isLt
  obtain ⟨t,r,locR,fr⟩ := OpeningStraight.block o b (digitOps d.val id) 1614 (by change 1614+9≤1660;decide)
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩ (checks _ _ _ (by omega) hi rfl depth heap) v locV fv
  obtain ⟨z,k,locZ,fz⟩ := CapWordStep.addiw o g t fr 1623 locR (by decide) .x30 .x30 1 rfl
  let endM := g.set .x30 (CapWordStep.imm (g.reg .x30) 1)
  obtain ⟨h,endRun,last,ff⟩ := OpeningStraight.block o endM decOps 1624 (by decide) ⟨rfl,True.intro⟩
    (by simp [decOps,Checked,Op.Valid]) z locZ fz
  refine ⟨h,_,CommitExact.compose (CommitExact.compose (CommitExact.compose (CommitExact.compose p q) r) k) endRun,last,ff,
    ?_,?_,?_,rfl,?_⟩
  · change ((m.reg .x23 &&& m.mem (CapLoad.word d.val id 3)) >>> (32:Nat)) + m.reg .x16*m.reg .x31=_
    have eq := congrArg W word
    simp only [W,BitVec.ofNat_toNat,BitVec.setWidth_eq] at eq
    rw [eq,value,radix,←BitVec.ofNat_mul,←BitVec.ofNat_add,Nat.mul_comm]
  · change CapWordStep.imm (m.reg .x30) 1=_
    rw [remaining,next_counter rem positive]
  · change m.reg .x25+signExtend12 4095=_
    rw [counter,show signExtend12 4095= -(1#64) from rfl,BitVec.sub_eq_add_neg];rfl
  · intro r member
    simp only [keep,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl

end CommitGolfCandidate.Reconstruction.CapHeaderDigit
