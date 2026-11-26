import CommitGolfCandidate.ReconstructedOpeningSaltLow

namespace CommitGolfCandidate.Reconstruction.OpeningHeaderLow
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery
open TwoPermutationPrototype.RV64 OpeningPut OpeningCursor TwoPermutationPrototype
open CommitBlocks (addr)
set_option maxRecDepth 12000

def beginOps : List Op := [.reg .x13 (.andi .x19 63),.reg .x12 (.srli .x19 3),.reg .x12 (.andi .x12 4088),
  .reg .x19 (.add .x12 .x25),.reg .x12 (.addi .x18 0)]
def spillOps (c : Nat) : List Op := [.ld .x5 .x19 0 (cell c),.reg .x12 (.sll .x18 .x13),.reg .x12 (.or .x5 .x12),
  .reg .x13 (.subw .x0 .x13),.reg .x13 (.srl .x18 .x13),.sd .x19 .x13 8 (cell c+1)]
def pending (m : Memory) (c : Nat) (v : Word) :=
  if c%64=0 then m else writeWord m (cell c+1) (v >>> (64-c%64))

theorem finish (m : Memory) (c : Nat) (v : Word) :
    writeWord (pending m c v) (cell c) (first m c v) = put m c 64 v := by
  unfold pending put
  by_cases z : c%64=0
  · simp only [z,ite_true,Nat.zero_add,lt_self_iff_false,ite_false]
  · simp only [z,ite_false,ite_eq_left (show 64<c%64+64 by omega)]
    funext w
    by_cases eq : w=cell c
    · subst w;simp [writeWord]
    · simp only [writeWord,eq,ite_false]

structure Staged (m q : Model) (c : Nat) : Prop where
  dst : q.reg .x19=wordAddress (cell c)
  current : q.reg .x12=first m.mem c (m.reg .x18)
  memory : q.mem=pending m.mem c (m.reg .x18)
  frame : ∀ r, r≠.x5 → r≠.x12 → r≠.x13 → r≠.x19 → q.reg r=m.reg r

theorem stage (o : Oracle) (m : Model) (c : Nat) (room : c/64<capacity) (cursor : m.reg .x19=W c)
    (baseReg : m.reg .x25=wordAddress base) (zero : m.reg .x0=0)
    (s : MachineState) (pc : s.pc=addr 345) (fits : Fits s m) :
    ∃ t q, CommitExact.Segment o OpeningStraight.image (if c%64=0 then 6 else 12) s t ∧ t.pc=addr 357 ∧
      Fits t q ∧ Staged m q c := by
  let a := after m beginOps
  have beginTable : OpeningStraight.Listed 345 (beginOps.map Op.instr) := ⟨rfl,rfl,rfl,rfl,rfl,True.intro⟩
  obtain ⟨u,ru,pu,hu⟩ := OpeningStraight.block o m beginOps 345 (by decide) beginTable
    (by simp [beginOps,Checked,Op.Valid]) s pc fits
  have off : a.reg .x13=W (c%64) := by change m.reg .x19 &&& signExtend12 63=_;rw [cursor,offset]
  have dst : a.reg .x19=wordAddress (cell c) := by
    change ((m.reg .x19 >>> (3 : Nat)) &&& signExtend12 4088)+m.reg .x25=_
    rw [cursor,baseReg,word_address c (by unfold capacity at room;omega)]
  have copied : a.reg .x12=m.reg .x18 := BitVec.add_zero _
  have step := zero_branch o u 350 351 357 .x13 28 pu (by decide) rfl rfl rfl (W (c%64)) ((hu.registers _).trans off)
  have eqv : W (c%64)=0 ↔ c%64=0 := by
    constructor
    · intro e;have n := congrArg BitVec.toNat e;change (c%64)%2^64=0 at n;omega
    · intro e;rw [e];rfl
  simp only [eqv] at step
  have frame (r : Reg) (t : r≠.x12) (p : r≠.x13) (d : r≠.x19) : a.reg r=m.reg r := by
    simp [a,after,beginOps,Op.apply,Model.set,t.symm,p.symm,d.symm]
  by_cases z : c%64=0
  · simp only [z,ite_true] at step ⊢
    exact ⟨_,a,CommitExact.compose ru step,rfl,hu.pc _,dst,by simpa only [first,z,ite_true] using copied,
      by simp only [pending,z,ite_true];rfl,fun r _ p q t => frame r p q t⟩
  · simp only [z,ite_false] at step ⊢
    have space := OpeningSaltLow.room c room
    have ck : Checked a (spillOps c) := by
      simp only [spillOps,Checked,Op.Valid,Op.apply,true_and,and_true]
      refine ⟨⟨by omega,?_⟩,⟨space,?_⟩⟩
      · rw [dst];exact BitVec.add_zero _
      · change a.reg .x19+signExtend12 8=_
        rw [dst,wordAddress_add];rfl
    have table : OpeningStraight.Listed 351 ((spillOps c).map Op.instr) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩
    obtain ⟨t,rt,pt,ht⟩ := OpeningStraight.block o a (spillOps c) 351 (by change 351+6≤1660;decide) table ck (u.setPC _) rfl (hu.pc _)
    let q := after a (spillOps c)
    have ord : (a.reg .x13).toNat%64=c%64 := by rw [off];change ((c%64)%2^64)%64=c%64;omega
    have sh := negative_shift ⟨c%64,by omega⟩ (Nat.pos_of_ne_zero z)
    refine ⟨t,q,CommitExact.compose (CommitExact.compose ru step) rt,pt,ht,dst,?_,?_,?_⟩
    · change a.mem (cell c) ||| (a.reg .x18 <<< ((a.reg .x13).toNat%64))=_
      rw [ord,first,ite_eq_right z];rfl
    · change writeWord a.mem (cell c+1) (a.reg .x18 >>> ((((a.reg .x0).truncate 32-
         (a.reg .x13).truncate 32).signExtend 64).toNat%64))=_
      rw [show a.reg .x0=0 from zero,off,pending,ite_eq_right z]
      exact congrArg (fun n : Nat => writeWord a.mem (cell c+1) (a.reg .x18 >>> n)) sh
    · intro r t d p g
      exact (show q.reg r=a.reg r by simp [q,after,spillOps,Op.apply,Model.store,Model.set,t.symm,d.symm,p.symm]).trans
        (frame r d p g)

end CommitGolfCandidate.Reconstruction.OpeningHeaderLow
