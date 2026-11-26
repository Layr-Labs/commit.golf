import CommitGolfCandidate.ReconstructedCapLoad

namespace CommitGolfCandidate.Reconstruction.CapLowStart
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut
open TwoPermutationPrototype.RV64
open CommitBlocks (addr)
set_option maxRecDepth 12000

def ops : List Op := [.reg .x26 (.andi .x7 63),.reg .x15 (.srli .x7 3),.reg .x15 (.andi .x15 4088),
  .reg .x6 (.add .x15 .x17),.reg .x15 (.addi .x7 64),.reg .x30 (.addi .x7 128)]

theorem values (m : Model) (c : Nat) (fit : c<2^64) (cursor : m.reg .x7=W c) (baseReg : m.reg .x17=wordAddress base) :
    let t := after m ops
    t.reg .x26=W (c%64) ∧ t.reg .x6=wordAddress (cell c) ∧ t.reg .x15=W (c+64) ∧
    t.reg .x30=W (c+128) ∧ t.mem=m.mem ∧ ∀ r, r≠.x26 → r≠.x6 → r≠.x15 → r≠.x30 → t.reg r=m.reg r := by
  refine ⟨?_,?_,?_,?_,rfl,?_⟩
  · change m.reg .x7 &&& signExtend12 63=_
    rw [cursor,offset]
  · change ((m.reg .x7 >>> (3:Nat)) &&& signExtend12 4088)+m.reg .x17=_
    rw [cursor,baseReg,word_address _ fit]
  · change m.reg .x7+signExtend12 64=_
    rw [cursor];exact (BitVec.ofNat_add ..).symm
  · change m.reg .x7+signExtend12 128=_
    rw [cursor];exact (BitVec.ofNat_add ..).symm
  · intro r a b d e
    simp [after,ops,Op.apply,Model.set,a.symm,b.symm,d.symm,e.symm]

theorem run (o : Oracle) (m : Model) (s : MachineState) (pc : s.pc=addr 1521) (fits : Fits s m)
    (c : Nat) (bound : c<2^64) (cursor : m.reg .x7=W c) (baseReg : m.reg .x17=wordAddress base) :
    ∃ t, CommitExact.Segment o OpeningStraight.image 7 s t ∧ t.pc=(if c%64=0 then addr 1562 else addr 1528) ∧
      Fits t (after m ops) := by
  obtain ⟨u,pre,upc,uf⟩ := OpeningStraight.block o m ops 1521 (by decide)
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,True.intro⟩ (by simp [ops,Checked,Op.Valid]) s pc fits
  have off := (values m c bound cursor baseReg).1
  have jump := zero_branch o u 1527 1528 1562 .x26 140 upc (by decide) rfl rfl rfl (W (c%64)) ((uf.registers _).trans off)
  have test : W (c%64)=0 ↔ c%64=0 := by
    constructor
    · intro eq;have n := congrArg BitVec.toNat eq;change (c%64)%2^64=0 at n;omega
    · intro eq;rw [eq];rfl
  simp only [test] at jump
  exact ⟨_,CommitExact.compose pre jump,rfl,uf.pc _⟩

end CommitGolfCandidate.Reconstruction.CapLowStart
