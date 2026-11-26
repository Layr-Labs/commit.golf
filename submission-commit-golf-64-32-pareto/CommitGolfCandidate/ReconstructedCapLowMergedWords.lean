import CommitGolfCandidate.ReconstructedCapLowCore

namespace CommitGolfCandidate.Reconstruction.CapLowMergedWords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel OpeningOps OpeningQuery OpeningCursor OpeningPut CapLowCore
open TwoPermutationPrototype (writeWord)
open TwoPermutationPrototype.RV64
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

def aOps (c : Nat) : List Op := [.ld .x29 .x6 0 (cell c),.reg .x12 (.sll .x14 .x26),.reg .x12 (.or .x29 .x12),
  .reg .x29 (.subw .x0 .x26),.reg .x14 (.srl .x14 .x29),.sd .x6 .x14 8 (cell c+1),.sd .x6 .x12 0 (cell c)]
def bOps (c : Nat) : List Op := [.reg .x15 (.srli .x15 3),.reg .x15 (.andi .x15 4088),.reg .x15 (.add .x15 .x17),
  .ld .x12 .x15 0 (cell c),.reg .x14 (.sll .x1 .x26),.reg .x12 (.or .x12 .x14),
  .reg .x14 (.srl .x1 .x29),.sd .x15 .x14 8 (cell c+1),.sd .x15 .x12 0 (cell c)]
def cOps (c : Nat) : List Op := [.reg .x12 (.srli .x30 3),.reg .x12 (.andi .x12 4088),.reg .x12 (.add .x12 .x17),
  .ld .x14 .x12 0 (cell c),.reg .x7 (.addi .x7 192),.reg .x15 (.sll .x16 .x26),.reg .x14 (.or .x14 .x15),
  .reg .x15 (.srl .x16 .x29),.sd .x12 .x15 8 (cell c+1),.sd .x12 .x14 0 (cell c)]

def signed (m : Model) := ((m.reg .x0).truncate 32-(m.reg .x26).truncate 32).signExtend 64

theorem amount (n : Nat) : (W (n%64)).toNat%64=n%64 := by change ((n%64)%2^64)%64=n%64;omega

theorem shift (m : Model) (c : Nat) (off : m.reg .x26=W (c%64)) (nz : c%64≠0) (zero : m.reg .x0=0) :
    (signed m).toNat%64=64-c%64 := by
  unfold signed;rw [off,zero];exact negative_shift ⟨c%64,Nat.mod_lt _ (by decide)⟩ (Nat.pos_of_ne_zero nz)

theorem a (m : Model) (c : Nat) (hi : cell c+1<2^33) (ptr : m.reg .x6=wordAddress (cell c))
    (zero : m.reg .x0=0) (off : m.reg .x26=W (c%64)) (nz : c%64≠0) :
    Checked m (aOps c) ∧ (after m (aOps c)).mem=put m.mem c 64 (m.reg .x14) ∧
    ((after m (aOps c)).reg .x29).toNat%64=64-c%64 := by
  have first : m.reg .x6+signExtend12 0=wordAddress (cell c) := by rw [ptr];exact BitVec.add_zero _
  have second : m.reg .x6+signExtend12 8=wordAddress (cell c+1) := by rw [ptr,wordAddress_add];rfl
  have sh := shift m c off nz zero
  refine ⟨?_,?_,sh⟩
  · simp only [aOps,Checked,Op.Valid,Op.apply,true_and,and_true]
    exact ⟨⟨by omega,first⟩,⟨hi,second⟩,⟨by omega,first⟩⟩
  · change writeWord (writeWord m.mem (cell c+1) (m.reg .x14 >>> ((signed m).toNat%64))) (cell c)
      (m.mem (cell c) ||| (m.reg .x14 <<< ((m.reg .x26).toNat%64)))=_
    rw [sh,off,amount,CapWriter.reverse_stores _ _ _ nz]

theorem ptrs (m : Model) (src : Reg) (c : Nat) (hi : c<2^64) (cursor : m.reg src=W c)
    (baseReg : m.reg .x17=wordAddress base) :
    let dst := ((m.reg src >>> (3:Nat)) &&& signExtend12 4088)+m.reg .x17
    dst+signExtend12 0=wordAddress (cell c) ∧ dst+signExtend12 8=wordAddress (cell c+1) := by
  dsimp only
  rw [cursor,baseReg,word_address c hi]
  exact ⟨BitVec.add_zero _,by rw [wordAddress_add];rfl⟩

theorem b (m : Model) (c : Nat) (hi : cell c+1<2^33) (bound : c<2^64) (cursor : m.reg .x15=W c)
    (baseReg : m.reg .x17=wordAddress base) (shift : (m.reg .x29).toNat%64=64-c%64)
    (off : m.reg .x26=W (c%64)) (nz : c%64≠0) :
    Checked m (bOps c) ∧ (after m (bOps c)).mem=put m.mem c 64 (m.reg .x1) := by
  obtain ⟨first,second⟩ := ptrs m .x15 c bound cursor baseReg
  constructor
  · simp only [bOps,Checked,Op.Valid,Op.apply,true_and,and_true]
    exact ⟨⟨by omega,first⟩,⟨hi,second⟩,⟨by omega,first⟩⟩
  · change writeWord (writeWord m.mem (cell c+1) (m.reg .x1 >>> ((m.reg .x29).toNat%64))) (cell c)
      (m.mem (cell c) ||| (m.reg .x1 <<< ((m.reg .x26).toNat%64)))=_
    rw [shift,off,amount,CapWriter.reverse_stores _ _ _ nz]

theorem third (m : Model) (c : Nat) (hi : cell c+1<2^33) (bound : c<2^64) (cursor : m.reg .x30=W c)
    (baseReg : m.reg .x17=wordAddress base) (shift : (m.reg .x29).toNat%64=64-c%64)
    (off : m.reg .x26=W (c%64)) (nz : c%64≠0) :
    Checked m (cOps c) ∧ (after m (cOps c)).mem=put m.mem c 64 (m.reg .x16) := by
  obtain ⟨first,second⟩ := ptrs m .x30 c bound cursor baseReg
  constructor
  · simp only [cOps,Checked,Op.Valid,Op.apply,true_and,and_true]
    exact ⟨⟨by omega,first⟩,⟨hi,second⟩,⟨by omega,first⟩⟩
  · change writeWord (writeWord m.mem (cell c+1) (m.reg .x16 >>> ((m.reg .x29).toNat%64))) (cell c)
      (m.mem (cell c) ||| (m.reg .x16 <<< ((m.reg .x26).toNat%64)))=_
    rw [shift,off,amount,CapWriter.reverse_stores _ _ _ nz]

end CommitGolfCandidate.Reconstruction.CapLowMergedWords
