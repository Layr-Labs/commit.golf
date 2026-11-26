import CommitGolfCandidate.S5CheckViewIndex
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
attribute [local irreducible] S5.atProof S5.packedInput readBuffer S5.complete S5.layerBits Reader.window S5.bits
theorem wire_peer (x : CheckInput) (b : Bool) (r h : Nat) :
    wireValue b x (peerBit r h) (peerOffset r h) (S5.bits h)=((view b x).peers r h).1 := by
  cases b
  · simp only [wireValue,view,S5.plainView,peerOffset,Bool.false_eq_true,ite_false,ite_true,↓reduceIte]
  · simp only [wireValue,view,S5.batchView,Reader.decoded,peerBit,↓reduceIte]
    rw [show (0 : Fin 4).val=0 from rfl,packed_zero]
theorem wire_bottom_peer (x : CheckInput) (b : Bool) (r : Nat) :
    wireValue b x (peerBit r 0+256) (peerOffset r 0+32) 256=((view b x).peers r 0).2 := by
  cases b
  · simp only [wireValue,view,S5.plainView,peerOffset,Bool.false_eq_true,ite_false,ite_true,↓reduceIte]
  · simp only [wireValue,view,S5.batchView,Reader.decoded,peerBit,↓reduceIte]
    rw [show (0 : Fin 4).val=0 from rfl,packed_zero]
end CommitGolfCandidate.S5Machine.Check
