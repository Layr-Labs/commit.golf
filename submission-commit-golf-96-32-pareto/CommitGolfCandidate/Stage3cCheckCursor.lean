import CommitGolfCandidate.Stage3cCheckViewIndex
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
attribute [local irreducible] Pw.atProof Pw.packedInput readBuffer Pw.layerBits Reader.window Pw.bits
theorem wire_peer (x : CheckInput) (b : Bool) (r h : Nat) :
    wireValue b x (peerBit r h) (peerOffset r h) (Pw.bits h)=((view b x).peers r h).1 := by
  cases b
  · simp only [wireValue,view,Pw.plainView,peerOffset,Bool.false_eq_true,ite_false,ite_true,↓reduceIte]
  · simp only [wireValue,view,Pw.batchView,Reader.decoded,peerBit,↓reduceIte]
end CommitGolfCandidate.Chained.BinaryMachine.Check
