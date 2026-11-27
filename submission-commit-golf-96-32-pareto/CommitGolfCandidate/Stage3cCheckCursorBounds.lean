import CommitGolfCandidate.Stage3cCursorFrame
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def peerBit (r h : Nat) :=3780*r+Pw.layerBits h
def peerOffset (r h : Nat) :=792*r+24+32*h
def view (batch : Bool) (x : CheckInput) := if batch then Pw.batchView x else Pw.plainView x
end CommitGolfCandidate.Chained.BinaryMachine.Check
