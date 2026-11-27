import CommitGolfCandidate.Stage3cCheckRecordInput
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def saltJump (b : Bool) := if b then 237 else 1117
def saltCost (b : Bool) :=if b then 438 else 7
structure SaltGot (o : Oracle) (x : CheckInput) (s t : MachineState) (b : Bool) (r steps : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt (saltJump b)
  data : readBuffer t saltBuf 24=(view b x).salt r
  mem : Outside s t saltBuf 32
  cursor : WireCursor b x t (peerBit r 0) (peerOffset r 0)
  keep : ∀ q,peerKeep q→t.getReg q=s.getReg q

private theorem low_salt (n : Nat) : (BitVec.ofNat 256 n).extractLsb' 0 192=BitVec.ofNat 192 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,BitVec.toNat_ofNat,Nat.shiftRight_zero]
  exact Nat.mod_mod_of_dvd n (pow_dvd_pow 2 (by decide : 192≤256))
attribute [local irreducible] Pw.packedInput Pw.atProof Reader.window readBuffer
theorem salt_window (x : CheckInput) (r : Nat) :
    (wireValue true x (3780*r) (792*r) 192).extractLsb' 0 192=(view true x).salt r := by
  simp only [wireValue,view,Pw.batchView,Reader.decoded,ite_true,↓reduceIte]
  exact low_salt _
end CommitGolfCandidate.Chained.BinaryMachine.Check
