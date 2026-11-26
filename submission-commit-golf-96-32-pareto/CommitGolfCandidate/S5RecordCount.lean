import CommitGolfCandidate.S5OrdinaryLoop
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape)
def ordinaryCost (xs : List Index) : Nat→Nat→Nat
  | _,0=>0
  | r,n+1=>(if (ix xs r).val%2=0 then 488 else 487)+ordinaryCost xs (r+1) n

theorem ordinary_cost_bound (xs : List Index) (r n : Nat) : ordinaryCost xs r n≤488*n := by
  induction n generalizing r with
  | zero=>simp [ordinaryCost]
  | succ n ih=>have tail:=ih (r+1);rw [ordinaryCost,Nat.mul_succ];split <;> omega

structure OrdinaryRegs (s : MachineState) (r k dst : Nat) : Prop where
  pc : s.pc=pcAt (if r<k then 501 else 989)
  table : s.getReg .x3=W 2048
  indices : s.getReg .x9=W (indexBase+8*r)
  remaining : s.getReg .x22=W (k-r)
  salts : s.getReg .x20=W rowBase
  radix : s.getReg .x25=3
  proof : s.getReg .x18=W proofBase
  dest : s.getReg .x19=W dst

attribute [local irreducible] afterLatch readBuffer ix
set_option maxHeartbeats 300000

def perRecord (xs : List Index) (r : Nat) := if (ix xs r).val%2=0 then 488 else 487

end CommitGolfCandidate.S5Machine.Open
