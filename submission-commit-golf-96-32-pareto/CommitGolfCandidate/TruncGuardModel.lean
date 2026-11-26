import CommitGolfCandidate.TruncModel
import CommitGolfCandidate.TruncCheckFetch
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 180000
def truncateAt (depth left : Nat) : Prop := left+1<depth ∧ (left≠1 ∨ depth≠24)
instance (d r : Nat) : Decidable (truncateAt d r) := inferInstanceAs (Decidable (r+1<d ∧ (r≠1 ∨ d≠24)))
def pathReply (depth left : Nat) (v : Digest) := if truncateAt depth left then padLow v else v

theorem stepMaskLevel (depth left : Nat) (mode : depth=16 ∨ depth=24) (pos : 0<left) (limit : left≤depth) (i : Index) :
    masked (((LENGTH+i.val)/2^(depth-left))/2) ↔ truncateAt depth left := by
  have small : i.val<16777216:=i.isLt
  rcases mode with rfl|rfl <;> unfold masked truncateAt <;> change _ ↔ _ <;>
    interval_cases left <;> norm_num [LENGTH,LOG_LENGTH] <;> omega

theorem pathReplyEq (depth left : Nat) (mode : depth=16 ∨ depth=24) (pos : 0<left) (limit : left≤depth) (i : Index) (v : Digest) :
    pathReply depth left v=storeNode (((LENGTH+i.val)/2^(depth-left))/2) v := by
  have equiv:=stepMaskLevel depth left mode pos limit i
  by_cases check : truncateAt depth left
  · simp only [pathReply,storeNode,if_pos check,if_pos (equiv.mpr check)]
  · simp only [pathReply,storeNode,if_neg check,if_neg (fun e=>check (equiv.mp e))]

def guardTest (s : MachineState) : Prop :=
  (s.getReg .x29+1).toNat<(s.getReg .x30).toNat ∧ (s.getReg .x29-1≠0 ∨ s.getReg .x19≠0)
instance (s : MachineState) : Decidable (guardTest s) := inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

theorem guardCorrect (s : MachineState) (d r : Nat) (mode : d=16 ∨ d=24) (pos : 0<r) (limit : r≤d)
    (counter : s.getReg .x29=BitVec.ofNat 64 r) (depth : s.getReg .x30=BitVec.ofNat 64 d)
    (cap : s.getReg .x19=0 ↔ d=24) : guardTest s ↔ truncateAt d r := by
  unfold guardTest truncateAt;rw [counter,depth]
  have small : r≤24 := by omega
  have unit : BitVec.ofNat 64 r-1=0 ↔ r=1 := by interval_cases r <;> decide
  have inc : BitVec.ofNat 64 r+1=BitVec.ofNat 64 (r+1) := (BitVec.ofNat_add r 1).symm
  have incSmall : r+1<2^64 := by omega
  have depthSmall : d<2^64 := by omega
  rw [inc,BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt incSmall,Nat.mod_eq_of_lt depthSmall]
  exact and_congr Iff.rfl (or_congr (not_congr unit) (not_congr cap))

end CommitGolfCandidate.Trunc
