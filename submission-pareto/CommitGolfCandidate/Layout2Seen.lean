import CommitGolfCandidate.GroupOpenStep
import CommitGolfCandidate.GroupOpenVirtual
import CommitGolfCandidate.GroupOpenInitial
import CommitGolfCandidate.K3OpenReply
import CommitGolfCandidate.Layout2Phase
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.K1OpenSalt

/-! Layout 2 V2 record blocks, pure definitions shared by the opener's bridge (`Layout2V2Ref`, `Layout2V2Bridge`) and
the fused loop (`Layout2FusedLoop`): the sorted positions (`pos`), the block geometry (`passDest`, `passWord`), the
linked salts, and `Seen` (a state whose record blocks hold each record's linked salt in words 0..1 and the inverse of
its quartet's reply in words 3..24). These were part of the V2a/V2b first pass (`Layout2Pass`, `Layout2PassStep`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening
open Opening (sortedIndex)
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Start of record `j`'s block (`Layout2.destOf j`). -/
def passDest (j : Nat) : Nat := proofBase+2136*(j/4)+CommitGolfCandidate.Layout2Phase.phaseBase (j%4)
/-- Its word index. -/
def passWord (j : Nat) : Nat := passDest j/8

theorem pass_dest_aligned (j : Nat) : passDest j%8=0 := by
  have hp : proofBase%8=0 := by decide
  unfold passDest CommitGolfCandidate.Layout2Phase.phaseBase; split_ifs <;> omega

theorem pass_word_mul (j : Nat) : 8*passWord j=passDest j := by
  have := pass_dest_aligned j; unfold passWord; omega

def pos (p : Positions) (j : Nat) : Index := ((p.sort (·≤·))[j]?).getD ⟨0,by decide⟩
theorem pos_present (p : Positions) (j : Nat) (hj : j<p.card) : pos p j=sortedIndex p j hj := by
  unfold pos sortedIndex;rw [List.getElem?_eq_getElem (by simpa using hj)];rfl

theorem card_le (p : Positions) : p.card≤16777216 := by change p.card≤LENGTH;simpa [Index] using Finset.card_le_univ p

/-- The linked (chained) salt array under the oracle's permutation and key `k`. -/
noncomputable abbrev linkedSalts (o : Oracle) (k : BitVec 192) :=
  Permutation.LinkedSalt.salts (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period) o.permutation k

/-- After the first `n` records: each record block holds its linked salt (words 0..1) and the inverse of its
quartet's reply (words 3..24). -/
structure Seen (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) (n : Nat) : Prop where
  salt : ∀ a<n, ∀ j : Fin 2, memoryView s (passWord a+j.val)=saltWords (linkedSalts o k (pos p a)) j
  reply : ∀ a<n, ∀ m (hm : m<25), 3≤m → memoryView s (passWord a+m)=
    replyWords (o.permutation.symm (groupReply td ((pos p a).val/4))) ⟨m,hm⟩

theorem seen_zero (o : Oracle) (k : BitVec 192) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)
    (s : MachineState) : Seen o k td p s 0 := ⟨fun _ h => absurd h (Nat.not_lt_zero _),fun _ h => absurd h (Nat.not_lt_zero _)⟩

end TwoPermutationPrototype.GroupedOpening.Layout2V2
