import CommitGolfCandidate.HeadStreamCheckInitial

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamFour

theorem restored_memory (k L B : Nat) (Q : Proof) (g : Word → Byte) (a : Word)
    (records : 481*k≤L) (capacity : L≤8355061248)
    (zero : ∀ q,B+2^33≤q.toNat ∧ q.toNat<B+2^33+k → g q=0) :
    insertByte k B Q
      (bodyByte k L B Q (prefixByte (B+2^33) k (fun j => BitVec.ofNat 8 (restoredHead k Q j)) g) 0) k a=
      if B≤a.toNat ∧ a.toNat<B+L then expandedByte k Q (a.toNat-B) else g a := by
  rw [insertByte,prefixByte]
  by_cases scratch : B+2^33≤a.toNat ∧ a.toNat<B+2^33+k
  · have outside : ¬(B≤a.toNat ∧ a.toNat<B+L) := by omega
    rw [if_pos scratch,if_neg outside]
    exact (zero a scratch).symm
  rw [if_neg scratch,installedByte]
  by_cases inside : B≤a.toNat ∧ a.toNat<B+L
  · rw [if_pos inside]
    by_cases head : headSlot k (a.toNat-B)
    · have installed : B≤a.toNat ∧ (a.toNat-B)/481<k ∧ (a.toNat-B)%481=45 := by
        unfold headSlot at head
        omega
      rw [if_pos installed,expandedByte,if_pos (show a.toNat-B<481*k ∧ (a.toNat-B)%481=45 from head)]
    · have absent : ¬(B≤a.toNat ∧ (a.toNat-B)/481<k ∧ (a.toNat-B)%481=45) := by
        unfold headSlot at head
        omega
      have copied : B≤a.toNat ∧ a.toNat<B+L ∧ ¬headSlot k (a.toNat-B) ∧ 0≤compactTarget k (a.toNat-B) :=
        ⟨inside.1,inside.2,head,Nat.zero_le _⟩
      rw [if_neg absent,bodyByte,if_pos copied,expandedByte,if_neg (show ¬(a.toNat-B<481*k ∧ (a.toNat-B)%481=45) from head)]
  · have absent : ¬(B≤a.toNat ∧ (a.toNat-B)/481<k ∧ (a.toNat-B)%481=45) := by omega
    have untouched : ¬(B≤a.toNat ∧ a.toNat<B+L ∧ ¬headSlot k (a.toNat-B) ∧ 0≤compactTarget k (a.toNat-B)) := by tauto
    rw [if_neg inside,if_neg absent,bodyByte,if_neg untouched,prefixByte,if_neg scratch]

end TwoPermutationPrototype.Packed.Checker.HeadRestore
