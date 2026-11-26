import CommitGolfCandidate.TruncBRowLogic
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4000
attribute [local irreducible] prefixNode lowerHash
theorem prefixFresh (H : Compression) (input : CheckInput) (n : Nat) (u : Fin 256)
    (ix : CommitGolfCandidate.openingIndex input.positions n/65536=u.val) (empty : prefixNode H input n u=none) (v : Fin 256) :
    prefixNode H input (n+1) v = if v=u then some (lowerHash H input n) else prefixNode H input n v := by
  rw [prefixNext]
  by_cases same : v=u
  · subst v;rw [empty];simp only [ix,if_true]
  · have ne : CommitGolfCandidate.openingIndex input.positions n/65536≠v.val := fun hit=>same (Fin.ext (ix.symm.trans hit)).symm
    cases e : prefixNode H input n v <;> simp [ne,same]
theorem prefixSeen (H : Compression) (input : CheckInput) (n : Nat) (u : Fin 256)
    (ix : CommitGolfCandidate.openingIndex input.positions n/65536=u.val) (d : Digest) (seen : prefixNode H input n u=some d) (v : Fin 256) :
    prefixNode H input (n+1) v=prefixNode H input n v := by
  rw [prefixNext]
  cases e : prefixNode H input n v with
  | some _ => rfl
  | none =>
    have ne : CommitGolfCandidate.openingIndex input.positions n/65536≠v.val := by
      intro hit
      have eqn : u=v := Fin.ext (ix.symm.trans hit)
      rw [eqn,e] at seen;contradiction
    simp [ne]
end CommitGolfCandidate.Trunc.Batch
