import CommitGolfCandidate.ReconstructedHidingInverse

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
set_option maxHeartbeats 2000000
noncomputable local instance traceSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by classical exact SampleableType.ofFintype _
local instance traceDiscrete {α : Type} : MeasurableSpace α := ⊤
attribute [local irreducible] blockSplit

abbrev Secrets (I : Type) := (Key × (I → Salt)) × (Group → Residue)

inductive QueryEnd where
  | forward (input : Reply)
  | inverse (output : Reply)
  | other

def chosenHit {I : Type} (position : I → Position) (blocks : (I → Salt) → Group → SaltBlock)
    (latent : BitVec 1344 → Option Reply) (query : QueryEnd) (secret : Secrets I) : Prop :=
  let key := secret.1.1
  let salts := secret.1.2
  let residue := secret.2
  match query with
  | .other => False
  | .forward x => keyHit x key ∨ tagHit position x salts
  | .inverse y => (∃ a, latent (outputTail y) = some a ∧ tagHit position a salts) ∨
      (Function.Injective (blocks salts) ∧
        (∀ g, ∀ hi, (latent hi).isSome → signature (blocks salts g) ≠ tailSignature hi) ∧
        ∃ g, blockSplit.symm (blocks salts g, residue g) = y)

theorem chosen_endpoint_le {I : Type} [Fintype I] [DecidableEq I]
    (position : I → Position) (unique : Function.Injective position)
    (blocks : (I → Salt) → Group → SaltBlock) (latent : BitVec 1344 → Option Reply)
    (query : QueryEnd) :
    Pr{let secrets ← $ᵗ (Secrets I)}[chosenHit position blocks latent query secrets]
      ≤ 1/(2^120 : ENNReal) := by
  cases query with
  | other =>
    rw [(SampleableType.prEvent_uniformSample_eq_zero_iff _).2 (fun _ h => h.elim)]
    exact zero_le
  | forward x =>
    apply SampleableType.prEvent_uniformSample_prod_le_of_forall_snd
    intro _
    exact forward_guess_le position unique x
  | inverse y =>
    let risk := fun (p : (I → Salt) × (Group → Residue)) =>
      (∃ a, latent (outputTail y) = some a ∧ tagHit position a p.1) ∨
      (Function.Injective (blocks p.1) ∧
        (∀ g, ∀ hi, (latent hi).isSome → signature (blocks p.1 g) ≠ tailSignature hi) ∧
        ∃ g, blockSplit.symm (blocks p.1 g,p.2 g) = y)
    have reassoc := SampleableType.prEvent_uniformSample_equiv (Equiv.prodAssoc Key (I → Salt) (Group → Residue))
      (fun p => risk p.2)
    refine reassoc.le.trans ?_
    apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
    intro _
    exact joint_inverse_guess position unique blocks latent y

/-- The oracle simulation and the public openings may generate a random trace.
After conditioning on those public data, unused nonces, generator residues
and the key remain independent draws in this reference calculation. -/
theorem chosen_trace_le {I F : Type} [Fintype I] [DecidableEq I]
    (position : I → Position) (unique : Function.Injective position)
    (prior : ProbComp F) (blocks : F → (I → Salt) → Group → SaltBlock)
    (latent : F → BitVec 1344 → Option Reply)
    (q : Nat) (trace : F → Fin q → QueryEnd) :
    Pr{let result ← (do let f ← prior; let secrets ← $ᵗ (Secrets I); pure (f,secrets))}[
      ∃ j, chosenHit position (blocks result.1) (latent result.1) (trace result.1 j) result.2]
      ≤ q/(2^120 : ENNReal) := by
  apply prEvent_bind_le_of_forall_le_of_support
  intro f _
  rw [bind_pure_comp,prEvent_map]
  refine (prEvent_exists_le_card_mul _ _ (fun j => chosen_endpoint_le position unique (blocks f)
    (latent f) (trace f j))).trans_eq ?_
  simp only [Fintype.card_fin,mul_one_div]

end CommitGolfCandidate.Reconstruction.HidingTape
