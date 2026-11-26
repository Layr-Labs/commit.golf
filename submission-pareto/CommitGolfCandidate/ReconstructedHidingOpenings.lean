import CommitGolfCandidate.ReconstructedHidingTrace

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
noncomputable local instance openingSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by classical exact SampleableType.ofFintype _

abbrev OpenIx (p : Finset Position) := {i : Position // i ∈ p}
abbrev ClosedIx (p : Finset Position) := {i : Position // i ∉ p}

def joinSalts (p : Finset Position) (op : OpenIx p → Salt) (cl : ClosedIx p → Salt)
    (i : Position) : Salt := if h : i ∈ p then op ⟨i,h⟩ else cl ⟨i,h⟩

def openClose (p : Finset Position) : (Position → Salt) ≃ (OpenIx p → Salt) × (ClosedIx p → Salt) where
  toFun s := (fun i => s i.val, fun i => s i.val)
  invFun pair := joinSalts p pair.1 pair.2
  left_inv s := by funext i; dsimp only [joinSalts]; split <;> rfl
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [joinSalts,i.property]
    · funext i
      simp [joinSalts,i.property]

def knownBlocks (p : Finset Position) (op : OpenIx p → Salt) (spare : Slack)
    (cl : ClosedIx p → Salt) (g : Group) : SaltBlock :=
  assemble (joinSalts p op cl) spare g.1 g.2

abbrev OpeningParts (p : Finset Position) :=
  (OpenIx p → Salt) × (ClosedIx p → Salt) × Slack × (Group → Residue)

noncomputable def splitOpening (p : Finset Position) : (Group → Reply) ≃ OpeningParts p :=
  (tapeSplit.trans ((openClose p).prodCongr (Equiv.refl _))).trans (Equiv.prodAssoc _ _ _)

theorem joined_reply (p : Finset Position) (parts : OpeningParts p) (g : Group) :
    (splitOpening p).symm parts g =
      blockSplit.symm (knownBlocks p parts.1 parts.2.2.1 parts.2.1 g, parts.2.2.2 g) := rfl

/-- The opening may be any subset of the position space. Revealing all its
salts and all spare lanes leaves the hidden salts and all generator residues
uniform and mutually independent. -/
theorem opening_distribution (p : Finset Position) :
    (splitOpening p) <$> ($ᵗ (Group → Reply)) =ᵈ ($ᵗ (OpeningParts p)) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective (splitOpening p).bijective

/-- An arbitrary transcript based on the public simulation, opened nonces and
spare lanes can make any mixture of forward and inverse guesses. -/
theorem opening_query_bound {F : Type} (p : Finset Position)
    (prior : ProbComp F) (op : F → (OpenIx p → Salt)) (spare : F → Slack)
    (latent : F → BitVec 1344 → Option Reply) (q : Nat) (queries : F → Fin q → QueryEnd) :
    Pr{let outcome ← (do let f ← prior; let h ← $ᵗ (Secrets (ClosedIx p)); pure (f,h))}[
      ∃ j, chosenHit Subtype.val (knownBlocks p (op outcome.1) (spare outcome.1))
        (latent outcome.1) (queries outcome.1 j) outcome.2] ≤ q/(2^120 : ENNReal) :=
  chosen_trace_le Subtype.val Subtype.val_injective prior (fun f => knownBlocks p (op f) (spare f))
    latent q queries

end CommitGolfCandidate.Reconstruction.HidingTape
