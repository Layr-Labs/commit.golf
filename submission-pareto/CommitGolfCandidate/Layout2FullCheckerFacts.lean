import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.Layout2Abstract
import CommitGolfCandidate.Layout2OneByteDecode
import CommitGolfCandidate.Layout2V1DeliveredData

/-! # The one-byte checker's facts for the full encoding `Cap.encoder`

The check image is 98b5b7e9's (the one-byte search); the opener keeps the final byte, so its encoding is
`Cap.encoder`. This is the "byte kept" case of `K1Check.checker_facts_onebyte_for` alone. `full_checker_facts`
instantiates it with the delivered V1 tables (`decTables`); `Cap.decoder` is their conversion. -/
namespace CommitGolf.K1Check
open CommitGolfCandidate TwoPermutationPrototype
open TwoPermutationPrototype.QuartetCertificate (CheckerFactsEnc honestCheckInput honestCheckInputEnc)

/-- The one-byte checker's facts for the full encoding `Cap.encoder` (the opener keeps every byte). Termination, the
query budget and binding are as above. Honest acceptance is the "byte kept" case of `checker_facts_onebyte_for`: an
honest encoding has `534 k + C(f)` bytes, which is even, so it is never 72,159 bytes long; the checker's entry guard
does not fire and the decoder gives the honest input back (`decode_encode`). -/
theorem checker_facts_full_for (τ : Layout2.Tables) (wf : Layout2.WellFormed τ)
    (physical : ∀ k, k<85440 → CommitGolfCandidate.Layout2Helpers.pget K1Artifact.checkData k=Layout2.tableByte τ k)
    (decodes : ∀ p P, Layout2.convert τ p.card (Layout2.Quartet.normalize p (Layout2.Cap.transform Layout2.Cap.dec p.card P)) =
      Layout2.Cap.decoder p P) :
    CheckerFactsEnc Layout2.Cap.encoder K1Artifact.submission := by
  have checked := Packed.Checker.executable_converted_observation τ wf physical
  have inputEq (X : CheckInput) : Layout2.converted τ (Layout2.Quartet.prepared (Layout2.Cap.prepared X)) =
      { X with proof := Layout2.Cap.decoder X.positions X.proof } := by
    show ({ X with proof := Layout2.convert τ X.positions.card (Layout2.Quartet.normalize X.positions
      (Layout2.Cap.transform Layout2.Cap.dec X.positions.card X.proof)) } : CheckInput) = _
    rw [decodes]
  refine ⟨fun o i => (checked o i).terminates, ?_, Packed.Checker.binding_of_decoder τ wf physical, ?_⟩
  · intro oracle i
    have calls := (checked oracle i).queries
    change _ ≤ 41*i.positions.card at calls
    omega
  · intro o m p s
    let base := honestCheckInput o m p s
    let H := base.proof
    let i := honestCheckInputEnc Layout2.Cap.encoder o m p s
    have encLen : (Layout2.Cap.encoder p H).length = H.length := by simp [Layout2.Cap.encoder]
    have hlen : H.length = 534*p.card + (30*(Opening.openingNodes p).length - 2*((Opening.openingNodes p).length/8)) :=
      PackedHonest.honest_proof_length o m p s
    have obs := checked o i
    have iproof : i.proof = Layout2.Cap.encoder p H := rfl
    have nofire : ¬ Layout2.Cap.fires i := by
      rintro ⟨c, l⟩
      have c' : p.card = 128 := c
      rw [iproof, encLen, hlen] at l
      omega
    rw [Layout2.Cap.effective_not _ nofire] at obs
    have e : Layout2.converted τ (Layout2.Quartet.prepared (Layout2.Cap.prepared i)) = base := by
      rw [inputEq, iproof]
      show ({ base with proof := Layout2.Cap.decoder p (Layout2.Cap.encoder p H) } : CheckInput) = base
      rw [Layout2.Cap.decode_encode p H (Layout2.Cap.honest_good' o m p s)]
    exact obs.honest m s e

theorem full_checker_facts : CheckerFactsEnc CommitGolfCandidate.Layout2.Cap.encoder K1Artifact.submission :=
  checker_facts_full_for Layout2.decTables Layout2.v1_delivered_wellFormed Layout2.v1_physical (fun _ _ => rfl)

end CommitGolf.K1Check
