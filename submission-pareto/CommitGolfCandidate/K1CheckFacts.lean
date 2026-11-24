import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.Layout2Abstract
import CommitGolfCandidate.Layout2OneByteDecode

/-! # The one-byte checker's facts for the opener's encoding `Cap.obEnc`

Termination, the query budget (41 k ≤ 100 k) and binding come from the observation facts of every input. Honest
acceptance splits on `obEnc`: when it drops the final byte (`k = 128` and a 72,160-byte encoding), the checker's
guard pads it back with a zero byte and the decoder gives `nearCheckInput` (`near_decode`), which the cap search
accepts (`nearHonest`); otherwise the honest encoding is not 72,159 bytes long (parity), the guard does not fire, and
the decoder gives the honest input back (`decode_encode`). -/
namespace CommitGolf.K1Check
open CommitGolfCandidate TwoPermutationPrototype
open TwoPermutationPrototype.QuartetCertificate (CheckerFactsEnc honestCheckInput honestCheckInputEnc)
open TwoPermutationPrototype.Packed.Checker (nearCheckInput honestNodes)

theorem checker_facts_onebyte_for (τ : Layout2.Tables) (wf : Layout2.WellFormed τ)
    (physical : ∀ k, k<85440 → CommitGolfCandidate.Layout2Helpers.pget K1Artifact.checkData k=Layout2.tableByte τ k)
    (decodes : ∀ p P, Layout2.convert τ p.card (Layout2.Quartet.normalize p (Layout2.Cap.transform Layout2.Cap.dec p.card P)) =
      Layout2.Cap.decoder p P) :
    CheckerFactsEnc Layout2.Cap.obEnc K1Artifact.submission := by
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
    let i := honestCheckInputEnc Layout2.Cap.obEnc o m p s
    have encLen : (Layout2.Cap.encoder p H).length = H.length := by simp [Layout2.Cap.encoder]
    have hlen : H.length = 534*p.card + (30*(Opening.openingNodes p).length - 2*((Opening.openingNodes p).length/8)) :=
      PackedHonest.honest_proof_length o m p s
    have nb := Opening.opening_nodes_bound p
    have obs := checked o i
    by_cases hd : p.card = 128 ∧ (Layout2.Cap.encoder p H).length = 72160
    · have iproof : i.proof = (Layout2.Cap.encoder p H).take 72159 := by
        show Layout2.Cap.obEnc p H = _
        unfold Layout2.Cap.obEnc
        rw [if_pos hd]
      have fires : Layout2.Cap.fires i := by
        refine ⟨hd.1, ?_⟩
        rw [iproof, List.length_take, hd.2]
        decide
      rw [Layout2.Cap.effective_fires _ fires] at obs
      have positive : p.card ≠ 0 := by omega
      have f128 : (honestNodes o m p s).length = 128 := by
        unfold honestNodes
        rw [List.length_map, ← Checker.checker_honest_cap_nodes p positive]
        have l := hd.2
        rw [encLen, hlen, hd.1] at l
        omega
      have e : Layout2.converted τ (Layout2.Quartet.prepared (Layout2.Cap.prepared (Layout2.Cap.pad i))) =
          nearCheckInput o m p s := by
        rw [inputEq]
        have pp : (Layout2.Cap.pad i).proof = (Layout2.Cap.encoder p H).take 72159 ++ [0] := by
          show i.proof ++ [0] = _
          rw [iproof]
        rw [pp]
        show ({ base with proof := Layout2.Cap.decoder p ((Layout2.Cap.encoder p H).take 72159 ++ [0]) } :
          CheckInput) = _
        rw [Layout2.Cap.near_decode o m p s hd.1 f128]
        rfl
      exact obs.nearHonest m s e hd.1 f128
    · have iproof : i.proof = Layout2.Cap.encoder p H := by
        show Layout2.Cap.obEnc p H = _
        unfold Layout2.Cap.obEnc
        rw [if_neg hd]
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

end CommitGolf.K1Check
