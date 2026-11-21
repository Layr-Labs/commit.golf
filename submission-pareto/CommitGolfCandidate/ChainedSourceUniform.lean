import CommitGolfCandidate.ChainedFinalHazard

/-! Uniform compression sampling is compared at the event level, not as syntax. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec

theorem source_uniform_event (input : CompressionSpec.Domain) (event : Output → Prop) :
    Pr{let reply ← $ᵗ CompressionSpec.Range input}[event reply] =
      Pr{let reply ← $ᵗ Output}[event reply] := by
  exact SampleableType.prEvent_uniformSample_inst_irrel
    (inferInstanceAs (SampleableType (CompressionSpec.Range input)))
    (inferInstanceAs (SampleableType Output)) event

end CommitGolfCandidate.Chained
