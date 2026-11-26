import CommitGolfCandidate.ReconstructedHidingIntegrate

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp TwoPermutationPrototype.Sampling

theorem uniform_versions {X : Type} {sa sb : SampleableType X} (p : X → Prop) :
    (Pr{let x ← @uniformSample X sa}[p x]) = (Pr{let x ← @uniformSample X sb}[p x]) := by
  let idTransport : Transport X X := transportOfEquiv (Equiv.refl X)
  have law := @uniform_transport_bind X X X sa sb idTransport (pure : X → ProbComp X)
  change ((@uniformSample X sa) >>= pure) =ᵈ ((@uniformSample X sb) >>= pure) at law
  rw [bind_pure,bind_pure] at law
  exact law.prEvent_eq p

theorem uniform_bound_of {X : Type} {sa sb : SampleableType X} {p : X → Prop} {bound : ENNReal}
    (h : (Pr{let x ← @uniformSample X sa}[p x]) ≤ bound) :
    (Pr{let x ← @uniformSample X sb}[p x]) ≤ bound := (uniform_versions p).le.trans h

theorem uniform_value_of {X : Type} {sa sb : SampleableType X} {p : X → Prop} {value : ENNReal}
    (h : (Pr{let x ← @uniformSample X sa}[p x]) = value) :
    (Pr{let x ← @uniformSample X sb}[p x]) = value := (uniform_versions p).trans h

end CommitGolfCandidate.Reconstruction.HidingTraffic
