import CommitGolfCandidate.TruncTranscript
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec OracleComp.DeferredSampling
local instance {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 12000
set_option maxHeartbeats 250000

private def remember {S : Type} {k : Nat} (c : Hiding.HidingChallenge S k) : Hiding.HidingChallenge (S×Positions) k :=
  ⟨c.message₀,c.message₁,c.positions,c.size_eq,c.agree,c.aux,c.positions⟩
private def mapped {S O : Type} {k : Nat} (a : Hiding.HidingAdversary S O k) : Hiding.HidingAdversary (S×Positions) O k where
  choose := remember <$> a.choose
  observe state root p := a.observe state.1 root (publicProof state.2 p)
private theorem mappedBound {S O : Type} {k t : Nat} (a : Hiding.HidingAdversary S O k)
    (h : Hiding.QueryBound a t) : Hiding.QueryBound (mapped a) t := by
  intro first member
  change first∈support (costDist (remember <$> a.choose) _) at member
  rw [costDist_map,support_map] at member;obtain ⟨c,hc,rfl⟩:=member
  exact ⟨(h c hc).1, fun root proof=>(h c hc).2 root (publicProof c.1.positions proof)⟩

attribute [local irreducible] publicProof referenceTranscript submission

private theorem publicDist (packRun : Wire.PackRun) (bytes : Wire.PackedBytes) {S O : Type} {k : Nat}
    (o : Oracle) (a : Hiding.HidingAdversary S O k) (b : Bool) :
    𝒟[fixedOracleRun o (Hiding.hidingExperiment submission.scheme a b)] = 𝒟[referenceHiding o (mapped a) b] := by
  have exp : Hiding.hidingExperiment submission.scheme a b = (do
      let c←a.choose
      let v←transcript (if b then c.message₁ else c.message₀) c.positions
      a.observe c.aux v.1 v.2) := by simp [Hiding.hidingExperiment,transcript,bind_assoc,pure_bind]
  rw [exp,fixed_oracle_run_bind]
  unfold referenceHiding
  simp only [mapped,fixed_oracle_run_map,bind_map_left]
  apply _root_.evalDist_bind_congr;intro c
  rw [fixed_oracle_run_bind,transcriptRun packRun bytes,bind_assoc];simp only [pure_bind,remember]
  let msg:=if b then c.message₁ else c.message₀
  exact commit_salts_uniform msg (fun salt=>
    let v:=referenceTranscript o.compression msg salt c.positions
    fixedOracleRun o (a.observe c.aux v.1 (publicProof c.positions v.2)))

theorem truncHiding (packRun : Wire.PackRun) (bytes : Wire.PackedBytes) : submission.scheme.Hiding HIDING_ERROR := by
  constructor
  · intro k t;unfold HIDING_ERROR;apply le_min (by norm_num);positivity
  · intro k t _ S O a bound
    have dist (b : Bool) : 𝒟[Hiding.runHiding (Hiding.hidingExperiment submission.scheme a b)] =
        𝒟[Oracle.sample >>= fun o=>referenceHiding o (mapped a) b] := by
      unfold Hiding.runHiding
      apply _root_.evalDist_bind_congr;intro o
      have same : (do let (v,_)←o.run (Hiding.hidingExperiment submission.scheme a b);pure v)=
          fixedOracleRun o (Hiding.hidingExperiment submission.scheme a b) := by
        unfold fixedOracleRun;rw [map_eq_bind_pure_comp];apply bind_congr;rintro ⟨v,n⟩;rfl
      rw [same];exact publicDist packRun bytes o a b
    simpa only [measureTVDist,dist] using (referencePrivacy (mapped a) (mappedBound a bound))
end CommitGolfCandidate.Trunc
