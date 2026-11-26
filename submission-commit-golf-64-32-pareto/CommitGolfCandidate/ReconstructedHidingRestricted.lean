import CommitGolfCandidate.ReconstructedHidingPosterior
import CommitGolfCandidate.TwoPermutationPinnedWorldBridge
import CommitGolfCandidate.TaggedPinnedConstantFrame
import CommitGolfCandidate.HidingPrefixBudget

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses hidingLeafDigests pinnedFullLeafDigests
local instance restrictedDiscrete {α : Type} : MeasurableSpace α := ⊤
noncomputable local instance restrictedOpen (p : Positions) : SampleableType (OpenIx p → Salt) := by
  classical exact SampleableType.ofFintype _
noncomputable local instance restrictedClosed (p : Positions) : SampleableType (ClosedIx p → Salt) := by
  classical exact SampleableType.ofFintype _

def wideOpen {p : Positions} (op : OpenIx p → Salt) : OpenedSalts p := fun i => (op i).setWidth 128
def wideClosed {p : Positions} (cl : ClosedIx p → Salt) : UnopenedSalts p := fun i => (cl i).setWidth 128

theorem wide_merge (p : Positions) (op : OpenIx p → Salt) (cl : ClosedIx p → Salt) :
    mergeSaltTape (wideOpen op) (wideClosed cl) = widenTape (joinSalts p op cl) := by
  funext i
  unfold mergeSaltTape widenTape joinSalts
  by_cases h : i ∈ p
  · rw [dite_eq_left h]
    apply congrArg (fun v : Salt => v.setWidth 128)
    split
    · rfl
    · rename_i opposite; exact (opposite h).elim
  · rw [dite_eq_right h]
    apply congrArg (fun v : Salt => v.setWidth 128)
    split
    · rename_i opposite; exact (h opposite).elim
    · rfl

theorem honest_masked_tape (p : BiPermutation Block) (m : Message) (s : PrivateSalts) :
    hidingLeafDigests p m (widenTape s) = pinnedFullLeafDigests p m (widenTape s) := by
  funext i
  unfold hidingLeafDigests pinnedFullLeafDigests widenTape
  rw [mask_widen]

noncomputable def restrictedPosterior {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (c : Compression) (b : Bool) : ProbComp O := do
  let (ch,base) ← lazyRun c a.choose (PermutationCache.empty Block)
  let op ← $ᵗ (OpenIx ch.positions → Salt)
  let cl ← $ᵗ (ClosedIx ch.positions → Salt)
  pinnedClosedRestrictedWorld base ch.positions ch.message₀ ch.message₁ (wideOpen op) (wideClosed cl) b
    (pinnedObserveTape a build c ch (wideOpen op))

noncomputable def restrictedError (q : Nat) : ℝ := (3*LENGTH:ℝ)*((q+3*LENGTH:ℝ)/2^1343)

theorem restricted_distance {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (c : Compression) (b : Bool) (q : Nat)
    (bound : Hiding.QueryBound a q) (small : q+1 ≤ 2^120) :
    measureTVDist (restrictedPosterior a build c b) (independentPosterior a build c b)
      ≤ restrictedError q := by
  have nn : 0 ≤ restrictedError q := by unfold restrictedError; positivity
  unfold restrictedPosterior independentPosterior
  apply pinned_restricted_bind_support_le (lazyRun c a.choose (PermutationCache.empty Block)) _ _ _ nn
  rintro ⟨ch,base⟩ reached
  obtain ⟨calls,fits,cache,_⟩ := hiding_prefix_split a bound c (ch,base) reached
  have room : base.entries.length + 3*LENGTH ≤ q+3*LENGTH := by
    change base.entries.length ≤ calls at cache
    omega
  have cap : q+3*LENGTH ≤ 2^121 := by
    have len : LENGTH=2^24 := rfl
    omega
  have agree (i : Index) (selected : i ∈ ch.positions) : ch.message₀ i = ch.message₁ i :=
    congrFun ch.agree ⟨i,selected⟩
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ nn
  intro op
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ nn
  intro cl
  have estimate := pinned_closed_restricted_world_near base ch.positions ch.message₀ ch.message₁
    (wideOpen op) (wideClosed cl) b agree (pinnedObserveTape a build c ch (wideOpen op))
    (q+3*LENGTH) room cap (fun result reached => by
      obtain ⟨length,_,covered⟩ := pinned_full_const_frame base [] (pinnedFirstAddresses ch.message₀ ch.message₁) result reached
      rw [pinned_first_addresses_length] at length
      exact ⟨length,covered⟩)
  rw [wide_merge] at estimate
  simp only [honest_masked_tape,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at estimate
  exact estimate

end CommitGolfCandidate.Reconstruction.HidingTape
