import CommitGolfCandidate.CapBScans3
import CommitGolfCandidate.CapBOld
import CommitGolfCandidate.Layout2CapRoundtrip
namespace CommitGolfCandidate.CapB
open CommitGolf
open TwoPermutationPrototype.GroupedOpening (capOffset foldNodes)
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

private theorem symbols_match (m i : Nat) (positive : 1≤m) (bound : m≤32) (inside : i<8*Layout2.Cap.size m) :
    Symbol.tags m i=Symbol.oldTags m (Layout2.Cap.enc m i) := by
  apply beq_iff_eq.mp
  change Symbol.compareAt m i=true
  interval_cases m
  · exact Symbol.labels1 i inside
  · exact Symbol.labels2 i inside
  · exact Symbol.labels3 i inside
  · exact Symbol.labels4 i inside
  · exact Symbol.labels5 i inside
  · exact Symbol.labels6 i inside
  · exact Symbol.labels7 i inside
  · exact Symbol.labels8 i inside
  · exact Symbol.labels9 i inside
  · exact Symbol.labels10 i inside
  · exact Symbol.labels11 i inside
  · exact Symbol.labels12 i inside
  · exact Symbol.labels13 i inside
  · exact Symbol.labels14 i inside
  · exact Symbol.labels15 i inside
  · exact Symbol.labels16 i inside
  · exact Symbol.labels17 i inside
  · exact Symbol.labels18 i inside
  · exact Symbol.labels19 i inside
  · exact Symbol.labels20 i inside
  · exact Symbol.labels21 i inside
  · exact Symbol.labels22 i inside
  · exact Symbol.labels23 i inside
  · exact Symbol.labels24 i inside
  · exact Symbol.labels25 i inside
  · exact Symbol.labels26 i inside
  · exact Symbol.labels27 i inside
  · exact Symbol.labels28 i inside
  · exact Symbol.labels29 i inside
  · exact Symbol.labels30 i inside
  · exact Symbol.labels31 i inside
  · exact Symbol.labels32 i inside

theorem honest_block (ds : List D) (bound : ds.length≤32) (clean : ∀ v∈ds,v.extractLsb' 238 18=0) : HonestBlock ds := by
  intro j good
  have positive : 1≤ds.length := by
    by_contra! empty
    have zero : ds.length=0 := by omega
    rw [zero] at good;exact Nat.not_lt_zero _ good
  apply BitVec.eq_of_getLsbD_eq;intro b small
  let i:=8*j+b;let old:=Layout2.Cap.enc ds.length i
  have hi : i<8*Layout2.Cap.size ds.length := by dsimp [i];omega
  have ho : old<8*Layout2.Cap.size ds.length := Layout2.Cap.enc_valid _ positive bound _ hi
  rw [Symbol.raw_bit clean j b (by rwa [capRaw_length]) small,canonicalBlock,Layout2.gather_bit _ _ _ _ _ small]
  change (Symbol.tags ds.length i).any (Symbol.readBit ds)=((foldNodes ds)[old/8]?.getD 0).getLsbD (old%8)
  rw [Symbol.canonical_bit ds clean _ _ (by omega) (by omega),show 8*(old/8)+old%8=old by omega]
  rw [symbols_match _ _ positive bound hi]

/-- The cap premise of encoder_of_blocks for honest frontier digests, including partial-group padding. -/
theorem cap_raw_honest (ds : List D) (clean : ∀ v∈ds,v.extractLsb' 238 18=0) :
    ∀ g j,j<952 → 952*g+j<capOffset ds.length →
       (capRaw ds)[952*g+j]?.getD 0=Layout2.gather Layout2.Cap.enc
         (if g<capOffset ds.length/952 then 32 else Layout2.Cap.tag (capOffset ds.length%952))
         (fun u=>(foldNodes ds)[952*g+u]?.getD 0) j :=
  all_blocks honest_block Layout2.Cap.enc_valid ds clean
end CommitGolfCandidate.CapB
