import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.QuadCommitGeometry

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves
set_option maxHeartbeats 900000

def qSource (g : Nat) := 603980292+64*g
def qLeaf (i : Nat) := qSource (i/4)+9+4*(i%4)
def qUpper (g : Nat) := 536871428+4*(4194304+g)
def qSalt (i : Nat) := 872415748+2*i

theorem source_address (g : Nat) :
    8*qSource g = 4294971424+quartetBaseOffset+quartetOffset g := by
  unfold qSource quartetBaseOffset quartetOffset LENGTH LOG_LENGTH;omega
theorem leaf_address (i : Nat) :
    8*qLeaf i = 4294971424+quartetBaseOffset+quartetLeafOffset i := by
  unfold qLeaf qSource quartetBaseOffset quartetLeafOffset quartetOffset LENGTH LOG_LENGTH;omega
theorem upper_address (g : Nat) :
    8*qUpper g = 4294971424+upperLeafOffset g := by
  unfold qUpper upperLeafOffset; rw [quartet_count];omega
theorem salt_address (i : Nat) :
    8*qSalt i = 4294971424+saltBaseOffset+16*i := by
  rw [base_offsets.2];unfold qSalt;omega

def PaddedLeaves (mem : Memory) (children : Nat → Words 4) : Prop :=
  (∀ g < 4194304, ∀ k < 9, mem (qSource g+k) = 0) ∧
  (∀ i < 16777216, (window mem (qLeaf i) : Words 4) = children i)

theorem leaf_spill_frame (mem : Memory) (i : Nat) (hi : i<16777216)
    (tag : Word) (nonce : Words 2) (a b : BitVec 1600) :
    let post := pinnedWrites mem tag nonce (leafStart i) (qLeaf i) a b
    (window post (qLeaf i) = lowDigest (replyWords b)) ∧
    (∀ j < i, ∀ k < 4, post (qLeaf j+k)=mem (qLeaf j+k)) ∧
    (∀ g < 4194304, ∀ k < 9, post (qSource g+k)=mem (qSource g+k)) ∧
    (∀ j, i<j → j<16777216 → ∀ k<32, post (leafStart j+5+k)=mem (leafStart j+5+k)) ∧
    (∀ j<16777216, ∀ k<2, post (qSalt j+k)=mem (qSalt j+k)) := by
  dsimp only
  refine ⟨pinned_digest_words ..,?_,?_,?_,?_⟩
  · intro j hj k hk
    apply pinned_word_outside
    · right;unfold leafStart qLeaf qSource;omega
    · left;unfold qLeaf qSource;omega
  · intro g hg k hk
    apply pinned_word_outside
    · right;unfold leafStart qSource;omega
    · by_cases earlier : g ≤ i/4
      · left;unfold qLeaf qSource;omega
      · right;unfold qLeaf qSource;omega
  · intro j more inRange k hk
    apply pinned_word_outside
    · right;unfold leafStart;omega
    · left;unfold qLeaf qSource leafStart;omega
  · intro j hj k hk
    apply pinned_word_outside
    · right;unfold leafStart qSalt;omega
    · right;unfold qLeaf qSource qSalt;omega

def quadWords (children : Nat → Words 4) (g : Nat) : Words 25 := fun k =>
  if k.val<9 then 0 else children (4*g+(k.val-9)/4) ⟨(k.val-9)%4,by omega⟩

theorem quad_input_words (mem : Memory) (children : Nat → Words 4) (g : Nat)
    (hg : g<4194304) (ready : PaddedLeaves mem children) :
    window mem (qSource g) = quadWords children g := by
  funext k
  have size := k.isLt
  unfold quadWords
  by_cases small : k.val<9
  · rw [if_pos small];exact ready.1 g hg k.val small
  · rw [if_neg small]
    let j := 4*g+(k.val-9)/4
    have bound : j<16777216 := by dsimp [j];omega
    have addr : qSource g+k.val=qLeaf j+(k.val-9)%4 := by
      unfold qLeaf; dsimp [j];have offset : (k.val-9)/4<4 := by omega
      have quotient : (4*g+(k.val-9)/4)/4=g := by omega
      rw [quotient];omega
    change mem (qSource g+k.val)=_
    rw [addr]
    exact congrFun (ready.2 j bound) ⟨(k.val-9)%4,by omega⟩

theorem upper_spill_frame (mem : Memory) (g : Nat) (hg : g<4194304) (reply : BitVec 1600) :
    let post := writeWindow mem (qUpper g) (replyWords reply)
    (window post (qUpper g) = lowDigest (replyWords reply)) ∧
    (∀ j < g, ∀ k<4, post (qUpper j+k)=mem (qUpper j+k)) ∧
    (∀ w, qSource 0≤w → post w=mem w) := by
  dsimp only
  constructor
  · funext k
    have hk := k.isLt
    have yes : qUpper g≤qUpper g+k.val ∧ qUpper g+k.val<qUpper g+25 := by omega
    simp [window,writeWindow,lowDigest,yes]
  constructor
  · intro j hj k hk
    apply dif_neg;unfold qUpper;omega
  · intro w high
    apply dif_neg;unfold qUpper qSource at *;omega

end TwoPermutationPrototype.QuartetCommit
