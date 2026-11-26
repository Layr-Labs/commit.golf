import CommitGolfCandidate.S5CheckCursorBounds
import CommitGolfCandidate.S5CheckRowSites
import CommitGolfCandidate.S5CheckNode
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv
def pathDepth (b : Bool) := if b then 15 else 24
def layerFuel (b : Bool) (h : Nat) :=
  24+(S4.radix h-1)*((if h=0 then 4 else 3)+(if b then 438 else 9))+6+parentFuel h
def pathFuel (b : Bool) (h n : Nat) := ((List.range' h n).map (layerFuel b)).sum
def pathCalls (h n : Nat) := ((List.range' h n).map levelCalls).sum
set_option maxHeartbeats 4000000 in
theorem path_limits : pathFuel false 0 24≤3500 ∧ pathFuel true 0 15≤10000 ∧ pathCalls 0 24=96 ∧ pathCalls 0 15=72 := by decide +kernel

theorem rowNumbers (p : RowSite) : p.radix=(if p.height.val=0 then 3 else 2) ∧ 2≤p.radix ∧ p.radix≤3 ∧
    p.peerOps.length=(if p.height.val=0 then 4 else 3) ∧ S5.bits p.height.val≤256 ∧
    S5.layerBits p.height.val+(p.radix-1)*S5.bits p.height.val=S5.layerBits (p.height.val+1) :=
  (by decide +kernel : ∀ q : RowSite,q.radix=(if q.height.val=0 then 3 else 2) ∧ 2≤q.radix ∧ q.radix≤3 ∧
    q.peerOps.length=(if q.height.val=0 then 4 else 3) ∧ S5.bits q.height.val≤256 ∧
    S5.layerBits q.height.val+(q.radix-1)*S5.bits q.height.val=S5.layerBits (q.height.val+1)) p

structure InputSize (x : CheckInput) (p : RowSite) (r : Nat) : Prop where
  row : r<x.positions.card
  mode : p.batch=decide (x.positions.card=BATCH)
  allowed : p.allowed=true

theorem InputSize.budget {x p r} (s : InputSize x p r) {k : Nat} (kbound : k<p.radix-1) :
    (p.batch=true → peerBit r p.height.val+k*S5.bits p.height.val+S5.bits p.height.val≤8*69397) ∧
    (p.batch=false → proofBase+(peerOffset r p.height.val+32*k)+32≤MEMORY_BYTES) ∧
    (peerOffset r p.height.val+32*k)%8=0 := by
  have cost : S5.layerBits p.height.val+(p.radix-1)*S5.bits p.height.val≤4030 ∨ p.batch=false :=
    (by decide +kernel : ∀ q : RowSite,q.allowed=true → S5.layerBits q.height.val+(q.radix-1)*S5.bits q.height.val≤4030 ∨ q.batch=false) p s.allowed
  have maxr : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  have off : (24+32*(if p.height.val=0 then 0 else p.height.val+1))+32*k+32≤824 :=by
    obtain ⟨rad,_,_,_,_,_⟩:=rowNumbers p
    rw [rad] at kbound
    have h:=p.height.isLt
    split at kbound <;> rename_i e <;> simp only [e,ite_true,ite_false] at * <;> omega
  refine ⟨?_,?_,?_⟩
  · intro isBatch
    have cnt : x.positions.card=128:=of_decide_eq_true (s.mode.symm.trans isBatch)
    have inside:=s.row
    obtain priced|no:=cost
    · have smaller:=Nat.mul_le_mul_right (S5.bits p.height.val) (show k+1≤p.radix-1 by omega)
      rw [Nat.succ_mul] at smaller;unfold peerBit;omega
    · simp_all
  · intro _;have hi:=s.row;change x.positions.card≤16777216 at maxr;unfold peerOffset proofBase MEMORY_BYTES;omega
  · unfold peerOffset;omega

theorem peer_bit_next (p : RowSite) (r : Nat) :
    peerBit r p.height.val+(p.radix-1)*S5.bits p.height.val=peerBit r (p.height.val+1) := by
  unfold peerBit;rw [Nat.add_assoc,(rowNumbers p).2.2.2.2.2]
theorem peer_offset_next (p : RowSite) (r : Nat) :
    peerOffset r p.height.val+32*(p.radix-1)=peerOffset r (p.height.val+1) := by
  have e:=(rowNumbers p).1;rw [e];unfold peerOffset;by_cases zero:p.height.val=0
  · simp [zero]
  · simp [zero];omega
end CommitGolfCandidate.S5Machine.Check
