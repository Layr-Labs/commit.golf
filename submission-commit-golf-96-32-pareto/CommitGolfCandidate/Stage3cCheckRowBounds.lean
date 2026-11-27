import CommitGolfCandidate.Stage3cCheckCursorBounds
import CommitGolfCandidate.Stage3cCheckRowSites
import CommitGolfCandidate.Stage3cCheckNode
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv
def pathDepth (b : Bool) := if b then 15 else 24
def layerFuel (b : Bool) (h : Nat) :=
  24+(Geo.radix h-1)*(3+(if b then 438 else 9))+6+parentFuel h
def pathFuel (b : Bool) (h n : Nat) := ((List.range' h n).map (layerFuel b)).sum
def pathCalls (h n : Nat) := ((List.range' h n).map levelCalls).sum
set_option maxHeartbeats 4000000 in
theorem path_limits : pathFuel false 0 24≤3500 ∧ pathFuel true 0 15≤10000 ∧ pathCalls 0 24=96 ∧ pathCalls 0 15=72 := by decide +kernel

theorem rowNumbers (p : RowSite) : p.radix=2 ∧ 2≤p.radix ∧ p.radix≤3 ∧
    p.peerOps.length=3 ∧ Pw.bits p.height.val≤256 ∧
    Pw.layerBits p.height.val+(p.radix-1)*Pw.bits p.height.val=Pw.layerBits (p.height.val+1) :=
  (by decide +kernel : ∀ q : RowSite,q.radix=2 ∧ 2≤q.radix ∧ q.radix≤3 ∧
    q.peerOps.length=3 ∧ Pw.bits q.height.val≤256 ∧
    Pw.layerBits q.height.val+(q.radix-1)*Pw.bits q.height.val=Pw.layerBits (q.height.val+1)) p

structure InputSize (x : CheckInput) (p : RowSite) (r : Nat) : Prop where
  row : r<x.positions.card
  mode : p.batch=decide (x.positions.card=BATCH)
  allowed : p.allowed=true

theorem InputSize.budget {x p r} (s : InputSize x p r) {k : Nat} (kbound : k<p.radix-1) :
    (p.batch=true → peerBit r p.height.val+k*Pw.bits p.height.val+Pw.bits p.height.val≤8*67840) ∧
    (p.batch=false → proofBase+(peerOffset r p.height.val+32*k)+32≤MEMORY_BYTES) ∧
    (peerOffset r p.height.val+32*k)%8=0 := by
  have cost : Pw.layerBits p.height.val+(p.radix-1)*Pw.bits p.height.val≤3780 ∨ p.batch=false :=
    (by decide +kernel : ∀ q : RowSite,q.allowed=true → Pw.layerBits q.height.val+(q.radix-1)*Pw.bits q.height.val≤3780 ∨ q.batch=false) p s.allowed
  have maxr : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  have off : (24+32*p.height.val)+32*k+32≤792 :=by
    have h:=p.height.isLt
    have k0 : k=0:=by change k<2-1 at kbound;omega
    omega
  refine ⟨?_,?_,?_⟩
  · intro isBatch
    have cnt : x.positions.card=128:=of_decide_eq_true (s.mode.symm.trans isBatch)
    have inside:=s.row
    obtain priced|no:=cost
    · have smaller:=Nat.mul_le_mul_right (Pw.bits p.height.val) (show k+1≤p.radix-1 by omega)
      rw [Nat.succ_mul] at smaller;unfold peerBit;omega
    · simp_all
  · intro _;have hi:=s.row;change x.positions.card≤16777216 at maxr;unfold peerOffset proofBase MEMORY_BYTES;omega
  · unfold peerOffset;omega

theorem peer_bit_next (p : RowSite) (r : Nat) :
    peerBit r p.height.val+(p.radix-1)*Pw.bits p.height.val=peerBit r (p.height.val+1) := by
  unfold peerBit;rw [Nat.add_assoc,(rowNumbers p).2.2.2.2.2]
theorem peer_offset_next (p : RowSite) (r : Nat) :
    peerOffset r p.height.val+32*(p.radix-1)=peerOffset r (p.height.val+1) := by
  unfold peerOffset RowSite.radix Geo.radix;omega
end CommitGolfCandidate.Chained.BinaryMachine.Check
