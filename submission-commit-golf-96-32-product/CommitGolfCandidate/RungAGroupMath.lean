import CommitGolfCandidate.RungAPlan
import CommitGolfCandidate.LateCachedTree
import CommitGolfCandidate.S4HonestTree
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf R4 Late
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1300000
abbrev scale (h : Nat) := slots .twentyFour h
def baseLeaf (o : Oracle) (m : Message) (r : Tape) (i : Nat) := (initialList o.compression m (pairSalts r))[i]?.getD 0
def model (o : Oracle) (m : Message) (r : Tape) := treeNode o.compression (baseLeaf o m r)
def rowValue (o : Oracle) (m : Message) (r : Tape) (g j : Nat) : Block :=
  if h : 24*g+j<LENGTH then finalRow o m r ⟨24*g+j,h⟩ else 0

theorem rowValue_leaf (o : Oracle) (m : Message) (r : Tape) (g j : Nat) (fit : 24*g+j<LENGTH) :
    o.compression (rowValue o m r g j)=model o m r 0 (24*g+j) := by
  let i : Index:=⟨24*g+j,fit⟩
  have leaf := (S4.honestTree o.compression m (pairSalts r)).leaf i
  have real:=fixed_tree_node_all o.compression m (pairSalts r) 0 i.val (by decide)
  rw [rowValue,dif_pos fit]
  exact (LateHiding.leaf_digest_eq o.compression (i.val.testBit 0) (pairSalts r i) (m i)).trans (leaf.symm.trans real)

private theorem geometry (g limit h j : Nat) (hg : g<699051)
    (valid : limit=min 24 (16777216-24*g)) (hsmall : h≤4) (bound : j<scale h) :
    (S4.span h*j<limit ↔ scale h*g+j<levelCount h) := by
  interval_cases h <;> norm_num [slots,leaves,depth,S4.span,levelCount,S4.width,LENGTH,LOG_LENGTH] at bound ⊢ <;> omega

private theorem child_order (h : Nat) (low : h<4) :
    scale h=S4.radix h*scale (h+1) ∧ 0<S4.radix h := by
  interval_cases h <;> decide

private theorem modelParent (o : Oracle) (m : Message) (r : Tape) (h j : Nat) (low : h<4) (ok : j<levelCount (h+1)) :
    model o m r (h+1) j =
    mask (h != 0) (o.compression ((if h=0 then model o m r h (S4.radix h*j+2) else 0) ++
      model o m r h (S4.radix h*j+1) ++ model o m r h (S4.radix h*j))) := by
  change treeNode _ _ (h+1) j=_
  refine (if_pos ok : treeNode o.compression (baseLeaf o m r) (h+1) j=_).trans ?_
  unfold layerHash S4.row
  have eqn (x : Late.Digest) : S4.retained S4.active (h+1) x=mask (h != 0) x:=by interval_cases h <;> rfl
  exact eqn _

attribute [local irreducible] model treeNode mask rowValue
theorem evalWanted (o : Oracle) (m : Message) (r : Tape) (g limit : Nat)
    (hg : g<699051) (valid : limit=min 24 (16777216-24*g)) (saved : Nat→Late.Digest) (h j : Nat)
    (hsmall : h≤4) (bound : j<scale h) :
    value o.compression (fun k=>o.compression (rowValue o m r g k)) saved (wanted limit h j)=
      model o m r h (scale h*g+j) := by
  let ev:=value o.compression (fun k=>o.compression (rowValue o m r g k)) saved
  change ev _=_
  induction h generalizing j with
  | zero=>
    have fit:=geometry g limit 0 j hg valid (by decide) bound
    change 1*j<limit ↔ 24*g+j<levelCount 0 at fit
    by_cases ok : j<limit
    · rw [wanted,if_pos ok]
      change value _ _ _ (.leaf j)=_
      exact rowValue_leaf o m r g j (fit.mp (by omega))
    · rw [wanted,if_neg ok]
      change value _ _ _ .zero=model _ _ _ 0 _
      unfold model;exact (missing_node _ _ _ _ (by change levelCount 0≤24*g+j;omega)).symm
  | succ h ih=>
    let ar:=S4.radix h
    let idx:=scale (h+1)*g+j
    have lo : h<4:=by omega
    have fit:=geometry g limit (h+1) j hg valid hsmall bound
    change 3*2^h*j<limit ↔ idx<levelCount (h+1) at fit
    by_cases ok : 3*2^h*j<limit
    · have ord : scale h=ar*scale (h+1):=(child_order h lo).1
      have ch (k : Nat) (kl : k<ar) : ev (wanted limit h (ar*j+k))=model o m r h (ar*idx+k) := by
        have step:=Nat.mul_le_mul_left ar (show j+1≤scale (h+1) from bound)
        rw [Nat.mul_succ] at step
        have room : ar*j+k<scale h:=by rw [ord];omega
        have sub:=ih (ar*j+k) (by omega) room
        have ix : scale h*g+(ar*j+k)=ar*idx+k:=by rw [ord];dsimp [idx];ring
        rw [ix] at sub;exact sub
      have c0:=ch 0 (show 0<ar from (child_order h lo).2)
      have c1:=ch 1 (by dsimp [ar,S4.radix];split <;> decide)
      simp only [Nat.add_zero] at c0
      rw [wanted,if_pos ok,modelParent _ _ _ _ _ lo (fit.mp ok)]
      change mask _ (o.compression (ev (if h=0 then wanted limit h (ar*j+2) else .zero) ++
        ev (wanted limit h (ar*j+1)) ++ ev (wanted limit h (ar*j))))=_
      rw [c0,c1]
      by_cases z : h=0
      · rw [if_pos z,if_pos z,ch 2 (by dsimp [ar,S4.radix];rw [if_pos z];decide)]
      · rw [if_neg z,if_neg z]
        change mask _ (o.compression (value _ _ _ .zero ++ _ ++ _))=_
        rfl
    · rw [wanted,if_neg ok]
      change value _ _ _ .zero=model _ _ _ _ _
      unfold model;exact (missing_node _ _ _ _ (by omega)).symm
end CommitGolfCandidate.RungA.Kernel
