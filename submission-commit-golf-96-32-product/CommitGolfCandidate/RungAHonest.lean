import CommitGolfCandidate.RungAReference
import CommitGolfCandidate.RungAGroup
import CommitGolfCandidate.S4RawProof
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor nodeAddress rowAddress levelCount unusedSlotAddr Digest slice node)
open S4 (radix nodeIndex childPos)
open S4.Machine (W byte indexBase)
attribute [local irreducible] List.finRange S4Hiding.tree

private theorem sliceBytes {td : Trapdoor} {a n k : Nat} (hk:k<n) (low:tdAddress≤a) :
    (slice td a n).extractLsb' (8*k) 8=slice td (a+k) 1 := by
  change (td.extractLsb' (8*(a-tdAddress)) (8*n)).extractLsb' (8*k) 8=td.extractLsb' (8*(a+k-tdAddress)) 8
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  simp only [BitVec.getLsbD_extractLsb',show j<8 by omega,show 8*k+j<8*n by omega,decide_true,Bool.true_and]
  exact congrArg (fun b : Nat=>td.getLsbD b) (show 8*(a-tdAddress)+(8*k+j)=8*(a+k-tdAddress)+j by omega)

theorem rebuiltFrame {H ps before after} (rebuilt : Rebuilt .twentyFour H ps before after)
    (a n : Nat) (lo:tdAddress≤a) (hi:a+n≤tdAddress+3355443200)
    (out : ∀ k,k<n → Novisit (selected .twentyFour ps) (a+k)) : slice after a n=slice before a n := by
  apply BitVec.eq_of_getLsbD_eq;intro b bb
  let k:=b/8
  have hk:k<n:=by dsimp [k];omega
  have e:=rebuilt.frame (a+k) (by omega) (by omega) (out k hk)
  rw [←sliceBytes hk lo,←sliceBytes hk lo] at e
  have bit:=congrArg (fun v : Byte=>v.getLsbD (b%8)) e
  simpa only [BitVec.getLsbD_extractLsb',show b%8<8 by omega,decide_true,Bool.true_and,
    show 8*k+b%8=b by dsimp [k];omega] using bit

theorem retainedSlot {H ps td after} (built : Rebuilt .twentyFour H ps td after)
    (h j : Nat) (low : 4≤h) (up : h≤24) (real : j<levelCount h) :
    slice after (nodeAddress h j) 32=slice td (nodeAddress h j) 32 := by
  apply rebuiltFrame built
  · unfold nodeAddress tdAddress;omega
  · have:=Late.parent_below_salts h j real;unfold Late.rowBase tdAddress at *;omega
  · intro k bk x y sel
    have hx:x<4:=sel.1
    have hit:=apartCells hx (by omega) sel.2.1 real (by left;omega)
    unfold Apart32 at hit;omega

private theorem siblingGroup (i : Index) (h k : Nat) (lh:h<4) (bk:k<radix h) :
    i.val/24=(radix h*nodeIndex i.val (h+1)+k)/sizeAt h := by
  interval_cases h <;> simp [sizeAt,slots,leaves,depth,radix,nodeIndex,S4.span] at * <;> omega

theorem siblingCorrect {o m r td after ps} (f : FusedTrapdoor .twentyFour o m r td)
    (built : Rebuilt .twentyFour o.compression ps td after) (i : Index) (mem:i∈ps) (h n : Nat) (bh:h<24) :
    slice after (S4.Open.siblingAddress i h n) 32=S4.sibling (tree o m r) i.val h n := by
  let p:=nodeIndex i.val (h+1)
  let k:=(childPos i.val h+n+1)%radix h
  let j:=radix h*p+k
  have hk:k<radix h:=Nat.mod_lt _ (by unfold radix;split <;> decide)
  have rad : radix h≤3:=by unfold radix;split <;> decide
  have eqv : nodeAddress h j=unusedSlotAddr h p k:=Late.row_slot _ _ _ hk
  change slice after (unusedSlotAddr h p k) 32=node (tree o m r) h j
  by_cases real:j<levelCount h
  · rw [←eqv]
    by_cases lh:h<4
    · have sel : selected .twentyFour ps h j:=⟨lh,real,i,mem,siblingGroup i h k lh hk⟩
      exact (built.nodes h j sel).trans (honestDigest f _ _ (by omega))
    · exact (retainedSlot built h j (by omega) bh.le real).trans (f.stored h (by change 4≤h;omega) (by change h≤24;omega) j real)
  · have pp:p<levelCount (h+1):=by
      unfold levelCount;rw [Nat.min_eq_left (by omega)];exact S4.indexInside i _
    have gap : Late.Padding h p k:=⟨bh,pp,by omega,Or.inr (by change levelCount h≤j;omega)⟩
    have past : slice after (unusedSlotAddr h p k) 32=slice td (unusedSlotAddr h p k) 32:=by
      apply rebuiltFrame built
      · unfold tdAddress unusedSlotAddr rowAddress;omega
      · have:=Late.padValid _ _ _ gap;unfold Late.rowBase tdAddress at *;omega
      · intro b bb u v hit
        have hu:u<4:=hit.1
        have:=Late.node_pad u v h p k (by omega) hit.2.1 gap;omega
    rw [past,f.gaps _ _ _ gap,tree,Late.fixed_tree_node_all _ _ _ _ _ bh.le,Late.missing_node _ _ _ _ (by omega)]

theorem saltCorrect {o m r td after ps} (f : FusedTrapdoor .twentyFour o m r td)
    (built : Rebuilt .twentyFour o.compression ps td after) (i : Index) :
    slice after (Late.sharedSaltAddr i.val) 24=R4.pairSalts r i := by
  apply Eq.trans _ (f.salts i);apply rebuiltFrame built
  · unfold Late.sharedSaltAddr tdAddress Late.rowBase;omega
  · have h:=i.isLt;change i.val<16777216 at h;unfold Late.sharedSaltAddr tdAddress Late.rowBase;omega
  · intro b bb u v hit;right;have:=Late.parent_below_salts u v hit.2.1;unfold Late.sharedSaltAddr;omega
end CommitGolfCandidate.RungA
