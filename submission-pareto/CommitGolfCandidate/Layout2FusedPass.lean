import CommitGolfCandidate.Layout2FusedLoop
import CommitGolfCandidate.Layout2Seen
import CommitGolfCandidate.GroupOpenHeaderSpec

/-! Fused opener: the reference state `fusedPass o td p` the record blocks are compared with. The V2a/V2b bridge
(`Layout2V2Bridge.pass_proof_eq`) reads the bytes the writers keep (the salt and the three quartet mates) from a state
`pass` that holds, in every record block, the linked salt (words 0..1) and the inverse of the quartet's reply (words
3..24): `Seen`. In V2b that was the first pass's end state. The fused loop has no such intermediate state, so
`fusedPass` is a pure definition (no machine run): the loaded input with those words written into every opened
record's block. `fused_seen` is `Seen` for it; `fused_retained` says that a fixed-oracle loop end state (`RSeen`) agrees
with it on every retained byte. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2F
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase (stride phaseBase)
open TwoPermutationPrototype.GroupedOpening.Layout2V2 (Seen linkedSalts pos pos_present passWord passDest)
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- The record whose block contains byte address `x` (for `x` in the record area). -/
def recIndex (x : Nat) : Nat :=
  4*((x-proofBase)/2136)+(if (x-proofBase)%2136<528 then 0 else if (x-proofBase)%2136<1064 then 1
    else if (x-proofBase)%2136<1600 then 2 else 3)

theorem rec_index (j m : Nat) (hm : m<25) : recIndex (destOf j+8*m)=j := by
  have pb : proofBase=13824430176 := rfl
  obtain ⟨g, r, hr, rfl⟩ : ∃ g r, r<4 ∧ j=4*g+r := ⟨j/4, j%4, Nat.mod_lt _ (by decide), by omega⟩
  have hg : (4*g+r)/4=g := by omega
  have hr' : (4*g+r)%4=r := by omega
  unfold recIndex destOf
  rw [hg, hr']
  have sub : proofBase+2136*g+phaseBase r+8*m-proofBase=2136*g+(phaseBase r+8*m) := by omega
  rw [sub]
  interval_cases r <;> simp only [phaseBase, ite_true, ite_false, reduceCtorEq, OfNat.ofNat_ne_zero,
    Nat.succ_ne_zero] <;> split_ifs <;> omega

/-- Word `w` of the reference state, from the loaded word `old`. -/
noncomputable def fusedWord (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat)
    (old : Word) : Word :=
  if proofBase ≤ 8*w ∧ recIndex (8*w)<p.card ∧ destOf (recIndex (8*w)) ≤ 8*w ∧
      (8*w-destOf (recIndex (8*w)))/8<25 then
    retainedWord o (keyOf td) td p (recIndex (8*w)) ((8*w-destOf (recIndex (8*w)))/8)
  else old

/-- The reference pass state. -/
noncomputable def fusedPass (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) : MachineState :=
  { actual.initialState .opening (td,p) with
    mem := fun a => if a.toNat%8=0 then fusedWord o td p (a.toNat/8) ((actual.initialState .opening (td,p)).mem a)
      else (actual.initialState .opening (td,p)).mem a }

theorem fused_view (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat) (hw : w<2^33) :
    memoryView (fusedPass o td p) w=fusedWord o td p w (memoryView (actual.initialState .opening (td,p)) w) := by
  have t : (wordAddress w).toNat=8*w := by unfold wordAddress; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change (if (wordAddress w).toNat%8=0 then _ else _)=_
  rw [t, if_pos (by omega), show 8*w/8=w by omega]; rfl

theorem pass_view (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (a m : Nat) (ha : a<p.card)
    (hm : m<25) : memoryView (fusedPass o td p) (blockW a+m)=retainedWord o (keyOf td) td p a m := by
  have card := Layout2V2.card_le p
  have bm := block_mul a
  have db := dest_bound a
  have pb : proofBase=13824430176 := rfl
  rw [fused_view o td p _ (by omega)]
  have e8 : 8*(blockW a+m)=destOf a+8*m := by omega
  unfold fusedWord
  rw [e8, rec_index a m hm, if_pos ⟨by omega, ha, by omega, by omega⟩]
  congr 1; omega

theorem fused_seen (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    Seen o (keyOf td) td p (fusedPass o td p) p.card := by
  have pp (a : Nat) (ha : a<p.card) : pos p a=posAt p a := by rw [pos_present p a ha, pos_at_eq p a ha]
  have pw (a : Nat) : passWord a=blockW a := rfl
  refine ⟨?_,?_⟩
  · intro a ha j
    have jj := j.isLt
    rw [pw, pass_view o td p a j.val ha (by omega)]
    unfold retainedWord
    rw [if_pos jj, pp a ha]
    congr 1; apply Fin.ext; simp; omega
  · intro a ha m hm three
    rw [pw, pass_view o td p a m ha hm]
    unfold retainedWord
    rw [if_neg (by omega), pp a ha]
    congr 1; apply Fin.ext; simp; omega

/-- A loop end state with the retained bytes of a fixed oracle agrees with `fusedPass` on them. -/
theorem fused_retained (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (s : MachineState)
    (seen : RSeen o (keyOf td) td p s p.card) :
    ∀ j<p.card, ∀ b<stride (j%4), Layout2Phase2.written ((posAt p j).val%4) (b/8)=false →
      s.getByte (BitVec.ofNat 64 (destOf j+b))=(fusedPass o td p).getByte (BitVec.ofNat 64 (destOf j+b)) := by
  intro j hj b hb hw
  have card := Layout2V2.card_le p
  have d25 : b/8<25 := by
    by_contra h
    have : Layout2Phase2.written ((posAt p j).val%4) (b/8)=true := by
      unfold Layout2Phase2.written; simp; omega
    rw [this] at hw; cases hw
  have bm := block_mul j
  have db := dest_bound j
  have pb : proofBase=13824430176 := rfl
  rw [seen j hj b hb hw, show destOf j+b=8*(blockW j+b/8)+b%8 by omega, byte_view _ _ _ (by omega) (by omega),
    pass_view o td p j (b/8) hj d25]

end TwoPermutationPrototype.GroupedOpening.Layout2F
