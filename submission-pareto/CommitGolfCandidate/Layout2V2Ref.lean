import CommitGolfCandidate.Layout2Pass
import CommitGolfCandidate.GroupOpenModel
import CommitGolfCandidate.TwoPermutationHeapInvariant
import CommitGolfCandidate.GroupOpenHeaderSpec

/-! Layout 2 V2a, the reference trapdoor. The V2a pass never writes the trapdoor: it puts the salts and the inverse
quartet replies into the record blocks. The V1 bridge (`Layout2Area.l2_proof_convert`, `GroupOpenModel`) is
stated for a trapdoor that holds them where V1's pass rebuilt them: the opened salts in the stash words and the
inverses of the opened quartets' replies in their rebuilt blocks. `refState o td p` is the loaded input with those
words filled in (a pure definition, no machine run), `refTd o td p` its trapdoor; the facts below are the four
facts V1 derived from its pass (heap and quartet nodes kept, rebuilt blocks, salts). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening
open TwoPermutationPrototype.Sampling (saltWords)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Word `w` of the reference state, from the loaded word `old`. -/
noncomputable def refWord (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat) (old : Word) :
    Word :=
  if h : 1140851204 ≤ w ∧ w<1140851204+2*16777216 then
    if (⟨(w-1140851204)/2,by change _<16777216; omega⟩ : Index) ∈ p then
      saltWords (linkedSalts o (keyOf td) ⟨(w-1140851204)/2,by change _<16777216; omega⟩) ⟨(w-1140851204)%2,by omega⟩
    else old
  else if h : 603980356 ≤ w ∧ (w-603980356)%128<25 ∧ (w-603980356)/128<4194304 then
    if ∃ i ∈ p, i.val/4=(w-603980356)/128 then
      replyWords (o.permutation.symm (groupReply td ((w-603980356)/128))) ⟨(w-603980356)%128,h.2.1⟩
    else old
  else old

/-- The reference state: the loaded input with the opened salts and rebuilt blocks. -/
noncomputable def refState (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) : MachineState :=
  { actual.initialState .opening (td,p) with
    mem := fun a => if a.toNat%8=0 then refWord o td p (a.toNat/8) ((actual.initialState .opening (td,p)).mem a)
      else (actual.initialState .opening (td,p)).mem a }

/-- The reference trapdoor. -/
noncomputable def refTd (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    BitVec (8*actual.sizes.trapdoor) := virtualTd (refState o td p)

theorem ref_view (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat) (hw : w<2^33) :
    memoryView (refState o td p) w=refWord o td p w (memoryView (actual.initialState .opening (td,p)) w) := by
  have t : (wordAddress w).toNat=8*w := by unfold wordAddress; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change (if (wordAddress w).toNat%8=0 then _ else _)=_
  rw [t, if_pos (by omega), show 8*w/8=w by omega]; rfl

/-- Outside the stash and the rebuilt blocks the reference state is the loaded input. -/
theorem ref_kept (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (w : Nat) (hw : w<2^33)
    (salt : w<1140851204 ∨ 1140851204+2*16777216 ≤ w)
    (block : w<603980356 ∨ 25 ≤ (w-603980356)%128 ∨ 4194304 ≤ (w-603980356)/128) :
    memoryView (refState o td p) w=memoryView (actual.initialState .opening (td,p)) w := by
  rw [ref_view o td p w hw]; unfold refWord
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem ref_salt (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (i : Index) (member : i∈p)
    (j : Fin 2) : memoryView (refState o td p) (1140851204+2*i.val+j.val)=saltWords (linkedSalts o (keyOf td) i) j := by
  have ix : i.val<16777216 := i.isLt
  have jj := j.isLt
  rw [ref_view o td p _ (by omega)]; unfold refWord
  rw [dif_pos (by omega)]
  have e1 : (1140851204+2*i.val+j.val-1140851204)/2=i.val := by omega
  have e2 : (1140851204+2*i.val+j.val-1140851204)%2=j.val := by omega
  have hi : (⟨(1140851204+2*i.val+j.val-1140851204)/2,by change _<16777216; omega⟩ : Index)=i := Fin.ext e1
  simp only [hi, member, if_true]
  exact congrArg _ (Fin.ext e2)

theorem ref_block (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (i : Index) (member : i∈p)
    (m : Nat) (hm : m<25) :
    memoryView (refState o td p) (rebuiltWord (i.val/4)+m)=
      replyWords (o.permutation.symm (groupReply td (i.val/4))) ⟨m,hm⟩ := by
  have ix : i.val<16777216 := i.isLt
  have rw0 : rebuiltWord (i.val/4)+m=603980356+128*(i.val/4)+m := by unfold rebuiltWord blockWord; omega
  rw [ref_view o td p _ (by rw [rw0]; omega)]; unfold refWord
  rw [rw0, dif_neg (by omega), dif_pos (by omega)]
  have e1 : (603980356+128*(i.val/4)+m-603980356)/128=i.val/4 := by omega
  have e2 : (603980356+128*(i.val/4)+m-603980356)%128=m := by omega
  rw [if_pos ⟨i,member,e1.symm⟩]
  simp only [e1]
  exact congrArg _ (Fin.ext e2)

/-- A slice of `cells` reference words outside the stash and the rebuilt blocks reads as the trapdoor's. -/
theorem ref_slice (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (off cells : Nat)
    (size : cells≤8) (a : off%8=0) (room : off+8*cells≤5100273664)
    (fresh : ∀ c<cells, let w:=536871428+off/8+c;
      (w<1140851204 ∨ 1140851204+2*16777216 ≤ w) ∧ (w<603980356 ∨ 25 ≤ (w-603980356)%128 ∨ 4194304 ≤ (w-603980356)/128)) :
    (refTd o td p).extractLsb' (8*off) (8*(8*cells))=td.extractLsb' (8*off) (8*(8*cells)) := by
  have room' : off+8*cells≤trapdoorBytes := by change _≤5100273664;omega
  unfold refTd
  rw [virtual_slice _ off _ (by rwa [actual_layout.trapdoorSize]),←input_trapdoor_slice actual actual_layout td p off _ room']
  apply Opening.copied_buffer _ _ _ _ _ (by unfold trapdoorBase LENGTH LOG_LENGTH;omega)
    (by unfold trapdoorBase LENGTH LOG_LENGTH;omega) size
  intro i hi
  have ea : trapdoorBase+off+8*i=8*(536871428+off/8+i) := by unfold trapdoorBase LENGTH LOG_LENGTH;omega
  rw [ea]
  obtain ⟨f1,f2⟩ := fresh i hi
  exact ref_kept o td p _ (by omega) f1 f2

theorem ref_heap (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (n : Nat) (hn : n<4194304) :
    Opening.trapdoorHeap (s:=actual) (refTd o td p) n=Opening.trapdoorHeap (s:=actual) td n := by
  have v:=ref_slice o td p (32*n) 4 (by decide) (by omega) (by omega) (fun c hc => by dsimp only; omega)
  simpa only [Opening.trapdoorHeap,←Nat.mul_assoc] using v

theorem ref_quad (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (idx : Index) :
    trapdoorQuad (s:=actual) (refTd o td p) idx=trapdoorQuad (s:=actual) td idx := by
  have ix : idx.val<16777216:=idx.isLt
  set h:=idx.val/4^^^1 with hh
  have hx : h<4194304 := xor_one_lt (idx.val/4) 22 (by omega) (by decide)
  have tb : trapdoorBase=4294971424 := rfl
  have nw : nodeWordOf h=603980292+128*(2*(h/2))+21-4*(h%2) := rfl
  have q := quad_address_node idx.val
  rw [← hh] at q
  have n1 : trapdoorBase≤8*nodeWordOf h := by rw [tb,nw]; omega
  have n2 : 8*nodeWordOf h-trapdoorBase+32≤5100273664 := by rw [tb,nw]; omega
  have v := ref_slice o td p (8*nodeWordOf h-trapdoorBase) 4 (by decide) (by rw [tb]; omega) (by omega)
    (fun c hc => by
      dsimp only
      rw [show 536871428+(8*nodeWordOf h-trapdoorBase)/8+c=nodeWordOf h+c by rw [tb]; omega, nw]
      have : h%2<2 := Nat.mod_lt _ (by decide)
      constructor
      · omega
      · omega)
  unfold trapdoorQuad
  rw [q]
  exact v

theorem ref_rebuilt (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (idx : Index) (member : idx∈p) :
    (refTd o td p).extractLsb' (8*(32*LENGTH+512+1024*(idx.val/4))) 1600=o.permutation.symm (groupReply td (idx.val/4)) := by
  have ix : idx.val<16777216:=idx.isLt
  set q:=idx.val/4 with hq
  have v : (refTd o td p).extractLsb' (8*(32*LENGTH+512+1024*q)) 1600=readBuffer (refState o td p) (8*rebuiltWord q) 200 := by
    rw [show 8*rebuiltWord q=trapdoorBase+(32*LENGTH+512+1024*q) by
      unfold rebuiltWord blockWord trapdoorBase LENGTH LOG_LENGTH; omega]
    exact virtual_slice _ _ 200 (by change _≤5100273664; unfold LENGTH LOG_LENGTH; omega)
  rw [v]
  apply aligned_buffer_eq _ _ 200 (by decide)
  intro c hc
  rw [ref_block o td p idx member c (by omega)]
  rfl

theorem ref_salt_slice (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (idx : Index)
    (member : idx∈p) : trapdoorSalt (s:=actual) (refTd o td p) idx=linkedSalts o (keyOf td) idx := by
  have iBound : idx.val<16777216:=idx.isLt
  unfold trapdoorSalt refTd
  rw [virtual_slice _ _ 16 (by change 288*16777216+16*idx.val+16≤5100273664;omega)]
  rw [show trapdoorBase+(288*LENGTH+16*idx.val)=8*(1140851204+2*idx.val) by unfold trapdoorBase LENGTH LOG_LENGTH;omega]
  apply aligned_buffer_eq _ _ 16 (by decide)
  intro b hb
  exact ref_salt o td p idx member ⟨b,hb⟩

/-- The reference state agrees with the reference trapdoor's fresh load on the input. -/
theorem ref_input (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) :
    SameOpeningInput (actual.initialState .opening (refTd o td p,p)) (refState o td p) := by
  apply virtual_input td p
  intro a lo hi al
  have w := ref_kept o td p (a/8) (by have : proofBase<2^36 := by decide
                                      omega)
    (by unfold trapdoorBase trapdoorBytes LENGTH LOG_LENGTH at lo; omega)
    (by unfold trapdoorBase trapdoorBytes LENGTH LOG_LENGTH at lo; omega)
  have ea : wordAddress (a/8)=BitVec.ofNat 64 a := by unfold wordAddress; congr 1; omega
  simpa only [memoryView, ea] using w

end TwoPermutationPrototype.GroupedOpening.Layout2V2
