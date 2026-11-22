import CommitGolfCandidate.Layout2V2Ref
import CommitGolfCandidate.Layout2Area
import CommitGolfCandidate.Layout2QuartetCodec

/-! Layout 2 V2a, the bridge from the machine's proof to V1's. The V2a opener outputs `l2ProofFromPass td pass p`
(record blocks: the writers' dwords and the bytes the pass left). When the pass left every record's linked salt and
the inverse of its quartet's reply in its block (`Seen`), that proof is Astra's quartet transform
`Quartet.transform true k (selectors p)` of V1's proof `l2ProofFromTrapdoor` of the reference trapdoor
`refTd o td p` (`pass_proof_eq`): inside each record's 184-byte window the transform moves V1's mates, level-0,
level-1 and A0 dwords to where the V2a writers put them; elsewhere it is the identity. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase (stride phaseBase writerByte writerCarry writerDwords recordSource)
open CommitGolfCandidate.Layout2Phase2 (written writtenByte v1Dword)
open TwoPermutationPrototype.Sampling (saltWords)
open Opening (openingNodes)
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! ### Bytes of words -/

theorem byte_view (s : MachineState) (w r : Nat) (hr : r<8) (hw : w<2^33) :
    s.getByte (BitVec.ofNat 64 (8*w+r))=(memoryView s w).extractLsb' (8*r) 8 := by
  have fx : 8*w+r<2^64 := by omega
  unfold MachineState.getByte
  rw [table_align_eq _ fx, table_offset_nat _ fx, show 8*w+r-(8*w+r)%8=8*w by omega, show (8*w+r)%8=r by omega]
  change extractByte (s.getMem (BitVec.ofNat 64 (8*w))) r=(s.getMem (BitVec.ofNat 64 (8*w))).extractLsb' (8*r) 8
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  simp [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', Nat.mul_comm]

theorem word_byte {n : Nat} (v : BitVec n) (a y : Nat) (hy : y<8) :
    (v.extractLsb' (64*a) 64).extractLsb' (8*y) 8=v.extractLsb' (8*(8*a+y)) 8 := by
  rw [ext_ext _ _ _ _ _ (by omega)]; congr 1; omega

/-! ### Source agreement between the trapdoor and the reference trapdoor (sources `k ≥ 112`) -/

theorem dword_congr2 {src src' : Nat → Byte} (k : Nat) (h : ∀ i, k ≤ i → i<k+8 → src i=src' i) :
    Layout2Phase.dwordOf src k=Layout2Phase.dwordOf src' k := by
  simp only [Layout2Phase.dwordOf, h k (by omega) (by omega), h (k+1) (by omega) (by omega), h (k+2) (by omega) (by omega),
    h (k+3) (by omega) (by omega), h (k+4) (by omega) (by omega), h (k+5) (by omega) (by omega),
    h (k+6) (by omega) (by omega), h (k+7) (by omega) (by omega)]

theorem stream_congr2 (p : Nat) {src src' : Nat → Byte} (c : Word) (h : ∀ i, 304 ≤ i → i<560 → src i=src' i) :
    Layout2Phase.streamRun p src c=Layout2Phase.streamRun p src' c := by
  unfold Layout2Phase.streamRun
  congr 1
  apply List.map_congr_left
  intro b hb
  simp only [List.mem_range] at hb
  exact dword_congr2 _ (fun i hi hi' => h i (by omega) (by omega))

theorem carry_congr2 (p : Nat) {src src' : Nat → Byte} (c : Word) (h : ∀ i, 304 ≤ i → i<560 → src i=src' i) :
    writerCarry p src c=writerCarry p src' c := by
  unfold writerCarry; rw [stream_congr2 p c h]

theorem high_congr2 (p : Nat) {src src' : Nat → Byte} (c : Word) (h : ∀ i, 112 ≤ i → i<560 → src i=src' i) :
    Layout2Phase2.writerHigh p src c=Layout2Phase2.writerHigh p src' c := by
  have d : ∀ k, 112 ≤ k → k+8 ≤ 560 → Layout2Phase.dwordOf src k=Layout2Phase.dwordOf src' k :=
    fun k hk hk' => dword_congr2 k (fun i hi hi' => h i (by omega) (by omega))
  unfold Layout2Phase2.writerHigh Layout2Phase.bandATails Layout2Phase.tailA
  rw [stream_congr2 p c (fun i hi hi' => h i (by omega) hi')]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · congr 1
          · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega) (by omega)
          · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega) (by omega)
        · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega) (by omega)
      · simp only [d 200 (by omega) (by omega), d 232 (by omega) (by omega), d 264 (by omega) (by omega),
          d 296 (by omega) (by omega)]
    · apply List.map_congr_left; intro i hi; simp only [List.mem_range] at hi; exact d _ (by omega) (by omega)

theorem written_congr2 (p : Nat) {src src' : Nat → Byte} (c : Word) (j : Nat)
    (h : ∀ i, 112 ≤ i → i<560 → src i=src' i) : writtenByte p src c j=writtenByte p src' c j := by
  have ge := (Layout2Phase2.v1Dword_ge (j/8)).1
  unfold writtenByte
  rw [Layout2Phase2.writer_split, Layout2Phase2.writer_split]
  have len : ∀ s : Nat → Byte, ([Layout2Phase.dwordOf s 0, Layout2Phase.dwordOf s 8] ++
      (List.range 12).map (fun i => Layout2Phase.dwordOf s (16+8*i))).length=14 := by intro s; simp
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [len]; omega),
    List.getElem?_append_right (by rw [len]; omega), len, len, high_congr2 p c h]

section
variable (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions)

/-- The trapdoor and the reference trapdoor give every record the same sources from 112 on. -/
theorem src_agree (j : Nat) (i : Nat) (lo : 112 ≤ i) (hi : i<560) :
    srcAt (actual.initialState .opening (td,p)) p j i=srcAt (actual.initialState .opening (refTd o td p,p)) p j i := by
  by_cases q : i<144
  · rw [src_quad actual actual_layout td p j i lo q, src_quad actual actual_layout _ p j i lo q, ref_quad]
  · have hp := pos_at_lt p j
    have node : upperNode (posAt p j) ((i-112)/32) ^^^ 1<4194304 := by
      apply Nat.xor_lt_two_pow (n := 22) _ (by decide)
      unfold upperNode Opening.lowerNode
      have pw : 2^3 ≤ 2^((i-112)/32+2) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      unfold LENGTH LOG_LENGTH; norm_num
      omega
    rw [src_heap actual actual_layout td p j i (by omega) hi, src_heap actual actual_layout _ p j i (by omega) hi,
      ref_heap o td p _ node]

theorem carry_agree (j : Nat) :
    carryAt (actual.initialState .opening (td,p)) p j=carryAt (actual.initialState .opening (refTd o td p,p)) p j := by
  induction j with
  | zero => simp only [carryAt]
  | succ j ih =>
    simp only [carryAt]
    rw [ih, carry_congr2 _ _ (fun i hi hi' => src_agree o td p j i (by omega) hi')]

end

/-! ### Geometry of the blocks against the nominal cells -/

theorem dest_sub (j : Nat) : destOf j-proofBase=2136*(j/4)+phaseBase (j%4) := by unfold destOf; omega

theorem dest_cell (j : Nat) : 534*j ≤ destOf j-proofBase+6 ∧ destOf j-proofBase ≤ 534*j ∧
    destOf j-proofBase+stride (j%4) ≤ 534*(j+1) := by
  rw [dest_sub]; unfold phaseBase stride
  have h := Nat.mod_lt j (show 4>0 by decide)
  split_ifs <;> omega

theorem dest_window (j : Nat) :
    534*j+CommitGolfCandidate.Layout2.Quartet.window j=destOf j-proofBase+16 := by
  rw [CommitGolfCandidate.Layout2.Quartet.window_base, dest_sub]
  unfold phaseBase
  have h := Nat.mod_lt j (show 4>0 by decide)
  split_ifs <;> omega

theorem pass_dest_eq (j : Nat) : passDest j=destOf j := rfl

/-- The prefix of `n` blocks. -/
theorem flat_length (f : Nat → Proof) (len : ∀ j, (f j).length=stride (j%4)) (n : Nat) :
    ((List.range n).flatMap f).length=destOf n-proofBase := by
  induction n with
  | zero => simp [dest_zero]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton, len]
    have := dest_next n; have := dest_bound n; omega

theorem flat_get (f : Nat → Proof) (len : ∀ j, (f j).length=stride (j%4)) (n j y : Nat) (hj : j<n)
    (hy : y<stride (j%4)) : ((List.range n).flatMap f)[destOf j-proofBase+y]?=(f j)[y]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases h : j<n
    · have m := dest_mono j n h
      have b := dest_bound j
      rw [List.getElem?_append_left (by rw [flat_length f len]; omega)]; exact ih h
    · have e : j=n := by omega
      subst e
      rw [List.getElem?_append_right (by rw [flat_length f len]; omega), flat_length f len, Nat.add_sub_cancel_left]

theorem locate (n i : Nat) (hi : i<destOf n-proofBase) :
    ∃ j<n, destOf j-proofBase ≤ i ∧ i<destOf (j+1)-proofBase := by
  induction n with
  | zero => rw [dest_zero] at hi; omega
  | succ n ih =>
    by_cases h : i<destOf n-proofBase
    · obtain ⟨j,hj,a,b⟩ := ih h; exact ⟨j,by omega,a,b⟩
    · exact ⟨n,by omega,by omega,hi⟩

open CommitGolfCandidate.Layout2.Quartet (window within) in
/-- Inside record `j`'s block the transform's index is the block offset `within true q 16 y`. -/
theorem index_block (k : Nat) (qs : CommitGolfCandidate.Layout2.Quartet.Selectors) (j y : Nat) (hj : j<k)
    (hy : y<stride (j%4)) :
    CommitGolfCandidate.Layout2.Quartet.index true k qs (destOf j-proofBase+y)=
      destOf j-proofBase+within true (qs j) 16 y := by
  obtain ⟨c1,c2,c3⟩ := dest_cell j
  have wb := dest_window j
  have hk : 534*(j+1) ≤ 534*k := by omega
  unfold CommitGolfCandidate.Layout2.Quartet.index
  rw [if_pos (by omega)]
  dsimp only
  by_cases win : 16 ≤ y ∧ y<16+184
  · have cell : (destOf j-proofBase+y)/534=j := by omega
    have off : (destOf j-proofBase+y)%534=CommitGolfCandidate.Layout2.Quartet.window j+(y-16) := by omega
    rw [cell, off]
    unfold CommitGolfCandidate.Layout2.Quartet.within
    rw [if_pos (by omega), if_pos win,
      show CommitGolfCandidate.Layout2.Quartet.window j+(y-16)-CommitGolfCandidate.Layout2.Quartet.window j=y-16 by omega]
    omega
  · obtain ⟨c,hc⟩ : ∃ c, (destOf j-proofBase+y)/534=c := ⟨_,rfl⟩
    have cases : c=j ∨ c+1=j := by omega
    have xm : (destOf j-proofBase+y)%534=destOf j-proofBase+y-534*c := by omega
    unfold CommitGolfCandidate.Layout2.Quartet.within
    rw [if_neg win, hc, xm]
    unfold CommitGolfCandidate.Layout2.Quartet.window at wb ⊢
    rcases cases with e|e
    · subst e
      rw [if_neg (by omega)]
      omega
    · subst e
      rw [if_neg (by omega)]
      omega

open CommitGolfCandidate.Layout2.Quartet (window within) in
/-- From the end of the records on the transform is the identity. -/
theorem index_tail (k : Nat) (qs : CommitGolfCandidate.Layout2.Quartet.Selectors) (i : Nat)
    (hi : destOf k-proofBase ≤ i) : CommitGolfCandidate.Layout2.Quartet.index true k qs i=i := by
  obtain ⟨c1,c2,_⟩ := dest_cell k
  unfold CommitGolfCandidate.Layout2.Quartet.index
  split
  · dsimp only
    unfold CommitGolfCandidate.Layout2.Quartet.within
    rw [if_neg (by unfold CommitGolfCandidate.Layout2.Quartet.window; omega)]
    omega
  · rfl

/-! ### The finite facts of the quartet permutation in one block -/

open CommitGolfCandidate.Layout2.Quartet (within) in
theorem written_index : ∀ q : Fin 4, ∀ y<536, written q.val (y/8)=true →
    (within true q 16 y)/8=v1Dword (y/8) ∧ (within true q 16 y)%8=y%8 := by decide +kernel

open CommitGolfCandidate.Layout2.Quartet (within) in
/-- A retained byte is a salt byte (fixed) or a byte of a mate slot `s ≠ q`, which the transform takes from V1's
mate `(s xor q) - 1` (V1 offset `16 + 32 m + r`). -/
theorem retained_index : ∀ q : Fin 4, ∀ y<536, written q.val (y/8)=false →
    (y<16 ∧ within true q 16 y=y) ∨
    (72 ≤ y ∧ y<200 ∧ 16 ≤ within true q 16 y ∧ within true q 16 y<112 ∧
      q.val ^^^ ((within true q 16 y-16)/32+1)=(y-72)/32 ∧ (within true q 16 y-16)/32<3 ∧
      (within true q 16 y-16)%32=(y-72)%32) := by decide +kernel

open CommitGolfCandidate.Layout2.Quartet (within) in
theorem within_block : ∀ q : Fin 4, ∀ y<536, within true q 16 y<536 ∧ (y<528 → within true q 16 y<528) := by
  decide +kernel

/-! ### One record -/

theorem reply_byte (R : BitVec PERMUTATION_WIDTH) (m : Fin 25) (r : Nat) (hr : r<8) :
    (replyWords R m).extractLsb' (8*r) 8=R.extractLsb' (8*(8*m.val+r)) 8 := by
  unfold replyWords; exact word_byte _ _ _ hr

theorem salt_byte (v : BitVec 128) (m : Fin 2) (r : Nat) (hr : r<8) :
    (saltWords v m).extractLsb' (8*r) 8=v.extractLsb' (8*(8*m.val+r)) 8 := by
  unfold saltWords; exact word_byte _ _ _ hr

private theorem xor_low (n j : Nat) (small : j<4) : n ^^^ j=4*(n/4)+(n%4 ^^^ j) := by
  have g : (n ^^^ j)/2^2=n/2^2 := by
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    have zero : j >>> 2=0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt small
    simp [zero]
  have p : (n ^^^ j)%2^2=n%2^2 ^^^ j := by
    rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt (show j<2^2 by omega)]
  have split := Nat.div_add_mod (n ^^^ j) (2^2)
  rw [g, p] at split
  simp only [show (2:Nat)^2=4 from rfl] at split
  omega

private theorem small_xor (a b : Nat) (ha : a<4) (hb : b<4) : a ^^^ b<4 :=
  Nat.xor_lt_two_pow (n := 2) ha hb

theorem pos_at_mem (p : Positions) (j : Nat) (hj : j<p.card) : posAt p j∈p := by
  rw [pos_at_eq p j hj]; unfold Opening.sortedIndex
  exact (Finset.mem_sort _).mp (List.getElem_mem _)

theorem pos_eq_pos_at (p : Positions) (j : Nat) (hj : j<p.card) : pos p j=posAt p j :=
  (pos_present p j hj).trans (pos_at_eq p j hj).symm

theorem selectors_at (p : Positions) (j : Nat) (hj : j<p.card) :
    (CommitGolfCandidate.Layout2.Quartet.selectors p j).val=(posAt p j).val%4 := by
  rw [← pos_eq_pos_at p j hj]; rfl

theorem dest_word (j y : Nat) (hj : j<16777216) (hy : y<536) :
    destOf j+y=8*(passWord j+y/8)+y%8 ∧ passWord j+y/8<2^33 := by
  have m := pass_word_mul j
  have b := dest_bound j
  have pb : proofBase=13824430176 := rfl
  rw [pass_dest_eq] at m
  constructor <;> omega

open CommitGolfCandidate.Layout2.Quartet (within) in
/-- A block byte of the V2a proof is the V1 block byte the transform takes it from. -/
theorem record_match (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (pass : MachineState)
    (seen : Seen o (keyOf td) td p pass p.card) (j y : Nat) (hj : j<p.card) (hy : y<stride (j%4)) :
    v2Byte (actual.initialState .opening (td,p)) pass p j y=
      writerByte (j%4) (srcAt (actual.initialState .opening (refTd o td p,p)) p j)
        (carryAt (actual.initialState .opening (refTd o td p,p)) p j)
        (within true (CommitGolfCandidate.Layout2.Quartet.selectors p j) 16 y) := by
  have sel := selectors_at p j hj
  have y536 : y<536 := by unfold stride at hy; split at hy <;> omega
  have member := pos_at_mem p j hj
  have px := (posAt p j).isLt
  change _<16777216 at px
  obtain ⟨dw,dwb⟩ := dest_word j y (by have := card_le p; omega) y536
  unfold v2Byte
  by_cases hw : written ((posAt p j).val%4) (y/8)=true
  · rw [if_pos hw]
    obtain ⟨i8,m8⟩ := written_index (CommitGolfCandidate.Layout2.Quartet.selectors p j) y y536 (by rw [sel]; exact hw)
    rw [carry_agree o td p j, written_congr2 _ _ _ (src_agree o td p j)]
    unfold writtenByte writerByte; rw [i8, m8]
  · have hw' : written ((posAt p j).val%4) (y/8)=false := by simpa using hw
    rw [if_neg hw]
    rcases retained_index (CommitGolfCandidate.Layout2.Quartet.selectors p j) y y536 (by rw [sel]; exact hw') with
      ⟨ys,wy⟩|⟨y1,y2,z1,z2,zx,zm,zr⟩
    · -- a salt byte
      rw [wy, Layout2.writer_copy _ _ _ _ (by omega), src_salt actual actual_layout _ p j y ys,
        ref_salt_slice o td p _ member, dw, byte_view pass _ _ (by omega) dwb]
      have st := seen.salt j hj ⟨y/8,by omega⟩
      rw [pos_eq_pos_at p j hj] at st
      rw [st, salt_byte _ _ (y%8) (by omega)]
      dsimp only
      rw [show 8*(8*(y/8)+y%8)=8*y by omega]
    · -- a mate byte
      set z := within true (CommitGolfCandidate.Layout2.Quartet.selectors p j) 16 y with hz
      rw [sel] at zx
      have mm : (z-16)/32+1<4 := by omega
      have xl := xor_low (posAt p j).val ((z-16)/32+1) mm
      have xs := small_xor ((posAt p j).val%4) ((z-16)/32+1) (by omega) mm
      rw [Layout2.writer_copy _ _ _ _ (by omega), src_mate actual actual_layout _ p j z z1 z2]
      unfold trapdoorLeaf
      rw [xl, show (4*((posAt p j).val/4)+((posAt p j).val%4 ^^^ ((z-16)/32+1)))/4=(posAt p j).val/4 by omega,
        show (4*((posAt p j).val/4)+((posAt p j).val%4 ^^^ ((z-16)/32+1)))%4=(posAt p j).val%4 ^^^ ((z-16)/32+1) by omega,
        zx, ext_ext _ _ _ _ _ (by omega),
        show 8*(32*LENGTH+512+1024*((posAt p j).val/4)+72+32*((y-72)/32))+8*((z-16)%32)=
          8*(32*LENGTH+512+1024*((posAt p j).val/4))+8*y by rw [zr]; omega,
        ← ext_ext (refTd o td p) (8*(32*LENGTH+512+1024*((posAt p j).val/4))) 1600 (8*y) 8 (by omega),
        ref_rebuilt o td p _ member, dw, byte_view pass _ _ (by omega) dwb]
      have rp := seen.reply j hj (y/8) (by omega) (by omega)
      rw [pos_eq_pos_at p j hj] at rp
      rw [rp, reply_byte _ _ (y%8) (by omega)]
      dsimp only
      rw [show 8*(8*(y/8)+y%8)=8*y by omega]
      all_goals rfl

/-! ### The whole proof -/

theorem phys2_get (L pass : MachineState) (p : Positions) (j y : Nat) (hy : y<stride (j%4)) :
    (physRecord2 L pass p j)[y]?.getD 0=v2Byte L pass p j y := by
  simp [physRecord2, List.getElem?_map, List.getElem?_range hy]

theorem phys1_get (L : MachineState) (p : Positions) (j z : Nat) (hz : z<stride (j%4)) :
    (physRecord L p j)[z]?.getD 0=writerByte (j%4) (srcAt L p j) (carryAt L p j) z := by
  simp [physRecord, List.getElem?_map, List.getElem?_range hz]

set_option maxRecDepth 200000 in
open CommitGolfCandidate.Layout2.Quartet (within transform selectors read_transform) in
/-- The V2a opener's proof is the quartet transform of V1's proof from the reference trapdoor. -/
theorem pass_proof_eq (o : Oracle) (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (pass : MachineState)
    (seen : Seen o (keyOf td) td p pass p.card) :
    l2ProofFromPass (s:=actual) td pass p=
      transform true p.card (selectors p) (l2ProofFromTrapdoor (s:=actual) (refTd o td p) p) := by
  let L1 := actual.initialState .opening (refTd o td p,p)
  let L2 := actual.initialState .opening (td,p)
  have len1 : ∀ j, (physRecord L1 p j).length=stride (j%4) := by intro j; simp [physRecord]
  have len2 : ∀ j, (physRecord2 L2 pass p j).length=stride (j%4) := by intro j; simp [physRecord2]
  have flushEq : physFlush L2 p=physFlush L1 p := by unfold physFlush; rw [carry_agree o td p]
  have capEq : (openingNodes p).map (Opening.trapdoorHeap (s:=actual) td)=
      (openingNodes p).map (Opening.trapdoorHeap (s:=actual) (refTd o td p)) := by
    apply List.map_congr_left
    intro n hn
    have small : n<512 := by
      unfold openingNodes at hn
      split at hn
      · simp at hn
      · exact Opening.cap_frontier_nodes_small _ 1 8 Opening.cap_span_root n hn
    exact (ref_heap o td p n (by omega)).symm
  unfold l2ProofFromPass l2Proof2 l2ProofFromTrapdoor l2Proof
  change (List.range p.card).flatMap (physRecord2 L2 pass p) ++ physFlush L2 p ++ _=
    transform true p.card (selectors p) ((List.range p.card).flatMap (physRecord L1 p) ++ physFlush L1 p ++ _)
  rw [flushEq, capEq]
  generalize hT : physFlush L1 p ++ foldNodes ((openingNodes p).map (Opening.trapdoorHeap (s:=actual) (refTd o td p)))=T
  rw [List.append_assoc, List.append_assoc, hT]
  have f1 := flat_length _ len1 p.card
  have f2 := flat_length _ len2 p.card
  have flushLen' : (physFlush L1 p).length=flushLen ((p.card+3)%4) := by simp [physFlush]
  have complete : 534*p.card ≤ ((List.range p.card).flatMap (physRecord L1 p)++T).length := by
    rw [List.length_append, f1, ← hT, List.length_append, flushLen']
    have := dest_end p.card; have := dest_bound p.card; omega
  apply List.ext_getElem
  · rw [CommitGolfCandidate.Layout2.Quartet.length_transform, List.length_append, List.length_append, f1, f2]
  · intro i h2 h1
    have hT1 : i<((List.range p.card).flatMap (physRecord L1 p)++T).length := by
      rwa [CommitGolfCandidate.Layout2.Quartet.length_transform] at h1
    have r := read_transform true p.card (selectors p) _ i complete hT1
    rw [List.getElem?_eq_getElem h1, Option.getD_some] at r
    rw [r, show ((List.range p.card).flatMap (physRecord2 L2 pass p)++T)[i]=
      (((List.range p.card).flatMap (physRecord2 L2 pass p)++T)[i]?).getD 0 by rw [List.getElem?_eq_getElem h2]; rfl]
    by_cases rec : i<destOf p.card-proofBase
    · obtain ⟨j,hj,lo,hi⟩ := locate p.card i rec
      have nx := dest_next j
      have bd := dest_bound j
      set y := i-(destOf j-proofBase) with hyd
      have hy : y<stride (j%4) := by omega
      have ie : i=destOf j-proofBase+y := by omega
      have y536 : y<536 := by unfold stride at hy; split_ifs at hy <;> omega
      have wb : within true (selectors p j) 16 y<stride (j%4) := by
        have := within_block (selectors p j) y y536
        unfold stride at hy ⊢; split_ifs at hy ⊢ <;> omega
      rw [ie, index_block p.card (selectors p) j y hj hy,
        List.getElem?_append_left (by rw [f2]; omega), List.getElem?_append_left (by rw [f1]; have := dest_mono j p.card hj; omega),
        flat_get _ len2 p.card j y hj hy, flat_get _ len1 p.card j _ hj wb]
      rw [phys2_get _ _ _ _ _ hy, phys1_get _ _ _ _ wb]
      exact record_match o td p pass seen j y hj hy
    · rw [index_tail p.card (selectors p) i (by omega),
        List.getElem?_append_right (by rw [f2]; omega), List.getElem?_append_right (by rw [f1]; omega), f1, f2]

end TwoPermutationPrototype.GroupedOpening.Layout2V2
