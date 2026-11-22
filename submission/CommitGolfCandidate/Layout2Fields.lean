import CommitGolfCandidate.Layout2Sources
import CommitGolfCandidate.Layout2ProofBytes
import CommitGolfCandidate.Layout2OpenerBridge

/-! Layout 2 opener, part 2: the machine's record area is Neon's V1 layout. On clean digests (band A bits
`240..255` and band B bits `238..255` zero, as on every honest heap), record `j`'s block
`writerByte (j%4) (srcAt j) (carryAt j)` is `newPhaseBytes (j%4)` of its 4-record block, the physical carry
`carryAt j` is `streamCarry` of the block, the flush is `newPartialFlush`, so `l2Proof = newProofBytes`, and with
Neon's `convert_enc_proofFromTrapdoor` the opener's proof is `convert encTables k` of today's proof. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate Sampling
open CommitGolfCandidate.Layout2Phase (stride writerByte writerCarry streamRun streamStep tailA tailB dwordOf
  bandATails carryIn)
open CommitGolfCandidate.Layout2 (RecordFields BandBClean leBytes wordBytes newPhaseFixedBytes newPhaseBytes
  newPartialFlush newBlockBytes newProofBytes phaseStreamCount phaseStreamStart bandATailWord bandBStreamDword
  streamCarry bandBTailWord46 trapdoorRecordFields recordFieldsOf convert encTables newPhaseFixedBytes_salt
  newPhaseFixedBytes_mate0 newPhaseFixedBytes_mate1 newPhaseFixedBytes_mate2 newPhaseFixedBytes_sib0
  newPhaseFixedBytes_sib1 newPhaseFixedBytes_bandA0 newPhaseFixedBytes_bandA1 newPhaseFixedBytes_bandA2
  newPhaseFixedBytes_bandA3 newPhaseFixedBytes_bandATail0 newPhaseFixedBytes_bandATail1 newPhaseFixedBytes_bandATail2
  newPhaseFixedBytes_bandB_body newPhaseFixedBytes_length newPhaseBytes_length newPhaseBytes_stream_dword
  streamCarry_one streamCarry_step_lt streamCarry_step_gt streamCarry_step_eq streamCarry_flush_r1
  streamCarry_flush_r2 streamCarry_flush_r3)
open Opening (openingNodes)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- Byte `k < 560` of a record's sources in field terms (salt, mates, level 0, level 1, band A, band B). -/
def fieldByte (f : RecordFields) (k : Nat) : Byte :=
  if k<16 then f.salt.extractLsb' (8*k) 8
  else if h : k<112 then (f.mate ⟨(k-16)/32, by omega⟩).extractLsb' (8*((k-16)%32)) 8
  else if k<144 then f.sib0.extractLsb' (8*(k-112)) 8
  else if k<176 then f.sib1.extractLsb' (8*(k-144)) 8
  else if h : k<304 then (f.bandA ⟨(k-176)/32, by omega⟩).extractLsb' (8*((k-176)%32)) 8
  else if h : k<560 then (f.bandB ⟨(k-304)/32, by omega⟩).extractLsb' (8*((k-304)%32)) 8
  else 0

theorem record_fields (s : Submission) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (j : Nat)
    (hj : j<positions.card) :
    trapdoorRecordFields (s:=s) t positions j=
      recordFieldsOf (trapdoorLeaf (s:=s) t) (Opening.trapdoorHeap (s:=s) t) (trapdoorQuad (s:=s) t (posAt positions j))
        (posAt positions j) (trapdoorSalt (s:=s) t (posAt positions j)) := by
  unfold trapdoorRecordFields
  have hl : j<(positions.sort (·≤·)).length := by simpa using hj
  rw [dif_pos hl, pos_at_eq positions j hj]
  rfl

/-- The record's sources are its fields. -/
theorem src_field (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (j : Nat) (hj : j<positions.card) (k : Nat) (hk : k<560) :
    srcAt (s.initialState .opening (t, positions)) positions j k=fieldByte (trapdoorRecordFields (s:=s) t positions j) k := by
  rw [record_fields s t positions j hj]
  unfold fieldByte
  by_cases h16 : k<16
  · rw [if_pos h16, src_salt s layout t positions j k h16]; rfl
  by_cases h112 : k<112
  · rw [if_neg h16, dif_pos h112, src_mate s layout t positions j k (by omega) h112]; rfl
  by_cases h144 : k<144
  · rw [if_neg h16, dif_neg h112, if_pos h144, src_quad s layout t positions j k (by omega) h144]; rfl
  rw [if_neg h16, dif_neg h112, if_neg h144, src_heap s layout t positions j k (by omega) hk]
  by_cases h176 : k<176
  · rw [if_pos h176, show (k-112)/32=1 by omega, show (k-112)%32=k-144 by omega]; rfl
  by_cases h304 : k<304
  · rw [if_neg h176, dif_pos h304, show (k-112)/32=2+(k-176)/32 by omega, show (k-112)%32=(k-176)%32 by omega]; rfl
  · rw [if_neg h176, dif_neg h304, dif_pos hk, show (k-112)/32=6+(k-304)/32 by omega,
      show (k-112)%32=(k-304)%32 by omega]; rfl

/-! ### List reading helpers -/

theorem take_get {L M : List Byte} {n : Nat} (h : L.take n=M) (j : Nat) (hj : j<n) : L[j]?.getD 0=M[j]?.getD 0 := by
  rw [← h, List.getElem?_take, if_pos hj]

theorem slice_get {L M : List Byte} {a n : Nat} (h : (L.drop a).take n=M) (j : Nat) (lo : a ≤ j) (hj : j<a+n) :
    L[j]?.getD 0=M[j-a]?.getD 0 := by
  rw [← h, List.getElem?_take, if_pos (by omega), List.getElem?_drop, show a+(j-a)=j by omega]

theorem le_get {n : Nat} (v : BitVec (8*n)) (i : Nat) (hi : i<n) : (leBytes v)[i]?.getD 0=v.extractLsb' (8*i) 8 := by
  simp [leBytes, hi]

theorem word_get (w : Word) (i : Nat) (hi : i<8) : (wordBytes w)[i]?.getD 0=w.extractLsb' (8*i) 8 :=
  le_get (n := 8) w i hi

theorem ext_idx {w : Nat} (v : BitVec w) (i j : Nat) (h : i=j) : v.extractLsb' i 8=v.extractLsb' j 8 := by rw [h]

theorem map_range_get (n : Nat) (g : Nat → Byte) (i : Nat) (hi : i<n) : ((List.range n).map g)[i]?.getD 0=g i := by
  simp [hi]

theorem map_range_getD (n : Nat) (g : Nat → Word) (i : Nat) (hi : i<n) : ((List.range n).map g).getD i 0=g i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem mate_eq (f : RecordFields) (x : Nat) (h : x<3) (m : Fin 3) (e : x=m.val) (i i' : Nat) (ei : i=i') :
    (f.mate ⟨x,h⟩).extractLsb' i 8=(f.mate m).extractLsb' i' 8 := by
  subst ei; congr

theorem bandA_eq (f : RecordFields) (x : Nat) (h : x<4) (m : Fin 4) (e : x=m.val) (i i' : Nat) (ei : i=i') :
    (f.bandA ⟨x,h⟩).extractLsb' i 8=(f.bandA m).extractLsb' i' 8 := by
  subst ei; congr

theorem bandB_eq (f : RecordFields) (x : Nat) (h : x<8) (m : Fin 8) (e : x=m.val) (i i' : Nat) (ei : i=i') :
    (f.bandB ⟨x,h⟩).extractLsb' i 8=(f.bandB m).extractLsb' i' 8 := by
  subst ei; congr

/-! ### The tail dwords -/

theorem tailA_field (src : Nat → Byte) (f : RecordFields) (agree : ∀ k<560, src k=fieldByte f k) (a : Nat)
    (a4 : a<4) : tailA src a=(f.bandA ⟨a, a4⟩).extractLsb' 192 64 := by
  unfold tailA
  apply dword_slice
  intro i hi
  rw [agree _ (by omega)]
  unfold fieldByte
  rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
  exact bandA_eq f _ _ _ (by simp; omega) _ _ (by omega)

theorem tailB_field (src : Nat → Byte) (f : RecordFields) (agree : ∀ k<560, src k=fieldByte f k) (b : Nat)
    (b8 : b<8) : tailB src b=(f.bandB ⟨b, b8⟩).extractLsb' 192 64 := by
  unfold tailB
  apply dword_slice
  intro i hi
  rw [agree _ (by omega)]
  unfold fieldByte
  rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega),
    dif_pos (by omega)]
  exact bandB_eq f _ _ _ (by simp; omega) _ _ (by omega)

theorem band_a_tails (src : Nat → Byte) (f : RecordFields) (agree : ∀ k<560, src k=fieldByte f k)
    (clean : ∀ a : Fin 4, (f.bandA a).extractLsb' 240 16=0) :
    bandATails src=[bandATailWord f 0, bandATailWord f 1, bandATailWord f 2] := by
  have t (a : Nat) (a4 : a<4) : tailA src a=((f.bandA ⟨a, a4⟩).extractLsb' 192 48).zeroExtend 64 := by
    rw [tailA_field src f agree a a4, CommitGolfCandidate.Layout2.tail48_eq_word64 _ (clean ⟨a, a4⟩)]
  unfold bandATails
  rw [t 0 (by decide), t 1 (by decide), t 2 (by decide), t 3 (by decide)]
  rfl

theorem tails_field (block : Nat → RecordFields) (p : Nat) (src : Nat → Byte)
    (agree : ∀ k<560, src k=fieldByte (block p) k) (clean : ∀ b : Fin 8, ((block p).bandB b).extractLsb' 238 18=0) :
    ∀ b<8, tailB src b=bandBTailWord46 block (8*p+b) := by
  intro b hb
  rw [tailB_field src (block p) agree b hb, ← CommitGolfCandidate.Layout2.tail46_eq_word64 _ (clean ⟨b, hb⟩)]
  have hf : (⟨(8*p+b)%8, Nat.mod_lt _ (by decide)⟩ : Fin 8)=⟨b, hb⟩ := Fin.ext (by show (8*p+b)%8=b; omega)
  unfold bandBTailWord46
  rw [show (8*p+b)/8=p by omega, hf]

/-! ### The fixed 488 bytes of a phase -/

theorem fixed_byte (p : Nat) (src : Nat → Byte) (c : Word) (f : RecordFields)
    (agree : ∀ k<560, src k=fieldByte f k) (cleanA : ∀ a : Fin 4, (f.bandA a).extractLsb' 240 16=0)
    (b : Nat) (hb : b<488) :
    writerByte p src c b=(newPhaseFixedBytes f)[b]?.getD 0 := by
  by_cases r1 : b<176
  · rw [writer_copy p src c b r1, agree b (by omega)]
    unfold fieldByte
    by_cases a0 : b<16
    · rw [if_pos a0, take_get (newPhaseFixedBytes_salt f) b a0, le_get _ _ a0]
    rw [if_neg a0]
    by_cases a1 : b<112
    · rw [dif_pos a1]
      by_cases m0 : b<48
      · rw [slice_get (newPhaseFixedBytes_mate0 f) b (by omega) (by omega), le_get _ _ (by omega)]
        exact mate_eq f _ _ 0 (by simp; omega) _ _ (by omega)
      by_cases m1 : b<80
      · rw [slice_get (newPhaseFixedBytes_mate1 f) b (by omega) (by omega), le_get _ _ (by omega)]
        exact mate_eq f _ _ 1 (by simp; omega) _ _ (by omega)
      · rw [slice_get (newPhaseFixedBytes_mate2 f) b (by omega) (by omega), le_get _ _ (by omega)]
        exact mate_eq f _ _ 2 (by simp; omega) _ _ (by omega)
    rw [dif_neg a1]
    by_cases a2 : b<144
    · rw [if_pos a2, slice_get (newPhaseFixedBytes_sib0 f) b (by omega) (by omega), le_get _ _ (by omega)]
    · rw [if_neg a2, if_pos r1, slice_get (newPhaseFixedBytes_sib1 f) b (by omega) (by omega),
        le_get _ _ (by omega)]
  by_cases r2 : b<272
  · rw [writer_bandA p src c b (by omega) r2, agree _ (by omega)]
    unfold fieldByte
    rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
    rcases (show (b-176)/24=0 ∨ (b-176)/24=1 ∨ (b-176)/24=2 ∨ (b-176)/24=3 by omega) with e|e|e|e
    · rw [slice_get (newPhaseFixedBytes_bandA0 f) b (by omega) (by omega), le_get _ _ (by omega),
        ext_ext _ _ _ _ _ (by omega)]
      exact bandA_eq f _ _ 0 (by simp; omega) _ _ (by omega)
    · rw [slice_get (newPhaseFixedBytes_bandA1 f) b (by omega) (by omega), le_get _ _ (by omega),
        ext_ext _ _ _ _ _ (by omega)]
      exact bandA_eq f _ _ 1 (by simp; omega) _ _ (by omega)
    · rw [slice_get (newPhaseFixedBytes_bandA2 f) b (by omega) (by omega), le_get _ _ (by omega),
        ext_ext _ _ _ _ _ (by omega)]
      exact bandA_eq f _ _ 2 (by simp; omega) _ _ (by omega)
    · rw [slice_get (newPhaseFixedBytes_bandA3 f) b (by omega) (by omega), le_get _ _ (by omega),
        ext_ext _ _ _ _ _ (by omega)]
      exact bandA_eq f _ _ 3 (by simp; omega) _ _ (by omega)
  by_cases r3 : b<296
  · rw [writer_tails p src c b (by omega) r3, band_a_tails src f agree cleanA]
    rcases (show (b-272)/8=0 ∨ (b-272)/8=1 ∨ (b-272)/8=2 by omega) with e|e|e
    · rw [e, slice_get (newPhaseFixedBytes_bandATail0 f) b (by omega) (by omega), word_get _ _ (by omega)]
      exact ext_idx _ _ _ (by omega)
    · rw [e, slice_get (newPhaseFixedBytes_bandATail1 f) b (by omega) (by omega), word_get _ _ (by omega)]
      exact ext_idx _ _ _ (by omega)
    · rw [e, slice_get (newPhaseFixedBytes_bandATail2 f) b (by omega) (by omega), word_get _ _ (by omega)]
      exact ext_idx _ _ _ (by omega)
  · rw [writer_bandB p src c b (by omega) hb, agree _ (by omega)]
    unfold fieldByte
    rw [if_neg (by omega), dif_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega),
      dif_pos (by omega)]
    have j8 : (b-296)/24<8 := by omega
    rw [slice_get (newPhaseFixedBytes_bandB_body f ⟨(b-296)/24, j8⟩) b (by simp; omega) (by simp; omega),
      le_get _ _ (by simp; omega), ext_ext _ _ _ _ _ (by simp; omega)]
    exact bandB_eq f _ _ _ (by simp; omega) _ _ (by simp; omega)

/-! ### The band-B stream of a phase -/

private theorem stream_tails (p : Nat) (src : Nat → Byte) (c : Word) :
    streamRun p src c=[tailB src 0, tailB src 1, tailB src 2, tailB src 3, tailB src 4, tailB src 5, tailB src 6,
      tailB src 7].foldl streamStep (c, carryIn p, []) := rfl

private theorem or_zero (w : Word) : 0 ||| (w <<< 0)=w := by simp

set_option maxHeartbeats 4000000 in
/-- The stream of phase `p`: its emitted dwords are the block's stream dwords `phaseStreamStart p ..`, and the
physical carry it leaves is `streamCarry` (phases 0..2). -/
theorem stream_phase (p : Nat) (hp : p<4) (block : Nat → RecordFields) (src : Nat → Byte) (c : Word)
    (tails : ∀ b<8, tailB src b=bandBTailWord46 block (8*p+b))
    (carry : p ≠ 0 → c=streamCarry block (8*p)) :
    (streamRun p src c).2.2=(List.range (phaseStreamCount p)).map (fun d => bandBStreamDword block (phaseStreamStart p+d)) ∧
      (p<3 → (streamRun p src c).1=streamCarry block (8*(p+1))) := by
  rw [stream_tails, tails 0 (by omega), tails 1 (by omega), tails 2 (by omega), tails 3 (by omega), tails 4 (by omega),
    tails 5 (by omega), tails 6 (by omega), tails 7 (by omega)]
  interval_cases p
  · have g1 := streamCarry_step_gt block 1 (by decide)
    have g2 := streamCarry_step_gt block 2 (by decide)
    have l3 := streamCarry_step_lt block 3 (by decide)
    have g4 := streamCarry_step_gt block 4 (by decide)
    have g5 := streamCarry_step_gt block 5 (by decide)
    have g6 := streamCarry_step_gt block 6 (by decide)
    have l7 := streamCarry_step_lt block 7 (by decide)
    simp only [Nat.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd] at g1 g2 l3 g4 g5 g6 l7
    simp (config := {decide := true}) only [List.foldl_cons, List.foldl_nil, streamStep, carryIn, Nat.reduceMul,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, List.nil_append, List.cons_append]
    rw [streamCarry_one, g1.1, g1.2, g2.1, g2.2, l3, g4.1, g4.2, g5.1, g5.2, g6.1, g6.2, l7]
    refine ⟨rfl, ?_⟩
    first | trivial | rfl | (intro _; rfl)
  · have c8 := carry (by decide)
    have g8 := streamCarry_step_gt block 8 (by decide)
    have g9 := streamCarry_step_gt block 9 (by decide)
    have l10 := streamCarry_step_lt block 10 (by decide)
    have g11 := streamCarry_step_gt block 11 (by decide)
    have g12 := streamCarry_step_gt block 12 (by decide)
    have g13 := streamCarry_step_gt block 13 (by decide)
    have l14 := streamCarry_step_lt block 14 (by decide)
    have g15 := streamCarry_step_gt block 15 (by decide)
    simp only [Nat.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd] at c8 g8 g9 l10 g11 g12 g13 l14 g15
    simp (config := {decide := true}) only [List.foldl_cons, List.foldl_nil, streamStep, carryIn, Nat.reduceMul,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, List.nil_append, List.cons_append]
    rw [c8, g8.1, g8.2, g9.1, g9.2, l10, g11.1, g11.2, g12.1, g12.2, g13.1, g13.2, l14, g15.1, g15.2]
    refine ⟨rfl, ?_⟩
    first | trivial | rfl | (intro _; rfl)
  · have c16 := carry (by decide)
    have g16 := streamCarry_step_gt block 16 (by decide)
    have l17 := streamCarry_step_lt block 17 (by decide)
    have g18 := streamCarry_step_gt block 18 (by decide)
    have g19 := streamCarry_step_gt block 19 (by decide)
    have g20 := streamCarry_step_gt block 20 (by decide)
    have l21 := streamCarry_step_lt block 21 (by decide)
    have g22 := streamCarry_step_gt block 22 (by decide)
    have g23 := streamCarry_step_gt block 23 (by decide)
    simp only [Nat.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd] at c16 g16 l17 g18 g19 g20 l21 g22 g23
    simp (config := {decide := true}) only [List.foldl_cons, List.foldl_nil, streamStep, carryIn, Nat.reduceMul,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, List.nil_append, List.cons_append]
    rw [c16, g16.1, g16.2, l17, g18.1, g18.2, g19.1, g19.2, g20.1, g20.2, l21, g22.1, g22.2, g23.1, g23.2]
    refine ⟨rfl, ?_⟩
    first | trivial | rfl | (intro _; rfl)
  · have c24 := carry (by decide)
    have l24 := streamCarry_step_lt block 24 (by decide)
    have g25 := streamCarry_step_gt block 25 (by decide)
    have g26 := streamCarry_step_gt block 26 (by decide)
    have g27 := streamCarry_step_gt block 27 (by decide)
    have l28 := streamCarry_step_lt block 28 (by decide)
    have g29 := streamCarry_step_gt block 29 (by decide)
    have g30 := streamCarry_step_gt block 30 (by decide)
    have e31 := streamCarry_step_eq block 31 (by decide)
    simp only [Nat.reduceMul, Nat.reduceMod, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd] at c24 l24 g25 g26 g27 l28 g29 g30 e31
    simp (config := {decide := true}) only [List.foldl_cons, List.foldl_nil, streamStep, carryIn, Nat.reduceMul,
      Nat.reduceAdd, Nat.reduceSub, ite_true, ite_false, List.nil_append, List.cons_append]
    rw [c24, l24, g25.1, g25.2, g26.1, g26.2, g27.1, g27.2, l28, g29.1, g29.2, g30.1, g30.2, e31.1]
    refine ⟨rfl, ?_⟩
    first | trivial | (intro h; contradiction) | (intro h; exact absurd h (by decide)) | (intro h; omega)

/-! ### One record -/

theorem ext_getD {l1 l2 : List Byte} (hl : l1.length=l2.length) (h : ∀ i<l1.length, l1[i]?.getD 0=l2[i]?.getD 0) :
    l1=l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have e := h i h1
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at e
  simpa using e

/-- Record block and outgoing carry of phase `p` on clean fields. -/
theorem record_bridge (p : Nat) (hp : p<4) (block : Nat → RecordFields) (src : Nat → Byte) (c : Word)
    (agree : ∀ k<560, src k=fieldByte (block p) k)
    (cleanA : ∀ a : Fin 4, ((block p).bandA a).extractLsb' 240 16=0)
    (cleanB : ∀ b : Fin 8, ((block p).bandB b).extractLsb' 238 18=0)
    (carry : p ≠ 0 → c=streamCarry block (8*p)) :
    (List.range (stride p)).map (writerByte p src c)=newPhaseBytes p block ∧
      (p<3 → writerCarry p src c=streamCarry block (8*(p+1))) := by
  obtain ⟨hs, hc⟩ := stream_phase p hp block src c (tails_field block p src agree cleanB) carry
  refine ⟨?_, hc⟩
  have count : stride p=488+8*phaseStreamCount p := by
    unfold Layout2Phase.stride phaseStreamCount; split_ifs <;> omega
  apply ext_getD
  · rw [List.length_map, List.length_range, newPhaseBytes_length]; unfold Layout2Phase.stride; split_ifs <;> rfl
  · intro i hi
    rw [List.length_map, List.length_range] at hi
    rw [map_range_get _ _ _ hi]
    by_cases fixed : i<488
    · rw [fixed_byte p src c (block p) agree cleanA i fixed]
      unfold newPhaseBytes
      rw [List.getElem?_append_left (by rw [newPhaseFixedBytes_length]; exact fixed)]
    · have hd : (i-488)/8<phaseStreamCount p := by omega
      rw [writer_stream p src c i (by omega), hs, map_range_getD _ _ _ hd,
        slice_get (newPhaseBytes_stream_dword p block _ hd) i (by omega) (by omega), word_get _ _ (by omega)]
      exact ext_idx _ _ _ (by omega)

end TwoPermutationPrototype.GroupedOpening.Layout2
