import CommitGolfCandidate.Layout2Fields

/-! Layout 2 opener, part 2 (whole record area): the physical carry chain is the block's `streamCarry`, Neon's
layout record by record, `l2Proof = newProofBytes` on clean records, and the conversion of today's proof. -/
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

/-! ### The whole record area -/

/-- Records `4q .. 4q+3` of `recs`. -/
def blk (recs : Nat → RecordFields) (q : Nat) : Nat → RecordFields := fun i => recs (4*q+i)

/-- Clean digests of the opened records: band A bits `240..255`, band B bits `238..255`. -/
structure CleanRecords (s : Submission) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions) : Prop where
  bandA : ∀ j<positions.card, ∀ a : Fin 4, ((trapdoorRecordFields (s:=s) t positions j).bandA a).extractLsb' 240 16=0
  bandB : ∀ j<positions.card, ∀ b : Fin 8, ((trapdoorRecordFields (s:=s) t positions j).bandB b).extractLsb' 238 18=0

theorem blk_at (recs : Nat → RecordFields) (j : Nat) : blk recs (j/4) (j%4)=recs j := by
  unfold blk; rw [Nat.div_add_mod]

/-- The physical carry entering record `j` is the block's `streamCarry`. -/
theorem carry_chain (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (clean : CleanRecords s t positions) :
    ∀ j, j ≤ positions.card → j%4 ≠ 0 →
      carryAt (s.initialState .opening (t, positions)) positions j=
        streamCarry (blk (trapdoorRecordFields (s:=s) t positions) (j/4)) (8*(j%4)) := by
  intro j
  induction j with
  | zero => intro _ h; exact absurd rfl h
  | succ j ih =>
    intro hj nz
    have p3 : j%4<3 := by omega
    have q : (j+1)/4=j/4 := by omega
    have m : (j+1)%4=j%4+1 := by omega
    have agree : ∀ k<560, srcAt (s.initialState .opening (t, positions)) positions j k=
        fieldByte (blk (trapdoorRecordFields (s:=s) t positions) (j/4) (j%4)) k := by
      intro k hk; rw [blk_at]; exact src_field s layout t positions j (by omega) k hk
    have br := record_bridge (j%4) (by omega) (blk (trapdoorRecordFields (s:=s) t positions) (j/4)) _
      (carryAt (s.initialState .opening (t, positions)) positions j)
      agree (by rw [blk_at]; exact clean.bandA j (by omega)) (by rw [blk_at]; exact clean.bandB j (by omega))
      (fun h => ih (by omega) h)
    show writerCarry (j%4) _ _=_
    rw [br.2 p3, q, m]

/-- Neon's proof layout record by record. -/
theorem new_proof_split (k : Nat) (recs : Nat → RecordFields) (cap : Proof) :
    newProofBytes k recs cap=(List.range k).flatMap (fun j => newPhaseBytes (j%4) (blk recs (j/4))) ++
      newPartialFlush (k%4) (blk recs (k/4)) ++ cap := by
  have four (q : Nat) (r : Nat) (hr : r ≤ 4) :
      ((List.range r).map (4*q+·)).flatMap (fun j => newPhaseBytes (j%4) (blk recs (j/4)))=
        (List.range r).flatMap (fun p => newPhaseBytes p (fun i => recs (4*q+i))) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro p hp
    have := List.mem_range.mp hp
    rw [show (4*q+p)%4=p by omega, show (4*q+p)/4=q by omega]
    rfl
  have flush4 (b : Nat → RecordFields) : newPartialFlush 4 b=[] := by
    unfold newPartialFlush; simp
  have whole : ∀ q, (List.range (4*q)).flatMap (fun j => newPhaseBytes (j%4) (blk recs (j/4)))=
      (List.range q).flatMap (fun g => newBlockBytes 4 (fun p => recs (4*g+p))) := by
    intro q
    induction q with
    | zero => simp only [Nat.mul_zero, List.range_zero, List.flatMap_nil]
    | succ q ih =>
      rw [show 4*(q+1)=4*q+4 by omega, List.range_add, List.flatMap_append, ih, four q 4 (by omega),
        show List.range (q+1)=List.range q ++ [q] from List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton, newBlockBytes, flush4, List.append_nil]
  have tail : (List.range (k%4)).flatMap (fun p => newPhaseBytes p (fun i => recs (4*(k/4)+i))) ++
      (newPartialFlush (k%4) (blk recs (k/4)) ++ cap)=
      (if k%4=0 then [] else newBlockBytes (k%4) (fun p => recs (4*(k/4)+p))) ++ cap := by
    by_cases z : k%4=0
    · rw [if_pos z, z]; unfold newPartialFlush; simp
    · rw [if_neg z, newBlockBytes, List.append_assoc]; rfl
  unfold newProofBytes
  rw [show (List.range k)=List.range (4*(k/4)+k%4) by rw [Nat.div_add_mod], List.range_add, List.flatMap_append,
    whole, four (k/4) (k%4) (by omega)]
  simp only [List.append_assoc, tail]

/-- On clean records, the Layout 2 record area and flush are Neon's `newProofBytes`. -/
theorem l2_proof_new (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (clean : CleanRecords s t positions) (cap : Proof) :
    l2Proof (s.initialState .opening (t, positions)) positions cap=
      newProofBytes positions.card (trapdoorRecordFields (s:=s) t positions) cap := by
  rw [new_proof_split]
  unfold l2Proof
  have h1 : (List.range positions.card).flatMap (physRecord (s.initialState .opening (t, positions)) positions)=
      (List.range positions.card).flatMap
        (fun j => newPhaseBytes (j%4) (blk (trapdoorRecordFields (s:=s) t positions) (j/4))) := by
    apply List.flatMap_congr
    intro j hj
    have hj' := List.mem_range.mp hj
    have agree : ∀ k<560, srcAt (s.initialState .opening (t, positions)) positions j k=
        fieldByte (blk (trapdoorRecordFields (s:=s) t positions) (j/4) (j%4)) k := by
      intro k hk; rw [blk_at]; exact src_field s layout t positions j hj' k hk
    exact (record_bridge (j%4) (by omega) (blk (trapdoorRecordFields (s:=s) t positions) (j/4)) _
      (carryAt (s.initialState .opening (t, positions)) positions j) agree
      (by rw [blk_at]; exact clean.bandA j hj') (by rw [blk_at]; exact clean.bandB j hj')
      (fun h => carry_chain s layout t positions clean j (by omega) h)).1
  have h2 : physFlush (s.initialState .opening (t, positions)) positions=
      newPartialFlush (positions.card%4) (blk (trapdoorRecordFields (s:=s) t positions) (positions.card/4)) := by
    unfold physFlush
    have cut (n : Nat) (w : Word) (hn : n ≤ 8) :
        (List.range n).map (fun b => w.extractLsb' (8*b) 8)=(wordBytes w).take n := by
      apply ext_getD (by simp; omega)
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      rw [map_range_get _ _ _ hi, List.getElem?_take, if_pos hi, word_get _ _ (by omega)]
    have k4 := Nat.mod_lt positions.card (show 4>0 by decide)
    rcases (show positions.card%4=0 ∨ positions.card%4=1 ∨ positions.card%4=2 ∨ positions.card%4=3 by omega)
      with r|r|r|r
    · rw [show (positions.card+3)%4=3 by omega, r]
      unfold flushLen newPartialFlush
      simp
    · rw [show (positions.card+3)%4=0 by omega,
        carry_chain s layout t positions clean _ (Nat.le_refl _) (by omega), r]
      unfold flushLen
      rw [if_pos rfl, cut 6 _ (by decide), ← streamCarry_flush_r1]
    · rw [show (positions.card+3)%4=1 by omega,
        carry_chain s layout t positions clean _ (Nat.le_refl _) (by omega), r]
      unfold flushLen
      rw [if_neg (by decide), if_pos rfl, cut 4 _ (by decide), ← streamCarry_flush_r2]
    · rw [show (positions.card+3)%4=2 by omega,
        carry_chain s layout t positions clean _ (Nat.le_refl _) (by omega), r]
      unfold flushLen
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl, cut 2 _ (by decide), ← streamCarry_flush_r3]
  rw [h1, h2]

/-- On clean records the opener's proof is today's proof in Neon's V1 layout. -/
theorem l2_proof_convert (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (clean : CleanRecords s t positions) :
    l2ProofFromTrapdoor (s:=s) t positions=convert encTables positions.card (proofFromTrapdoor (s:=s) t positions) := by
  rw [CommitGolfCandidate.Layout2.convert_enc_proofFromTrapdoor (s:=s) t positions
    (fun i hi j => clean.bandB i hi ⟨j.val, by omega⟩)]
  exact l2_proof_new s layout t positions clean _

end TwoPermutationPrototype.GroupedOpening.Layout2
