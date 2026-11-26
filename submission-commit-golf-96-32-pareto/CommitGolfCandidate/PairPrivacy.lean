import CommitGolfCandidate.PairPayload
import CommitGolfCandidate.PairStatic
import CommitGolfCandidate.HidingSecurity

namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 500000
attribute [local irreducible] readBuffer Nat.iterate overrideSlot openingResult CommitGolfCandidate.openingResult
private abbrev oldSub := CommitGolfCandidate.submission
private abbrev tdOf (s : MachineState) := readBuffer s oldSub.layout.trapdoor oldSub.sizes.trapdoor
private def oldProof (s : MachineState) (ps : Positions) :=
  oldSub.readProof (CommitGolfCandidate.openingResult (tdOf s) ps)
private def newProof (s : MachineState) (ps : Positions) :=
  submission.readProof (openingResult (tdOf s) ps)
private abbrev atByte (s : MachineState) (a : Nat) := s.getByte (BitVec.ofNat 64 (10871640096+a))

private theorem oldByte (s : MachineState) (ps : Positions) (hb : ps.card = BATCH) (j : Nat) (hj : j < 75776) :
    (oldProof s ps)[j]?.getD 0 = atByte (CommitGolfCandidate.openingResult (tdOf s) ps).state j := by
  unfold oldProof Submission.readProof
  simp only [CommitGolfCandidate.opening_result_succeeded,if_true,CommitGolfCandidate.opening_result_length,
    openingProofBytes,hb,if_pos]
  rw [List.getElem?_eq_getElem (by simpa using hj)]
  simp [atByte]
  rfl

private theorem offsetByte (s : MachineState) (pos lane : Nat) (h : lane < 32) :
    atByte s (pos+lane) = (readBuffer s (10871640096+pos) 32).extractLsb' (8*lane) 8 := by
  rw [read_buffer_byte _ _ _ _ h]; simp [atByte,Nat.add_assoc]

private theorem saltByte (s : MachineState) (pos lane : Nat) (h : lane < 16) :
    atByte s (pos+lane) = (readBuffer s (10871640096+pos) 16).extractLsb' (8*lane) 8 := by
  rw [read_buffer_byte _ _ _ _ h]; simp [atByte,Nat.add_assoc]

private theorem overrideCongr {α : Type} (bucket : Nat → Nat) (p n : Nat) {a b : Nat → α}
    (same : ∀ k < n, a k = b k) (fallback : α) :
    overrideSlot bucket a p n fallback = overrideSlot bucket b p n fallback := by
  induction n generalizing fallback with
  | zero => simp [overrideSlot]
  | succ n ih =>
    simp only [overrideSlot,same n (Nat.lt_succ_self _)]
    exact ih (fun k hk => same k (by omega)) _

private theorem slotByte (s : MachineState) (ps : Positions) (hb : ps.card=BATCH)
    (p lane : Nat) (hp : p<128) (h : lane<32) :
    atByte (openingResult (tdOf s) ps).state (67584+32*p+lane) =
      (oldProof s ps)[slotOffset ps p + lane]?.getD 0 := by
  rw [offsetByte _ _ _ h]
  rw [show 10871640096+(67584+32*p) = outBase+32*p by dsimp [outBase]; omega]
  erw [batchSlot s ps hb p hp]
  let byte := fun (d : Digest) => d.extractLsb' (8*lane) 8
  let lookup := fun j => (oldProof s ps)[j+lane]?.getD 0
  change byte (overrideSlot _ _ _ _ _) = lookup (overrideSlot _ _ _ _ _)
  rw [map_overrideSlot byte, map_overrideSlot lookup]
  have base := CommitGolfCandidate.opening_output_records_cap s ps hb
  have cap : lookup (71680+32*p) = byte (readBuffer s (4294971424+heapOffset (128+p)) 32) := by
    unfold lookup; rw [oldByte s ps hb _ (by omega), offsetByte _ _ _ h]
    rw [show 10871640096+(71680+32*p) = oldSub.layout.proof+71680+32*p by
      change _ = 10871640096+71680+32*p; omega]
    rw [base.2 p hp]
  rw [cap]
  apply overrideCongr
  intro k hk
  have hk128 : k < 128 := hk
  unfold lookup
  rw [oldByte s ps hb _ (by omega),offsetByte _ _ _ h]
  have eqn : 10871640096 + (560*k+528) = oldSub.layout.proof+560*k+16+32*16 := by
    change 10871640096 + (560*k+528) = 10871640096+560*k+16+32*16; omega
  rw [eqn,(base.1 k hk).2 16 (by decide)]
  unfold childAddress
  rw [show (LENGTH+openingIndex ps k)/2^16 = 256 + openingIndex ps k / 65536 by
    change (16777216+openingIndex ps k)/65536 = _; omega]

private theorem recordByte (s : MachineState) (ps : Positions) (hb : ps.card=BATCH) (j : Nat) (hj : j<67584) :
    atByte (openingResult (tdOf s) ps).state j =
      (oldProof s ps)[(j/528)*560 + j%528]?.getD 0 := by
  let k := j/528
  let off := j%528
  have hk : k<128 := by dsimp [k]; omega
  have lim : off<528 := Nat.mod_lt _ (by decide)
  have pos : j=528*k+off := by dsimp [k,off];omega
  have ob := (CommitGolfCandidate.opening_output_records_cap s ps hb).1 k hk
  have nb := batchRecords s ps hb k hk
  have oldPos : j/528*560+j%528=560*k+off := by dsimp [k,off];omega
  rw [oldPos,oldByte s ps hb _ (by omega)]
  change atByte _ j=atByte _ (560*k+off)
  rw [pos]
  by_cases salt : off<16
  · rw [saltByte _ _ _ salt,saltByte _ _ _ salt]
    exact congrArg (fun d : Salt=>d.extractLsb' (8*off) 8) (nb.1.trans ob.1.symm)
  · let part:=(off-16)/32
    let lane:=(off-16)%32
    have bound : part<16 := by dsimp [part];omega
    have hl : lane<32 := Nat.mod_lt _ (by decide)
    have offEq : off=16+32*part+lane := by dsimp [part,lane];omega
    rw [show 528*k+off=(528*k+16+32*part)+lane by omega,
        show 560*k+off=(560*k+16+32*part)+lane by omega,offsetByte _ _ _ hl,offsetByte _ _ _ hl]
    have ne : 10871640096+(528*k+16+32*part)=10871640096+528*k+16+32*part := by omega
    have oe : 10871640096+(560*k+16+32*part)=oldSub.layout.proof+560*k+16+32*part := by
      change _=10871640096+560*k+16+32*part;omega
    rw [ne,oe]
    exact congrArg (fun d : Digest=>d.extractLsb' (8*lane) 8) ((nb.2 part bound).trans (ob.2 part (by omega)).symm)

private theorem normalOutput (td : BitVec (8*submission.sizes.trapdoor)) (ps : Positions)
    (normal : ps.card ≠ BATCH) : openingResult td ps = CommitGolfCandidate.openingResult td ps := by
  have n : (openingInitializedState (submission.initialState .opening (td,ps))).getReg .x27 ≠ 128 := by
    rw [(opening_setup_registers _).2.2.2.1]
    intro eqn
    have h := congrArg BitVec.toNat eqn
    have b : ps.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ ps
    have small : ps.card < 2^64 := by change ps.card ≤ 16777216 at b; omega
    change (BitVec.ofNat 64 ps.card).toNat = (128#64).toNat at h
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at h
    exact normal (h.trans (by decide))
  unfold openingResult CommitGolfCandidate.openingResult openingFinalState CommitGolfCandidate.openingFinalState
  unfold openingCycles CommitGolfCandidate.openingCycles
  simp only [if_neg normal]
  change _ = _
  have stateEq : submission.initialState .opening (td,ps) = oldSub.initialState .opening (td,ps) := rfl
  have depthEq (x : MachineState) (v : x.getReg .x27 ≠ 128) :
      pair_openingDepthState x = openingDepthState x := by
    unfold pair_openingDepthState openingDepthState
    rw [if_neg v,if_neg v]
  rw [depthEq _ n, stateEq]

theorem honestConversion (s : MachineState) (ps : Positions) : newProof s ps = convert ps (oldProof s ps) := by
  by_cases hb : ps.card=BATCH
  · have len : (newProof s ps).length = 71680 := by
      exact (opening_proof_length (tdOf s) ps).trans (by simp [proofBytes,hb])
    apply List.ext_getElem
    · rw [len,convert_batch_length hb]
    · intro j hj hj'
      have inside : j<71680 := len ▸ hj
      have left : (newProof s ps)[j] = atByte (openingResult (tdOf s) ps).state j := by
        simp only [newProof,Submission.readProof,opening_result_succeeded (tdOf s) ps,if_true,List.getElem_map,List.getElem_range]
        rfl
      rw [left]
      simp only [convert,hb,↓reduceIte,List.getElem_map,List.getElem_range,oldOffset]
      split
      next lo => exact recordByte s ps hb j lo
      next hi =>
        let p := (j-67584)/32
        have e := slotByte s ps hb p (j%32) (by dsimp [p]; omega) (by omega)
        rw [show 67584+32*p+j%32 = j by dsimp [p]; omega] at e
        exact e
  · rw [convert_normal hb,newProof,normalOutput (tdOf s) ps hb]; rfl

private theorem experiments (aState out : Type) (k : Nat) (a : Hiding.HidingAdversary aState out k) (b : Bool) :
    Hiding.hidingExperiment submission.scheme a b =
      Hiding.hidingExperiment (convertedScheme oldSub.scheme) a b := by
  unfold Hiding.hidingExperiment
  apply bind_congr; intro c
  change (oldSub.scheme.commit _ >>= _) = (oldSub.scheme.commit _ >>= _)
  apply bind_congr_of_forall_mem_support
  rintro ⟨root,td⟩ reached
  change _ ∈ support (oldSub.readCommit <$> oldSub.run .commit _) at reached
  rw [support_map] at reached
  obtain ⟨result,_,he⟩ := reached
  have ht : td = tdOf result.state := (congrArg Prod.snd he).symm
  subst td
  change (submission.scheme.opening (tdOf result.state) c.positions >>= _) = _
  erw [opening_scheme_execution (tdOf result.state) c.positions]
  change _ = ((convert c.positions <$> oldSub.scheme.opening _ _) >>= _)
  erw [CommitGolfCandidate.opening_scheme_execution (tdOf result.state) c.positions]
  simp only [map_pure,pure_bind]
  rw [show submission.readProof (openingResult (tdOf result.state) c.positions) = _ from
    honestConversion result.state c.positions]
  rfl

theorem pair_hiding : submission.scheme.Hiding HIDING_ERROR := by
  have converted := hiding_of_conversion oldSub.scheme CommitGolfCandidate.submission_hiding
  refine ⟨converted.1, ?_⟩
  intro k t hk st out a bounded
  rw [experiments st out k a false, experiments st out k a true]
  exact converted.2 k t hk st out a bounded

end CommitGolfCandidate.PairCap
