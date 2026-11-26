import CommitGolfCandidate.ReconstructedHidingRetainedGame
import CommitGolfCandidate.ReconstructedHidingUpper
import CommitGolfCandidate.ReconstructedHidingUniform

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingReplay HidingTraffic TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
noncomputable local instance prefixSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by classical exact SampleableType.ofFintype _

def repliesByGroup : GenReplies ≃ (Group → Reply) where
  toFun y g := y (blockNumber g)
  invFun z j := z (groupIndex j)
  left_inv y := funext (fun j => congrArg y (blockNumber_index j))
  right_inv z := funext (fun g => congrArg z (index_blockNumber g))

noncomputable def prefixParts : (Key × GenReplies) ≃ ((Key × PrivateSalts) × (Slack × (Group → Residue))) :=
  (((Equiv.refl Key).prodCongr (repliesByGroup.trans tapeSplit)).trans (Equiv.prodAssoc _ _ _).symm)

theorem prefix_salts (v : Key × GenReplies) : (prefixParts v).1=(v.1,tapeFromReplies v.2) := rfl

attribute [local irreducible] tapeFromReplies prefixParts blockSplit publicBlocks keyHit tagHit

theorem prefix_row_input (x : Reply) :
    Pr{let p ← $ᵗ (Key × GenReplies)}[keyHit x p.1 ∨ tagHit id x (tapeFromReplies p.2)] ≤ 1/2^120 := by
  let hit := fun p : Key × PrivateSalts => keyHit x p.1 ∨ tagHit id x p.2
  have move := SampleableType.prEvent_uniformSample_equiv prefixParts (fun v => hit v.1)
  rw [SampleableType.prEvent_uniformSample_fst hit] at move
  have same : (fun v : Key × GenReplies => hit (prefixParts v).1) =
      fun v => keyHit x v.1 ∨ tagHit id x (tapeFromReplies v.2) := by funext v; rw [prefix_salts]
  rw [same] at move
  exact move.le.trans (uniform_bound_of (forward_guess_le (fun i : Position => i) Function.injective_id x))

theorem prefix_row_output (b : Reply) :
    Pr{let p ← $ᵗ (Key × GenReplies)}[∃ j, p.2 j=b] ≤ (groupCount:ENNReal)/2^1600 := by
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
  intro _
  have hit (j : Fin groupCount) : Pr{let y ← $ᵗ GenReplies}[y j=b] = 1/2^1600 := by
    have bound := uniform_coordinate_guess j b
    have card : Fintype.card Reply = 2^1600 := by rw [←FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
    rw [card,Nat.cast_pow,Nat.cast_ofNat,←one_div] at bound
    exact uniform_value_of bound
  have bound := prEvent_exists_le_card_mul ($ᵗ GenReplies) (fun (j : Fin groupCount) y => y j=b) (fun j => (hit j).le)
  simpa only [Fintype.card_fin,mul_one_div] using bound

def prefixMark (row : Row) (v : Key × GenReplies) : Prop :=
  (keyHit row.1 v.1 ∨ tagHit id row.1 (tapeFromReplies v.2)) ∨ (∃ j, v.2 j=row.2)

theorem prefix_row_payment (table : Cache) :
    Pr{let v ← $ᵗ (Key × GenReplies)}[∃ row ∈ table.entries, prefixMark row v] ≤
      table.entries.length * (1/2^120+(groupCount:ENNReal)/2^1600) := by
  apply prEvent_list_le
  intro row _
  exact (prEvent_or_le _ _ _).trans (add_le_add (prefix_row_input row.1) (prefix_row_output row.2))

theorem prefix_key_payment (addresses : List Reply) :
    Pr{let p ← $ᵗ (Key × GenReplies)}[∃ x ∈ addresses, keyHit x p.1] ≤ (addresses.length:ENNReal)/2^192 := by
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_snd
  intro _
  have one (x : Reply) : Pr{let k ← $ᵗ Key}[keyHit x k] ≤ 1/2^192 := by
    let address := fun i => x.extractLsb' (64*i) 64
    unfold keyHit
    change Pr{let k ← $ᵗ Key}[∃ (t : Fin 4096) (g : Fin 342), ∀ i < 25, inputWord t g k i = address i] ≤ _
    exact uniform_bound_of (key_address_hit address)
  exact (prEvent_list_le addresses ($ᵗ Key) (fun x k => keyHit x k) (1/2^192)
    (fun x _ => one x)).trans_eq (mul_one_div _ _)

theorem prefix_signature_payment (table : Cache) :
    Pr{let p ← $ᵗ (Key × GenReplies)}[∃ j : Fin groupCount, ∃ i : Fin table.entries.length,
      signature ((blockSplit (p.2 j)).1)=tailSignature (outputTail table.entries[i].2)] ≤
        (groupCount:ENNReal)*table.entries.length/2^360 := by
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
  intro _
  let tails (i : Fin table.entries.length) := outputTail table.entries[i].2
  let hit := fun ys : Parts => ∃ j i, signature (ys j)=tailSignature (tails i)
  have move := SampleableType.prEvent_uniformSample_equiv (tableSplit (n := groupCount) blockSplit) (fun v => hit v.1)
  rw [SampleableType.prEvent_uniformSample_fst hit] at move
  have bound := tail_overlap_bound (G := Fin groupCount) tails
  rw [Fintype.card_fin,Fintype.card_fin] at bound
  have ret : (fun y : GenReplies => hit ((tableSplit blockSplit y).1)) =
      (fun y => ∃ j : Fin groupCount, ∃ i : Fin table.entries.length, signature ((blockSplit (y j)).1)=tailSignature (tails i)) := by
    unfold tableSplit hit publicBlocks
    rfl
  rw [ret] at move
  exact move.le.trans (uniform_bound_of bound)

theorem prefix_duplicate_payment :
    (Pr{let z ← $ᵗ (Key × GenReplies)}[¬Function.Injective (publicBlocks blockSplit z.2)]).toReal ≤
      (groupCount:ℝ)*groupCount/2^1440 := by
  let test := fun y : GenReplies => ¬Function.Injective (publicBlocks blockSplit y)
  have swap := SampleableType.prEvent_uniformSample_equiv (Equiv.prodComm Key GenReplies) (fun p => test p.1)
  rw [SampleableType.prEvent_uniformSample_fst test] at swap
  change (Pr{let z ← $ᵗ (Key × GenReplies)}[test z.2]).toReal ≤ _
  rw [show Pr{let z ← $ᵗ (Key × GenReplies)}[test z.2] = Pr{let y ← $ᵗ GenReplies}[test y] from swap]
  unfold test
  let bad := fun d : Parts => ¬Function.Injective d
  have move := SampleableType.prEvent_uniformSample_equiv (tableSplit (n := groupCount) blockSplit) (fun v => bad v.1)
  rw [SampleableType.prEvent_uniformSample_fst bad] at move
  rw [show (Pr{let v ← $ᵗ GenReplies}[¬Function.Injective (publicBlocks blockSplit v)]) =
      Pr{let d ← $ᵗ Parts}[bad d] from move,uniform_ind]
  have size : Fintype.card SaltBlock = 2^1440 := by
    change Fintype.card (Fin 12 → BitVec 120) = _
    rw [Fintype.card_fun,←FinEnum.card_eq_fintypeCard (α := BitVec 120),FinEnum.card_bitVec,Fintype.card_fin]
    norm_num
  have bound := duplicate_parts_bound (n := groupCount) (D := SaltBlock)
  rw [size,Nat.cast_pow,Nat.cast_ofNat] at bound
  exact bound

end CommitGolfCandidate.Reconstruction.HidingTape
