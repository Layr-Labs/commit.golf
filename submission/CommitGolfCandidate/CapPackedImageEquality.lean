import CommitGolf.Artifact
import CommitGolfCandidate.Group341Encoding
import CommitGolfCandidate.CapExperimentalABI
import CommitGolfCandidate.NonceCompressedPrograms
/-! Checked indexed equality with the independently regenerated delivered artifact.
Periodic512-word facts and balanced joins avoid materializing the full code list. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
/-- A pure, indexed specification for one packed image subtree. -/
def PackedMatches {count : Nat} (packed : ArtifactEncoding.Packed count)
    (spec : Nat → BitVec 32) (offset : Nat) : Prop :=
  ∀ index : Fin count, packed.get 32 index=spec (offset+index.val)

theorem packed_matches_join {leftCount rightCount : Nat}
    (left : ArtifactEncoding.Packed leftCount) (right : ArtifactEncoding.Packed rightCount)
    (spec : Nat → BitVec 32) (offset : Nat)
    (hl : PackedMatches left spec offset)
    (hr : PackedMatches right spec (offset+leftCount)) :
    PackedMatches (.join left right) spec offset := by
  intro index
  by_cases inside : index.val<leftCount
  · rw [ArtifactEncoding.get_join_left 32 left right index inside]
    exact hl ⟨index.val,inside⟩
  · rw [ArtifactEncoding.get_join_right 32 left right index inside]
    calc
      _ = spec ((offset+leftCount)+(index.val-leftCount)) := hr ⟨index.val-leftCount,by omega⟩
      _ = spec (offset+index.val) := by congr 1;omega

theorem packed_periodic_phase1 (index : Fin 512) :
    Artifact.commitCode_0_1.get 32 index=group341BodyWord (1+index.val) := by
  fin_cases index <;> rfl

theorem packed_periodic_phase0 (index : Fin 512) :
    Artifact.commitCode_0_2.get 32 index=group341BodyWord index.val := by
  fin_cases index <;> rfl

theorem packed_periodic_phase2 (index : Fin 512) :
    Artifact.commitCode_0_3.get 32 index=group341BodyWord (2+index.val) := by
  fin_cases index <;> rfl

def longImageSpec (index : Nat) : BitVec 32 :=
  if index<166 then group341HeadWords.getD index 0
  else if index<251824 then group341BodyWord (index-166)
  else group341EndWords.getD (index-251824) 0

theorem packed_periodic_window (packed : ArtifactEncoding.Packed 512) (phase offset : Nat)
    (same : ∀ index : Fin 512, packed.get 32 index=group341BodyWord (phase+index.val))
    (above : 166≤offset) (below : offset+512≤251824)
    (aligned : (offset-166)%3=phase%3) : PackedMatches packed longImageSpec offset := by
  intro index
  rw [same]
  unfold longImageSpec
  rw [if_neg (by omega),if_pos (by omega)]
  have matching : (phase+index.val)%3=(offset+index.val-166)%3 := by omega
  unfold group341BodyWord
  rw [matching]

/-- A Boolean element-by-element comparison, evaluated once by the kernel. -/
def packedCheck {count : Nat} (packed : ArtifactEncoding.Packed count) (spec : Nat → BitVec 32)
    (offset : Nat) : Bool :=
  (List.finRange count).all fun index => packed.get 32 index == spec (offset + index.val)

theorem packed_check_matches {count : Nat} (packed : ArtifactEncoding.Packed count)
    (spec : Nat → BitVec 32) (offset : Nat) (ok : packedCheck packed spec offset = true) :
    PackedMatches packed spec offset := by
  intro index
  unfold packedCheck at ok
  rw [List.all_eq_true] at ok
  exact beq_iff_eq.mp (ok index (List.mem_finRange index))

/-- Chunks inside the appended code are compared as one list against a drop/take window. -/
theorem packed_end_matches {count : Nat} (packed : ArtifactEncoding.Packed count) (skip : Nat)
    (ok : (ArtifactEncoding.decode 32 packed == (group341EndWords.drop skip).take count) = true)
    (inside : skip + count ≤ group341EndWords.length) :
    PackedMatches packed longImageSpec (251824 + skip) := by
  intro index
  have same := beq_iff_eq.mp ok
  have lhs : packed.get 32 index = (ArtifactEncoding.decode 32 packed).getD index.val 0 :=
    (ArtifactEncoding.getD_decode 32 packed index.val index.isLt).symm
  rw [lhs, same]
  unfold longImageSpec
  rw [if_neg (by omega), if_neg (by omega), show 251824 + skip + index.val - 251824 = skip + index.val by omega]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]
  simp

theorem packed_0_0 : PackedMatches Artifact.commitCode_0_0 longImageSpec 0 := by
  exact packed_check_matches _ _ _ (by decide +kernel)

theorem packed_0_1 : PackedMatches Artifact.commitCode_0_1 longImageSpec 512 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_2 : PackedMatches Artifact.commitCode_0_2 longImageSpec 1024 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_3 : PackedMatches Artifact.commitCode_0_3 longImageSpec 1536 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_4 : PackedMatches Artifact.commitCode_0_4 longImageSpec 2048 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_5 : PackedMatches Artifact.commitCode_0_5 longImageSpec 2560 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_6 : PackedMatches Artifact.commitCode_0_6 longImageSpec 3072 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_7 : PackedMatches Artifact.commitCode_0_7 longImageSpec 3584 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_8 : PackedMatches Artifact.commitCode_0_8 longImageSpec 4096 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_9 : PackedMatches Artifact.commitCode_0_9 longImageSpec 4608 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_10 : PackedMatches Artifact.commitCode_0_10 longImageSpec 5120 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_11 : PackedMatches Artifact.commitCode_0_11 longImageSpec 5632 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_12 : PackedMatches Artifact.commitCode_0_12 longImageSpec 6144 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_13 : PackedMatches Artifact.commitCode_0_13 longImageSpec 6656 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_14 : PackedMatches Artifact.commitCode_0_14 longImageSpec 7168 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_15 : PackedMatches Artifact.commitCode_0_15 longImageSpec 7680 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_16 : PackedMatches Artifact.commitCode_0_16 longImageSpec 8192 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_17 : PackedMatches Artifact.commitCode_0_17 longImageSpec 8704 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_18 : PackedMatches Artifact.commitCode_0_18 longImageSpec 9216 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_19 : PackedMatches Artifact.commitCode_0_19 longImageSpec 9728 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_20 : PackedMatches Artifact.commitCode_0_20 longImageSpec 10240 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_21 : PackedMatches Artifact.commitCode_0_21 longImageSpec 10752 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_22 : PackedMatches Artifact.commitCode_0_22 longImageSpec 11264 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_23 : PackedMatches Artifact.commitCode_0_23 longImageSpec 11776 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_24 : PackedMatches Artifact.commitCode_0_24 longImageSpec 12288 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_25 : PackedMatches Artifact.commitCode_0_25 longImageSpec 12800 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_26 : PackedMatches Artifact.commitCode_0_26 longImageSpec 13312 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_27 : PackedMatches Artifact.commitCode_0_27 longImageSpec 13824 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_28 : PackedMatches Artifact.commitCode_0_28 longImageSpec 14336 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_29 : PackedMatches Artifact.commitCode_0_29 longImageSpec 14848 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_30 : PackedMatches Artifact.commitCode_0_30 longImageSpec 15360 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_31 : PackedMatches Artifact.commitCode_0_31 longImageSpec 15872 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_32 : PackedMatches Artifact.commitCode_0_32 longImageSpec 16384 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_33 : PackedMatches Artifact.commitCode_0_33 longImageSpec 16896 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_34 : PackedMatches Artifact.commitCode_0_34 longImageSpec 17408 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_35 : PackedMatches Artifact.commitCode_0_35 longImageSpec 17920 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_36 : PackedMatches Artifact.commitCode_0_36 longImageSpec 18432 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_37 : PackedMatches Artifact.commitCode_0_37 longImageSpec 18944 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_38 : PackedMatches Artifact.commitCode_0_38 longImageSpec 19456 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_39 : PackedMatches Artifact.commitCode_0_39 longImageSpec 19968 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_40 : PackedMatches Artifact.commitCode_0_40 longImageSpec 20480 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_41 : PackedMatches Artifact.commitCode_0_41 longImageSpec 20992 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_42 : PackedMatches Artifact.commitCode_0_42 longImageSpec 21504 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_43 : PackedMatches Artifact.commitCode_0_43 longImageSpec 22016 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_44 : PackedMatches Artifact.commitCode_0_44 longImageSpec 22528 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_45 : PackedMatches Artifact.commitCode_0_45 longImageSpec 23040 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_46 : PackedMatches Artifact.commitCode_0_46 longImageSpec 23552 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_47 : PackedMatches Artifact.commitCode_0_47 longImageSpec 24064 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_48 : PackedMatches Artifact.commitCode_0_48 longImageSpec 24576 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_49 : PackedMatches Artifact.commitCode_0_49 longImageSpec 25088 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_50 : PackedMatches Artifact.commitCode_0_50 longImageSpec 25600 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_51 : PackedMatches Artifact.commitCode_0_51 longImageSpec 26112 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_52 : PackedMatches Artifact.commitCode_0_52 longImageSpec 26624 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_53 : PackedMatches Artifact.commitCode_0_53 longImageSpec 27136 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_54 : PackedMatches Artifact.commitCode_0_54 longImageSpec 27648 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_55 : PackedMatches Artifact.commitCode_0_55 longImageSpec 28160 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_56 : PackedMatches Artifact.commitCode_0_56 longImageSpec 28672 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_57 : PackedMatches Artifact.commitCode_0_57 longImageSpec 29184 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_58 : PackedMatches Artifact.commitCode_0_58 longImageSpec 29696 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_59 : PackedMatches Artifact.commitCode_0_59 longImageSpec 30208 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_60 : PackedMatches Artifact.commitCode_0_60 longImageSpec 30720 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_61 : PackedMatches Artifact.commitCode_0_61 longImageSpec 31232 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_62 : PackedMatches Artifact.commitCode_0_62 longImageSpec 31744 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_63 : PackedMatches Artifact.commitCode_0_63 longImageSpec 32256 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_64 : PackedMatches Artifact.commitCode_0_64 longImageSpec 32768 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_65 : PackedMatches Artifact.commitCode_0_65 longImageSpec 33280 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_66 : PackedMatches Artifact.commitCode_0_66 longImageSpec 33792 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_67 : PackedMatches Artifact.commitCode_0_67 longImageSpec 34304 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_68 : PackedMatches Artifact.commitCode_0_68 longImageSpec 34816 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_69 : PackedMatches Artifact.commitCode_0_69 longImageSpec 35328 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_70 : PackedMatches Artifact.commitCode_0_70 longImageSpec 35840 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_71 : PackedMatches Artifact.commitCode_0_71 longImageSpec 36352 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_72 : PackedMatches Artifact.commitCode_0_72 longImageSpec 36864 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_73 : PackedMatches Artifact.commitCode_0_73 longImageSpec 37376 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_74 : PackedMatches Artifact.commitCode_0_74 longImageSpec 37888 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_75 : PackedMatches Artifact.commitCode_0_75 longImageSpec 38400 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_76 : PackedMatches Artifact.commitCode_0_76 longImageSpec 38912 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_77 : PackedMatches Artifact.commitCode_0_77 longImageSpec 39424 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_78 : PackedMatches Artifact.commitCode_0_78 longImageSpec 39936 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_79 : PackedMatches Artifact.commitCode_0_79 longImageSpec 40448 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_80 : PackedMatches Artifact.commitCode_0_80 longImageSpec 40960 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_81 : PackedMatches Artifact.commitCode_0_81 longImageSpec 41472 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_82 : PackedMatches Artifact.commitCode_0_82 longImageSpec 41984 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_83 : PackedMatches Artifact.commitCode_0_83 longImageSpec 42496 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_84 : PackedMatches Artifact.commitCode_0_84 longImageSpec 43008 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_85 : PackedMatches Artifact.commitCode_0_85 longImageSpec 43520 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_86 : PackedMatches Artifact.commitCode_0_86 longImageSpec 44032 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_87 : PackedMatches Artifact.commitCode_0_87 longImageSpec 44544 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_88 : PackedMatches Artifact.commitCode_0_88 longImageSpec 45056 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_89 : PackedMatches Artifact.commitCode_0_89 longImageSpec 45568 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_90 : PackedMatches Artifact.commitCode_0_90 longImageSpec 46080 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_91 : PackedMatches Artifact.commitCode_0_91 longImageSpec 46592 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_92 : PackedMatches Artifact.commitCode_0_92 longImageSpec 47104 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_93 : PackedMatches Artifact.commitCode_0_93 longImageSpec 47616 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_94 : PackedMatches Artifact.commitCode_0_94 longImageSpec 48128 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_95 : PackedMatches Artifact.commitCode_0_95 longImageSpec 48640 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_96 : PackedMatches Artifact.commitCode_0_96 longImageSpec 49152 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_97 : PackedMatches Artifact.commitCode_0_97 longImageSpec 49664 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_98 : PackedMatches Artifact.commitCode_0_98 longImageSpec 50176 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_99 : PackedMatches Artifact.commitCode_0_99 longImageSpec 50688 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_100 : PackedMatches Artifact.commitCode_0_100 longImageSpec 51200 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_101 : PackedMatches Artifact.commitCode_0_101 longImageSpec 51712 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_102 : PackedMatches Artifact.commitCode_0_102 longImageSpec 52224 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_103 : PackedMatches Artifact.commitCode_0_103 longImageSpec 52736 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_104 : PackedMatches Artifact.commitCode_0_104 longImageSpec 53248 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_105 : PackedMatches Artifact.commitCode_0_105 longImageSpec 53760 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_106 : PackedMatches Artifact.commitCode_0_106 longImageSpec 54272 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_107 : PackedMatches Artifact.commitCode_0_107 longImageSpec 54784 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_108 : PackedMatches Artifact.commitCode_0_108 longImageSpec 55296 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_109 : PackedMatches Artifact.commitCode_0_109 longImageSpec 55808 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_110 : PackedMatches Artifact.commitCode_0_110 longImageSpec 56320 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_111 : PackedMatches Artifact.commitCode_0_111 longImageSpec 56832 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_112 : PackedMatches Artifact.commitCode_0_112 longImageSpec 57344 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_113 : PackedMatches Artifact.commitCode_0_113 longImageSpec 57856 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_114 : PackedMatches Artifact.commitCode_0_114 longImageSpec 58368 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_115 : PackedMatches Artifact.commitCode_0_115 longImageSpec 58880 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_116 : PackedMatches Artifact.commitCode_0_116 longImageSpec 59392 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_117 : PackedMatches Artifact.commitCode_0_117 longImageSpec 59904 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_118 : PackedMatches Artifact.commitCode_0_118 longImageSpec 60416 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_119 : PackedMatches Artifact.commitCode_0_119 longImageSpec 60928 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_120 : PackedMatches Artifact.commitCode_0_120 longImageSpec 61440 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_121 : PackedMatches Artifact.commitCode_0_121 longImageSpec 61952 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_122 : PackedMatches Artifact.commitCode_0_122 longImageSpec 62464 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_123 : PackedMatches Artifact.commitCode_0_123 longImageSpec 62976 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_124 : PackedMatches Artifact.commitCode_0_124 longImageSpec 63488 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_125 : PackedMatches Artifact.commitCode_0_125 longImageSpec 64000 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_126 : PackedMatches Artifact.commitCode_0_126 longImageSpec 64512 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_127 : PackedMatches Artifact.commitCode_0_127 longImageSpec 65024 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_128 : PackedMatches Artifact.commitCode_0_128 longImageSpec 65536 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_129 : PackedMatches Artifact.commitCode_0_129 longImageSpec 66048 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_130 : PackedMatches Artifact.commitCode_0_130 longImageSpec 66560 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_131 : PackedMatches Artifact.commitCode_0_131 longImageSpec 67072 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_132 : PackedMatches Artifact.commitCode_0_132 longImageSpec 67584 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_133 : PackedMatches Artifact.commitCode_0_133 longImageSpec 68096 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_134 : PackedMatches Artifact.commitCode_0_134 longImageSpec 68608 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_135 : PackedMatches Artifact.commitCode_0_135 longImageSpec 69120 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_136 : PackedMatches Artifact.commitCode_0_136 longImageSpec 69632 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_137 : PackedMatches Artifact.commitCode_0_137 longImageSpec 70144 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_138 : PackedMatches Artifact.commitCode_0_138 longImageSpec 70656 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_139 : PackedMatches Artifact.commitCode_0_139 longImageSpec 71168 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_140 : PackedMatches Artifact.commitCode_0_140 longImageSpec 71680 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_141 : PackedMatches Artifact.commitCode_0_141 longImageSpec 72192 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_142 : PackedMatches Artifact.commitCode_0_142 longImageSpec 72704 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_143 : PackedMatches Artifact.commitCode_0_143 longImageSpec 73216 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_144 : PackedMatches Artifact.commitCode_0_144 longImageSpec 73728 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_145 : PackedMatches Artifact.commitCode_0_145 longImageSpec 74240 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_146 : PackedMatches Artifact.commitCode_0_146 longImageSpec 74752 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_147 : PackedMatches Artifact.commitCode_0_147 longImageSpec 75264 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_148 : PackedMatches Artifact.commitCode_0_148 longImageSpec 75776 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_149 : PackedMatches Artifact.commitCode_0_149 longImageSpec 76288 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_150 : PackedMatches Artifact.commitCode_0_150 longImageSpec 76800 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_151 : PackedMatches Artifact.commitCode_0_151 longImageSpec 77312 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_152 : PackedMatches Artifact.commitCode_0_152 longImageSpec 77824 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_153 : PackedMatches Artifact.commitCode_0_153 longImageSpec 78336 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_154 : PackedMatches Artifact.commitCode_0_154 longImageSpec 78848 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_155 : PackedMatches Artifact.commitCode_0_155 longImageSpec 79360 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_156 : PackedMatches Artifact.commitCode_0_156 longImageSpec 79872 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_157 : PackedMatches Artifact.commitCode_0_157 longImageSpec 80384 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_158 : PackedMatches Artifact.commitCode_0_158 longImageSpec 80896 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_159 : PackedMatches Artifact.commitCode_0_159 longImageSpec 81408 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_160 : PackedMatches Artifact.commitCode_0_160 longImageSpec 81920 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_161 : PackedMatches Artifact.commitCode_0_161 longImageSpec 82432 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_162 : PackedMatches Artifact.commitCode_0_162 longImageSpec 82944 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_163 : PackedMatches Artifact.commitCode_0_163 longImageSpec 83456 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_164 : PackedMatches Artifact.commitCode_0_164 longImageSpec 83968 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_165 : PackedMatches Artifact.commitCode_0_165 longImageSpec 84480 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_166 : PackedMatches Artifact.commitCode_0_166 longImageSpec 84992 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_167 : PackedMatches Artifact.commitCode_0_167 longImageSpec 85504 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_168 : PackedMatches Artifact.commitCode_0_168 longImageSpec 86016 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_169 : PackedMatches Artifact.commitCode_0_169 longImageSpec 86528 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_170 : PackedMatches Artifact.commitCode_0_170 longImageSpec 87040 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_171 : PackedMatches Artifact.commitCode_0_171 longImageSpec 87552 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_172 : PackedMatches Artifact.commitCode_0_172 longImageSpec 88064 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_173 : PackedMatches Artifact.commitCode_0_173 longImageSpec 88576 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_174 : PackedMatches Artifact.commitCode_0_174 longImageSpec 89088 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_175 : PackedMatches Artifact.commitCode_0_175 longImageSpec 89600 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_176 : PackedMatches Artifact.commitCode_0_176 longImageSpec 90112 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_177 : PackedMatches Artifact.commitCode_0_177 longImageSpec 90624 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_178 : PackedMatches Artifact.commitCode_0_178 longImageSpec 91136 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_179 : PackedMatches Artifact.commitCode_0_179 longImageSpec 91648 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_180 : PackedMatches Artifact.commitCode_0_180 longImageSpec 92160 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_181 : PackedMatches Artifact.commitCode_0_181 longImageSpec 92672 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_182 : PackedMatches Artifact.commitCode_0_182 longImageSpec 93184 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_183 : PackedMatches Artifact.commitCode_0_183 longImageSpec 93696 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_184 : PackedMatches Artifact.commitCode_0_184 longImageSpec 94208 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_185 : PackedMatches Artifact.commitCode_0_185 longImageSpec 94720 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_186 : PackedMatches Artifact.commitCode_0_186 longImageSpec 95232 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_187 : PackedMatches Artifact.commitCode_0_187 longImageSpec 95744 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_188 : PackedMatches Artifact.commitCode_0_188 longImageSpec 96256 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_189 : PackedMatches Artifact.commitCode_0_189 longImageSpec 96768 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_190 : PackedMatches Artifact.commitCode_0_190 longImageSpec 97280 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_191 : PackedMatches Artifact.commitCode_0_191 longImageSpec 97792 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_192 : PackedMatches Artifact.commitCode_0_192 longImageSpec 98304 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_193 : PackedMatches Artifact.commitCode_0_193 longImageSpec 98816 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_194 : PackedMatches Artifact.commitCode_0_194 longImageSpec 99328 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_195 : PackedMatches Artifact.commitCode_0_195 longImageSpec 99840 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_196 : PackedMatches Artifact.commitCode_0_196 longImageSpec 100352 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_197 : PackedMatches Artifact.commitCode_0_197 longImageSpec 100864 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_198 : PackedMatches Artifact.commitCode_0_198 longImageSpec 101376 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_199 : PackedMatches Artifact.commitCode_0_199 longImageSpec 101888 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_200 : PackedMatches Artifact.commitCode_0_200 longImageSpec 102400 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_201 : PackedMatches Artifact.commitCode_0_201 longImageSpec 102912 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_202 : PackedMatches Artifact.commitCode_0_202 longImageSpec 103424 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_203 : PackedMatches Artifact.commitCode_0_203 longImageSpec 103936 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_204 : PackedMatches Artifact.commitCode_0_204 longImageSpec 104448 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_205 : PackedMatches Artifact.commitCode_0_205 longImageSpec 104960 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_206 : PackedMatches Artifact.commitCode_0_206 longImageSpec 105472 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_207 : PackedMatches Artifact.commitCode_0_207 longImageSpec 105984 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_208 : PackedMatches Artifact.commitCode_0_208 longImageSpec 106496 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_209 : PackedMatches Artifact.commitCode_0_209 longImageSpec 107008 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_210 : PackedMatches Artifact.commitCode_0_210 longImageSpec 107520 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_211 : PackedMatches Artifact.commitCode_0_211 longImageSpec 108032 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_212 : PackedMatches Artifact.commitCode_0_212 longImageSpec 108544 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_213 : PackedMatches Artifact.commitCode_0_213 longImageSpec 109056 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_214 : PackedMatches Artifact.commitCode_0_214 longImageSpec 109568 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_215 : PackedMatches Artifact.commitCode_0_215 longImageSpec 110080 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_216 : PackedMatches Artifact.commitCode_0_216 longImageSpec 110592 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_217 : PackedMatches Artifact.commitCode_0_217 longImageSpec 111104 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_218 : PackedMatches Artifact.commitCode_0_218 longImageSpec 111616 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_219 : PackedMatches Artifact.commitCode_0_219 longImageSpec 112128 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_220 : PackedMatches Artifact.commitCode_0_220 longImageSpec 112640 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_221 : PackedMatches Artifact.commitCode_0_221 longImageSpec 113152 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_222 : PackedMatches Artifact.commitCode_0_222 longImageSpec 113664 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_223 : PackedMatches Artifact.commitCode_0_223 longImageSpec 114176 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_224 : PackedMatches Artifact.commitCode_0_224 longImageSpec 114688 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_225 : PackedMatches Artifact.commitCode_0_225 longImageSpec 115200 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_226 : PackedMatches Artifact.commitCode_0_226 longImageSpec 115712 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_227 : PackedMatches Artifact.commitCode_0_227 longImageSpec 116224 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_228 : PackedMatches Artifact.commitCode_0_228 longImageSpec 116736 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_229 : PackedMatches Artifact.commitCode_0_229 longImageSpec 117248 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_230 : PackedMatches Artifact.commitCode_0_230 longImageSpec 117760 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_231 : PackedMatches Artifact.commitCode_0_231 longImageSpec 118272 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_232 : PackedMatches Artifact.commitCode_0_232 longImageSpec 118784 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_233 : PackedMatches Artifact.commitCode_0_233 longImageSpec 119296 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_234 : PackedMatches Artifact.commitCode_0_234 longImageSpec 119808 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_235 : PackedMatches Artifact.commitCode_0_235 longImageSpec 120320 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_236 : PackedMatches Artifact.commitCode_0_236 longImageSpec 120832 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_237 : PackedMatches Artifact.commitCode_0_237 longImageSpec 121344 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_238 : PackedMatches Artifact.commitCode_0_238 longImageSpec 121856 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_239 : PackedMatches Artifact.commitCode_0_239 longImageSpec 122368 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_240 : PackedMatches Artifact.commitCode_0_240 longImageSpec 122880 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_241 : PackedMatches Artifact.commitCode_0_241 longImageSpec 123392 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_242 : PackedMatches Artifact.commitCode_0_242 longImageSpec 123904 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_243 : PackedMatches Artifact.commitCode_0_243 longImageSpec 124416 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_244 : PackedMatches Artifact.commitCode_0_244 longImageSpec 124928 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_245 : PackedMatches Artifact.commitCode_0_245 longImageSpec 125440 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_246 : PackedMatches Artifact.commitCode_0_246 longImageSpec 125952 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_247 : PackedMatches Artifact.commitCode_0_247 longImageSpec 126464 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_248 : PackedMatches Artifact.commitCode_0_248 longImageSpec 126976 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_249 : PackedMatches Artifact.commitCode_0_249 longImageSpec 127488 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_250 : PackedMatches Artifact.commitCode_0_250 longImageSpec 128000 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_251 : PackedMatches Artifact.commitCode_0_251 longImageSpec 128512 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_252 : PackedMatches Artifact.commitCode_0_252 longImageSpec 129024 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_253 : PackedMatches Artifact.commitCode_0_253 longImageSpec 129536 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_254 : PackedMatches Artifact.commitCode_0_254 longImageSpec 130048 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_255 : PackedMatches Artifact.commitCode_0_255 longImageSpec 130560 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_256 : PackedMatches Artifact.commitCode_0_256 longImageSpec 131072 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_257 : PackedMatches Artifact.commitCode_0_257 longImageSpec 131584 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_258 : PackedMatches Artifact.commitCode_0_258 longImageSpec 132096 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_259 : PackedMatches Artifact.commitCode_0_259 longImageSpec 132608 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_260 : PackedMatches Artifact.commitCode_0_260 longImageSpec 133120 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_261 : PackedMatches Artifact.commitCode_0_261 longImageSpec 133632 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_262 : PackedMatches Artifact.commitCode_0_262 longImageSpec 134144 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_263 : PackedMatches Artifact.commitCode_0_263 longImageSpec 134656 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_264 : PackedMatches Artifact.commitCode_0_264 longImageSpec 135168 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_265 : PackedMatches Artifact.commitCode_0_265 longImageSpec 135680 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_266 : PackedMatches Artifact.commitCode_0_266 longImageSpec 136192 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_267 : PackedMatches Artifact.commitCode_0_267 longImageSpec 136704 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_268 : PackedMatches Artifact.commitCode_0_268 longImageSpec 137216 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_269 : PackedMatches Artifact.commitCode_0_269 longImageSpec 137728 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_270 : PackedMatches Artifact.commitCode_0_270 longImageSpec 138240 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_271 : PackedMatches Artifact.commitCode_0_271 longImageSpec 138752 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_272 : PackedMatches Artifact.commitCode_0_272 longImageSpec 139264 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_273 : PackedMatches Artifact.commitCode_0_273 longImageSpec 139776 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_274 : PackedMatches Artifact.commitCode_0_274 longImageSpec 140288 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_275 : PackedMatches Artifact.commitCode_0_275 longImageSpec 140800 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_276 : PackedMatches Artifact.commitCode_0_276 longImageSpec 141312 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_277 : PackedMatches Artifact.commitCode_0_277 longImageSpec 141824 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_278 : PackedMatches Artifact.commitCode_0_278 longImageSpec 142336 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_279 : PackedMatches Artifact.commitCode_0_279 longImageSpec 142848 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_280 : PackedMatches Artifact.commitCode_0_280 longImageSpec 143360 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_281 : PackedMatches Artifact.commitCode_0_281 longImageSpec 143872 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_282 : PackedMatches Artifact.commitCode_0_282 longImageSpec 144384 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_283 : PackedMatches Artifact.commitCode_0_283 longImageSpec 144896 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_284 : PackedMatches Artifact.commitCode_0_284 longImageSpec 145408 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_285 : PackedMatches Artifact.commitCode_0_285 longImageSpec 145920 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_286 : PackedMatches Artifact.commitCode_0_286 longImageSpec 146432 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_287 : PackedMatches Artifact.commitCode_0_287 longImageSpec 146944 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_288 : PackedMatches Artifact.commitCode_0_288 longImageSpec 147456 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_289 : PackedMatches Artifact.commitCode_0_289 longImageSpec 147968 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_290 : PackedMatches Artifact.commitCode_0_290 longImageSpec 148480 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_291 : PackedMatches Artifact.commitCode_0_291 longImageSpec 148992 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_292 : PackedMatches Artifact.commitCode_0_292 longImageSpec 149504 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_293 : PackedMatches Artifact.commitCode_0_293 longImageSpec 150016 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_294 : PackedMatches Artifact.commitCode_0_294 longImageSpec 150528 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_295 : PackedMatches Artifact.commitCode_0_295 longImageSpec 151040 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_296 : PackedMatches Artifact.commitCode_0_296 longImageSpec 151552 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_297 : PackedMatches Artifact.commitCode_0_297 longImageSpec 152064 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_298 : PackedMatches Artifact.commitCode_0_298 longImageSpec 152576 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_299 : PackedMatches Artifact.commitCode_0_299 longImageSpec 153088 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_300 : PackedMatches Artifact.commitCode_0_300 longImageSpec 153600 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_301 : PackedMatches Artifact.commitCode_0_301 longImageSpec 154112 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_302 : PackedMatches Artifact.commitCode_0_302 longImageSpec 154624 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_303 : PackedMatches Artifact.commitCode_0_303 longImageSpec 155136 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_304 : PackedMatches Artifact.commitCode_0_304 longImageSpec 155648 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_305 : PackedMatches Artifact.commitCode_0_305 longImageSpec 156160 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_306 : PackedMatches Artifact.commitCode_0_306 longImageSpec 156672 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_307 : PackedMatches Artifact.commitCode_0_307 longImageSpec 157184 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_308 : PackedMatches Artifact.commitCode_0_308 longImageSpec 157696 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_309 : PackedMatches Artifact.commitCode_0_309 longImageSpec 158208 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_310 : PackedMatches Artifact.commitCode_0_310 longImageSpec 158720 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_311 : PackedMatches Artifact.commitCode_0_311 longImageSpec 159232 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_312 : PackedMatches Artifact.commitCode_0_312 longImageSpec 159744 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_313 : PackedMatches Artifact.commitCode_0_313 longImageSpec 160256 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_314 : PackedMatches Artifact.commitCode_0_314 longImageSpec 160768 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_315 : PackedMatches Artifact.commitCode_0_315 longImageSpec 161280 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_316 : PackedMatches Artifact.commitCode_0_316 longImageSpec 161792 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_317 : PackedMatches Artifact.commitCode_0_317 longImageSpec 162304 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_318 : PackedMatches Artifact.commitCode_0_318 longImageSpec 162816 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_319 : PackedMatches Artifact.commitCode_0_319 longImageSpec 163328 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_320 : PackedMatches Artifact.commitCode_0_320 longImageSpec 163840 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_321 : PackedMatches Artifact.commitCode_0_321 longImageSpec 164352 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_322 : PackedMatches Artifact.commitCode_0_322 longImageSpec 164864 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_323 : PackedMatches Artifact.commitCode_0_323 longImageSpec 165376 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_324 : PackedMatches Artifact.commitCode_0_324 longImageSpec 165888 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_325 : PackedMatches Artifact.commitCode_0_325 longImageSpec 166400 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_326 : PackedMatches Artifact.commitCode_0_326 longImageSpec 166912 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_327 : PackedMatches Artifact.commitCode_0_327 longImageSpec 167424 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_328 : PackedMatches Artifact.commitCode_0_328 longImageSpec 167936 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_329 : PackedMatches Artifact.commitCode_0_329 longImageSpec 168448 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_330 : PackedMatches Artifact.commitCode_0_330 longImageSpec 168960 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_331 : PackedMatches Artifact.commitCode_0_331 longImageSpec 169472 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_332 : PackedMatches Artifact.commitCode_0_332 longImageSpec 169984 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_333 : PackedMatches Artifact.commitCode_0_333 longImageSpec 170496 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_334 : PackedMatches Artifact.commitCode_0_334 longImageSpec 171008 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_335 : PackedMatches Artifact.commitCode_0_335 longImageSpec 171520 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_336 : PackedMatches Artifact.commitCode_0_336 longImageSpec 172032 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_337 : PackedMatches Artifact.commitCode_0_337 longImageSpec 172544 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_338 : PackedMatches Artifact.commitCode_0_338 longImageSpec 173056 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_339 : PackedMatches Artifact.commitCode_0_339 longImageSpec 173568 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_340 : PackedMatches Artifact.commitCode_0_340 longImageSpec 174080 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_341 : PackedMatches Artifact.commitCode_0_341 longImageSpec 174592 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_342 : PackedMatches Artifact.commitCode_0_342 longImageSpec 175104 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_343 : PackedMatches Artifact.commitCode_0_343 longImageSpec 175616 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_344 : PackedMatches Artifact.commitCode_0_344 longImageSpec 176128 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_345 : PackedMatches Artifact.commitCode_0_345 longImageSpec 176640 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_346 : PackedMatches Artifact.commitCode_0_346 longImageSpec 177152 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_347 : PackedMatches Artifact.commitCode_0_347 longImageSpec 177664 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_348 : PackedMatches Artifact.commitCode_0_348 longImageSpec 178176 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_349 : PackedMatches Artifact.commitCode_0_349 longImageSpec 178688 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_350 : PackedMatches Artifact.commitCode_0_350 longImageSpec 179200 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_351 : PackedMatches Artifact.commitCode_0_351 longImageSpec 179712 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_352 : PackedMatches Artifact.commitCode_0_352 longImageSpec 180224 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_353 : PackedMatches Artifact.commitCode_0_353 longImageSpec 180736 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_354 : PackedMatches Artifact.commitCode_0_354 longImageSpec 181248 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_355 : PackedMatches Artifact.commitCode_0_355 longImageSpec 181760 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_356 : PackedMatches Artifact.commitCode_0_356 longImageSpec 182272 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_357 : PackedMatches Artifact.commitCode_0_357 longImageSpec 182784 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_358 : PackedMatches Artifact.commitCode_0_358 longImageSpec 183296 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_359 : PackedMatches Artifact.commitCode_0_359 longImageSpec 183808 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_360 : PackedMatches Artifact.commitCode_0_360 longImageSpec 184320 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_361 : PackedMatches Artifact.commitCode_0_361 longImageSpec 184832 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_362 : PackedMatches Artifact.commitCode_0_362 longImageSpec 185344 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_363 : PackedMatches Artifact.commitCode_0_363 longImageSpec 185856 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_364 : PackedMatches Artifact.commitCode_0_364 longImageSpec 186368 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_365 : PackedMatches Artifact.commitCode_0_365 longImageSpec 186880 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_366 : PackedMatches Artifact.commitCode_0_366 longImageSpec 187392 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_367 : PackedMatches Artifact.commitCode_0_367 longImageSpec 187904 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_368 : PackedMatches Artifact.commitCode_0_368 longImageSpec 188416 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_369 : PackedMatches Artifact.commitCode_0_369 longImageSpec 188928 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_370 : PackedMatches Artifact.commitCode_0_370 longImageSpec 189440 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_371 : PackedMatches Artifact.commitCode_0_371 longImageSpec 189952 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_372 : PackedMatches Artifact.commitCode_0_372 longImageSpec 190464 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_373 : PackedMatches Artifact.commitCode_0_373 longImageSpec 190976 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_374 : PackedMatches Artifact.commitCode_0_374 longImageSpec 191488 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_375 : PackedMatches Artifact.commitCode_0_375 longImageSpec 192000 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_376 : PackedMatches Artifact.commitCode_0_376 longImageSpec 192512 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_377 : PackedMatches Artifact.commitCode_0_377 longImageSpec 193024 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_378 : PackedMatches Artifact.commitCode_0_378 longImageSpec 193536 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_379 : PackedMatches Artifact.commitCode_0_379 longImageSpec 194048 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_380 : PackedMatches Artifact.commitCode_0_380 longImageSpec 194560 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_381 : PackedMatches Artifact.commitCode_0_381 longImageSpec 195072 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_382 : PackedMatches Artifact.commitCode_0_382 longImageSpec 195584 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_383 : PackedMatches Artifact.commitCode_0_383 longImageSpec 196096 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_384 : PackedMatches Artifact.commitCode_0_384 longImageSpec 196608 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_385 : PackedMatches Artifact.commitCode_0_385 longImageSpec 197120 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_386 : PackedMatches Artifact.commitCode_0_386 longImageSpec 197632 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_387 : PackedMatches Artifact.commitCode_0_387 longImageSpec 198144 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_388 : PackedMatches Artifact.commitCode_0_388 longImageSpec 198656 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_389 : PackedMatches Artifact.commitCode_0_389 longImageSpec 199168 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_390 : PackedMatches Artifact.commitCode_0_390 longImageSpec 199680 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_391 : PackedMatches Artifact.commitCode_0_391 longImageSpec 200192 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_392 : PackedMatches Artifact.commitCode_0_392 longImageSpec 200704 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_393 : PackedMatches Artifact.commitCode_0_393 longImageSpec 201216 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_394 : PackedMatches Artifact.commitCode_0_394 longImageSpec 201728 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_395 : PackedMatches Artifact.commitCode_0_395 longImageSpec 202240 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_396 : PackedMatches Artifact.commitCode_0_396 longImageSpec 202752 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_397 : PackedMatches Artifact.commitCode_0_397 longImageSpec 203264 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_398 : PackedMatches Artifact.commitCode_0_398 longImageSpec 203776 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_399 : PackedMatches Artifact.commitCode_0_399 longImageSpec 204288 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_400 : PackedMatches Artifact.commitCode_0_400 longImageSpec 204800 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_401 : PackedMatches Artifact.commitCode_0_401 longImageSpec 205312 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_402 : PackedMatches Artifact.commitCode_0_402 longImageSpec 205824 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_403 : PackedMatches Artifact.commitCode_0_403 longImageSpec 206336 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_404 : PackedMatches Artifact.commitCode_0_404 longImageSpec 206848 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_405 : PackedMatches Artifact.commitCode_0_405 longImageSpec 207360 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_406 : PackedMatches Artifact.commitCode_0_406 longImageSpec 207872 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_407 : PackedMatches Artifact.commitCode_0_407 longImageSpec 208384 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_408 : PackedMatches Artifact.commitCode_0_408 longImageSpec 208896 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_409 : PackedMatches Artifact.commitCode_0_409 longImageSpec 209408 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_410 : PackedMatches Artifact.commitCode_0_410 longImageSpec 209920 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_411 : PackedMatches Artifact.commitCode_0_411 longImageSpec 210432 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_412 : PackedMatches Artifact.commitCode_0_412 longImageSpec 210944 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_413 : PackedMatches Artifact.commitCode_0_413 longImageSpec 211456 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_414 : PackedMatches Artifact.commitCode_0_414 longImageSpec 211968 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_415 : PackedMatches Artifact.commitCode_0_415 longImageSpec 212480 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_416 : PackedMatches Artifact.commitCode_0_416 longImageSpec 212992 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_417 : PackedMatches Artifact.commitCode_0_417 longImageSpec 213504 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_418 : PackedMatches Artifact.commitCode_0_418 longImageSpec 214016 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_419 : PackedMatches Artifact.commitCode_0_419 longImageSpec 214528 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_420 : PackedMatches Artifact.commitCode_0_420 longImageSpec 215040 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_421 : PackedMatches Artifact.commitCode_0_421 longImageSpec 215552 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_422 : PackedMatches Artifact.commitCode_0_422 longImageSpec 216064 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_423 : PackedMatches Artifact.commitCode_0_423 longImageSpec 216576 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_424 : PackedMatches Artifact.commitCode_0_424 longImageSpec 217088 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_425 : PackedMatches Artifact.commitCode_0_425 longImageSpec 217600 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_426 : PackedMatches Artifact.commitCode_0_426 longImageSpec 218112 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_427 : PackedMatches Artifact.commitCode_0_427 longImageSpec 218624 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_428 : PackedMatches Artifact.commitCode_0_428 longImageSpec 219136 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_429 : PackedMatches Artifact.commitCode_0_429 longImageSpec 219648 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_430 : PackedMatches Artifact.commitCode_0_430 longImageSpec 220160 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_431 : PackedMatches Artifact.commitCode_0_431 longImageSpec 220672 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_432 : PackedMatches Artifact.commitCode_0_432 longImageSpec 221184 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_433 : PackedMatches Artifact.commitCode_0_433 longImageSpec 221696 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_434 : PackedMatches Artifact.commitCode_0_434 longImageSpec 222208 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_435 : PackedMatches Artifact.commitCode_0_435 longImageSpec 222720 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_436 : PackedMatches Artifact.commitCode_0_436 longImageSpec 223232 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_437 : PackedMatches Artifact.commitCode_0_437 longImageSpec 223744 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_438 : PackedMatches Artifact.commitCode_0_438 longImageSpec 224256 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_439 : PackedMatches Artifact.commitCode_0_439 longImageSpec 224768 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_440 : PackedMatches Artifact.commitCode_0_440 longImageSpec 225280 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_441 : PackedMatches Artifact.commitCode_0_441 longImageSpec 225792 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_442 : PackedMatches Artifact.commitCode_0_442 longImageSpec 226304 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_443 : PackedMatches Artifact.commitCode_0_443 longImageSpec 226816 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_444 : PackedMatches Artifact.commitCode_0_444 longImageSpec 227328 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_445 : PackedMatches Artifact.commitCode_0_445 longImageSpec 227840 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_446 : PackedMatches Artifact.commitCode_0_446 longImageSpec 228352 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_447 : PackedMatches Artifact.commitCode_0_447 longImageSpec 228864 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_448 : PackedMatches Artifact.commitCode_0_448 longImageSpec 229376 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_449 : PackedMatches Artifact.commitCode_0_449 longImageSpec 229888 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_450 : PackedMatches Artifact.commitCode_0_450 longImageSpec 230400 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_451 : PackedMatches Artifact.commitCode_0_451 longImageSpec 230912 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_452 : PackedMatches Artifact.commitCode_0_452 longImageSpec 231424 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_453 : PackedMatches Artifact.commitCode_0_453 longImageSpec 231936 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_454 : PackedMatches Artifact.commitCode_0_454 longImageSpec 232448 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_455 : PackedMatches Artifact.commitCode_0_455 longImageSpec 232960 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_456 : PackedMatches Artifact.commitCode_0_456 longImageSpec 233472 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_457 : PackedMatches Artifact.commitCode_0_457 longImageSpec 233984 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_458 : PackedMatches Artifact.commitCode_0_458 longImageSpec 234496 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_459 : PackedMatches Artifact.commitCode_0_459 longImageSpec 235008 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_460 : PackedMatches Artifact.commitCode_0_460 longImageSpec 235520 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_461 : PackedMatches Artifact.commitCode_0_461 longImageSpec 236032 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_462 : PackedMatches Artifact.commitCode_0_462 longImageSpec 236544 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_463 : PackedMatches Artifact.commitCode_0_463 longImageSpec 237056 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_464 : PackedMatches Artifact.commitCode_0_464 longImageSpec 237568 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_465 : PackedMatches Artifact.commitCode_0_465 longImageSpec 238080 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_466 : PackedMatches Artifact.commitCode_0_466 longImageSpec 238592 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_467 : PackedMatches Artifact.commitCode_0_467 longImageSpec 239104 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_468 : PackedMatches Artifact.commitCode_0_468 longImageSpec 239616 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_469 : PackedMatches Artifact.commitCode_0_469 longImageSpec 240128 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_470 : PackedMatches Artifact.commitCode_0_470 longImageSpec 240640 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_471 : PackedMatches Artifact.commitCode_0_471 longImageSpec 241152 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_472 : PackedMatches Artifact.commitCode_0_472 longImageSpec 241664 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_473 : PackedMatches Artifact.commitCode_0_473 longImageSpec 242176 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_474 : PackedMatches Artifact.commitCode_0_474 longImageSpec 242688 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_475 : PackedMatches Artifact.commitCode_0_475 longImageSpec 243200 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_476 : PackedMatches Artifact.commitCode_0_476 longImageSpec 243712 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_477 : PackedMatches Artifact.commitCode_0_477 longImageSpec 244224 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_478 : PackedMatches Artifact.commitCode_0_478 longImageSpec 244736 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_479 : PackedMatches Artifact.commitCode_0_479 longImageSpec 245248 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_480 : PackedMatches Artifact.commitCode_0_480 longImageSpec 245760 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_481 : PackedMatches Artifact.commitCode_0_481 longImageSpec 246272 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_482 : PackedMatches Artifact.commitCode_0_482 longImageSpec 246784 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_483 : PackedMatches Artifact.commitCode_0_483 longImageSpec 247296 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_484 : PackedMatches Artifact.commitCode_0_484 longImageSpec 247808 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_485 : PackedMatches Artifact.commitCode_0_485 longImageSpec 248320 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_486 : PackedMatches Artifact.commitCode_0_486 longImageSpec 248832 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_487 : PackedMatches Artifact.commitCode_0_487 longImageSpec 249344 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_488 : PackedMatches Artifact.commitCode_0_488 longImageSpec 249856 := by
  apply packed_periodic_window _ 0 _ ?_ (by decide) (by decide) (by decide)
  intro index
  change Artifact.commitCode_0_2.get 32 index=group341BodyWord (0+index.val)
  rw [Nat.zero_add]
  exact packed_periodic_phase0 index

theorem packed_0_489 : PackedMatches Artifact.commitCode_0_489 longImageSpec 250368 := by
  apply packed_periodic_window _ 2 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase2

theorem packed_0_490 : PackedMatches Artifact.commitCode_0_490 longImageSpec 250880 := by
  apply packed_periodic_window _ 1 _ ?_ (by decide) (by decide) (by decide)
  exact packed_periodic_phase1

theorem packed_0_491 : PackedMatches Artifact.commitCode_0_491 longImageSpec 251392 := by
  exact packed_check_matches _ _ _ (by decide +kernel)

theorem packed_0_492 : PackedMatches Artifact.commitCode_0_492 longImageSpec (251824 + 80) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_493 : PackedMatches Artifact.commitCode_0_493 longImageSpec (251824 + 592) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_494 : PackedMatches Artifact.commitCode_0_494 longImageSpec (251824 + 1104) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_495 : PackedMatches Artifact.commitCode_0_495 longImageSpec (251824 + 1616) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_496 : PackedMatches Artifact.commitCode_0_496 longImageSpec (251824 + 2128) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_497 : PackedMatches Artifact.commitCode_0_497 longImageSpec (251824 + 2640) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_498 : PackedMatches Artifact.commitCode_0_498 longImageSpec (251824 + 3152) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_499 : PackedMatches Artifact.commitCode_0_499 longImageSpec (251824 + 3664) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_500 : PackedMatches Artifact.commitCode_0_500 longImageSpec (251824 + 4176) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_501 : PackedMatches Artifact.commitCode_0_501 longImageSpec (251824 + 4688) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_502 : PackedMatches Artifact.commitCode_0_502 longImageSpec (251824 + 5200) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_503 : PackedMatches Artifact.commitCode_0_503 longImageSpec (251824 + 5712) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_504 : PackedMatches Artifact.commitCode_0_504 longImageSpec (251824 + 6224) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_505 : PackedMatches Artifact.commitCode_0_505 longImageSpec (251824 + 6736) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_506 : PackedMatches Artifact.commitCode_0_506 longImageSpec (251824 + 7248) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_0_507 : PackedMatches Artifact.commitCode_0_507 longImageSpec (251824 + 7760) := by
  exact packed_end_matches _ _ (by decide +kernel) (by decide)

theorem packed_1_0 : PackedMatches Artifact.commitCode_1_0 longImageSpec 0 := by
  unfold Artifact.commitCode_1_0
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_0 packed_0_1) (packed_matches_join _ _ _ _ packed_0_2 packed_0_3)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_4 packed_0_5) (packed_matches_join _ _ _ _ packed_0_6 packed_0_7)))

theorem packed_1_1 : PackedMatches Artifact.commitCode_1_1 longImageSpec 4096 := by
  unfold Artifact.commitCode_1_1
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_8 packed_0_9) (packed_matches_join _ _ _ _ packed_0_10 packed_0_11)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_12 packed_0_13) (packed_matches_join _ _ _ _ packed_0_14 packed_0_15)))

theorem packed_1_2 : PackedMatches Artifact.commitCode_1_2 longImageSpec 8192 := by
  unfold Artifact.commitCode_1_2
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_16 packed_0_17) (packed_matches_join _ _ _ _ packed_0_18 packed_0_19)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_20 packed_0_21) (packed_matches_join _ _ _ _ packed_0_22 packed_0_23)))

theorem packed_1_3 : PackedMatches Artifact.commitCode_1_3 longImageSpec 12288 := by
  unfold Artifact.commitCode_1_3
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_24 packed_0_25) (packed_matches_join _ _ _ _ packed_0_26 packed_0_27)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_28 packed_0_29) (packed_matches_join _ _ _ _ packed_0_30 packed_0_31)))

theorem packed_1_4 : PackedMatches Artifact.commitCode_1_4 longImageSpec 16384 := by
  unfold Artifact.commitCode_1_4
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_32 packed_0_33) (packed_matches_join _ _ _ _ packed_0_34 packed_0_35)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_36 packed_0_37) (packed_matches_join _ _ _ _ packed_0_38 packed_0_39)))

theorem packed_1_5 : PackedMatches Artifact.commitCode_1_5 longImageSpec 20480 := by
  unfold Artifact.commitCode_1_5
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_40 packed_0_41) (packed_matches_join _ _ _ _ packed_0_42 packed_0_43)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_44 packed_0_45) (packed_matches_join _ _ _ _ packed_0_46 packed_0_47)))

theorem packed_1_6 : PackedMatches Artifact.commitCode_1_6 longImageSpec 24576 := by
  unfold Artifact.commitCode_1_6
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_48 packed_0_49) (packed_matches_join _ _ _ _ packed_0_50 packed_0_51)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_52 packed_0_53) (packed_matches_join _ _ _ _ packed_0_54 packed_0_55)))

theorem packed_1_7 : PackedMatches Artifact.commitCode_1_7 longImageSpec 28672 := by
  unfold Artifact.commitCode_1_7
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_56 packed_0_57) (packed_matches_join _ _ _ _ packed_0_58 packed_0_59)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_60 packed_0_61) (packed_matches_join _ _ _ _ packed_0_62 packed_0_63)))

theorem packed_1_8 : PackedMatches Artifact.commitCode_1_8 longImageSpec 32768 := by
  unfold Artifact.commitCode_1_8
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_64 packed_0_65) (packed_matches_join _ _ _ _ packed_0_66 packed_0_67)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_68 packed_0_69) (packed_matches_join _ _ _ _ packed_0_70 packed_0_71)))

theorem packed_1_9 : PackedMatches Artifact.commitCode_1_9 longImageSpec 36864 := by
  unfold Artifact.commitCode_1_9
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_72 packed_0_73) (packed_matches_join _ _ _ _ packed_0_74 packed_0_75)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_76 packed_0_77) (packed_matches_join _ _ _ _ packed_0_78 packed_0_79)))

theorem packed_1_10 : PackedMatches Artifact.commitCode_1_10 longImageSpec 40960 := by
  unfold Artifact.commitCode_1_10
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_80 packed_0_81) (packed_matches_join _ _ _ _ packed_0_82 packed_0_83)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_84 packed_0_85) (packed_matches_join _ _ _ _ packed_0_86 packed_0_87)))

theorem packed_1_11 : PackedMatches Artifact.commitCode_1_11 longImageSpec 45056 := by
  unfold Artifact.commitCode_1_11
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_88 packed_0_89) (packed_matches_join _ _ _ _ packed_0_90 packed_0_91)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_92 packed_0_93) (packed_matches_join _ _ _ _ packed_0_94 packed_0_95)))

theorem packed_1_12 : PackedMatches Artifact.commitCode_1_12 longImageSpec 49152 := by
  unfold Artifact.commitCode_1_12
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_96 packed_0_97) (packed_matches_join _ _ _ _ packed_0_98 packed_0_99)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_100 packed_0_101) (packed_matches_join _ _ _ _ packed_0_102 packed_0_103)))

theorem packed_1_13 : PackedMatches Artifact.commitCode_1_13 longImageSpec 53248 := by
  unfold Artifact.commitCode_1_13
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_104 packed_0_105) (packed_matches_join _ _ _ _ packed_0_106 packed_0_107)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_108 packed_0_109) (packed_matches_join _ _ _ _ packed_0_110 packed_0_111)))

theorem packed_1_14 : PackedMatches Artifact.commitCode_1_14 longImageSpec 57344 := by
  unfold Artifact.commitCode_1_14
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_112 packed_0_113) (packed_matches_join _ _ _ _ packed_0_114 packed_0_115)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_116 packed_0_117) (packed_matches_join _ _ _ _ packed_0_118 packed_0_119)))

theorem packed_1_15 : PackedMatches Artifact.commitCode_1_15 longImageSpec 61440 := by
  unfold Artifact.commitCode_1_15
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_120 packed_0_121) (packed_matches_join _ _ _ _ packed_0_122 packed_0_123)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_124 packed_0_125) (packed_matches_join _ _ _ _ packed_0_126 packed_0_127)))

theorem packed_1_16 : PackedMatches Artifact.commitCode_1_16 longImageSpec 65536 := by
  unfold Artifact.commitCode_1_16
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_128 packed_0_129) (packed_matches_join _ _ _ _ packed_0_130 packed_0_131)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_132 packed_0_133) (packed_matches_join _ _ _ _ packed_0_134 packed_0_135)))

theorem packed_1_17 : PackedMatches Artifact.commitCode_1_17 longImageSpec 69632 := by
  unfold Artifact.commitCode_1_17
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_136 packed_0_137) (packed_matches_join _ _ _ _ packed_0_138 packed_0_139)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_140 packed_0_141) (packed_matches_join _ _ _ _ packed_0_142 packed_0_143)))

theorem packed_1_18 : PackedMatches Artifact.commitCode_1_18 longImageSpec 73728 := by
  unfold Artifact.commitCode_1_18
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_144 packed_0_145) (packed_matches_join _ _ _ _ packed_0_146 packed_0_147)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_148 packed_0_149) (packed_matches_join _ _ _ _ packed_0_150 packed_0_151)))

theorem packed_1_19 : PackedMatches Artifact.commitCode_1_19 longImageSpec 77824 := by
  unfold Artifact.commitCode_1_19
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_152 packed_0_153) (packed_matches_join _ _ _ _ packed_0_154 packed_0_155)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_156 packed_0_157) (packed_matches_join _ _ _ _ packed_0_158 packed_0_159)))

theorem packed_1_20 : PackedMatches Artifact.commitCode_1_20 longImageSpec 81920 := by
  unfold Artifact.commitCode_1_20
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_160 packed_0_161) (packed_matches_join _ _ _ _ packed_0_162 packed_0_163)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_164 packed_0_165) (packed_matches_join _ _ _ _ packed_0_166 packed_0_167)))

theorem packed_1_21 : PackedMatches Artifact.commitCode_1_21 longImageSpec 86016 := by
  unfold Artifact.commitCode_1_21
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_168 packed_0_169) (packed_matches_join _ _ _ _ packed_0_170 packed_0_171)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_172 packed_0_173) (packed_matches_join _ _ _ _ packed_0_174 packed_0_175)))

theorem packed_1_22 : PackedMatches Artifact.commitCode_1_22 longImageSpec 90112 := by
  unfold Artifact.commitCode_1_22
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_176 packed_0_177) (packed_matches_join _ _ _ _ packed_0_178 packed_0_179)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_180 packed_0_181) (packed_matches_join _ _ _ _ packed_0_182 packed_0_183)))

theorem packed_1_23 : PackedMatches Artifact.commitCode_1_23 longImageSpec 94208 := by
  unfold Artifact.commitCode_1_23
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_184 packed_0_185) (packed_matches_join _ _ _ _ packed_0_186 packed_0_187)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_188 packed_0_189) (packed_matches_join _ _ _ _ packed_0_190 packed_0_191)))

theorem packed_1_24 : PackedMatches Artifact.commitCode_1_24 longImageSpec 98304 := by
  unfold Artifact.commitCode_1_24
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_192 packed_0_193) (packed_matches_join _ _ _ _ packed_0_194 packed_0_195)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_196 packed_0_197) (packed_matches_join _ _ _ _ packed_0_198 packed_0_199)))

theorem packed_1_25 : PackedMatches Artifact.commitCode_1_25 longImageSpec 102400 := by
  unfold Artifact.commitCode_1_25
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_200 packed_0_201) (packed_matches_join _ _ _ _ packed_0_202 packed_0_203)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_204 packed_0_205) (packed_matches_join _ _ _ _ packed_0_206 packed_0_207)))

theorem packed_1_26 : PackedMatches Artifact.commitCode_1_26 longImageSpec 106496 := by
  unfold Artifact.commitCode_1_26
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_208 packed_0_209) (packed_matches_join _ _ _ _ packed_0_210 packed_0_211)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_212 packed_0_213) (packed_matches_join _ _ _ _ packed_0_214 packed_0_215)))

theorem packed_1_27 : PackedMatches Artifact.commitCode_1_27 longImageSpec 110592 := by
  unfold Artifact.commitCode_1_27
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_216 packed_0_217) (packed_matches_join _ _ _ _ packed_0_218 packed_0_219)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_220 packed_0_221) (packed_matches_join _ _ _ _ packed_0_222 packed_0_223)))

theorem packed_1_28 : PackedMatches Artifact.commitCode_1_28 longImageSpec 114688 := by
  unfold Artifact.commitCode_1_28
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_224 packed_0_225) (packed_matches_join _ _ _ _ packed_0_226 packed_0_227)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_228 packed_0_229) (packed_matches_join _ _ _ _ packed_0_230 packed_0_231)))

theorem packed_1_29 : PackedMatches Artifact.commitCode_1_29 longImageSpec 118784 := by
  unfold Artifact.commitCode_1_29
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_232 packed_0_233) (packed_matches_join _ _ _ _ packed_0_234 packed_0_235)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_236 packed_0_237) (packed_matches_join _ _ _ _ packed_0_238 packed_0_239)))

theorem packed_1_30 : PackedMatches Artifact.commitCode_1_30 longImageSpec 122880 := by
  unfold Artifact.commitCode_1_30
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_240 packed_0_241) (packed_matches_join _ _ _ _ packed_0_242 packed_0_243)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_244 packed_0_245) (packed_matches_join _ _ _ _ packed_0_246 packed_0_247)))

theorem packed_1_31 : PackedMatches Artifact.commitCode_1_31 longImageSpec 126976 := by
  unfold Artifact.commitCode_1_31
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_248 packed_0_249) (packed_matches_join _ _ _ _ packed_0_250 packed_0_251)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_252 packed_0_253) (packed_matches_join _ _ _ _ packed_0_254 packed_0_255)))

theorem packed_1_32 : PackedMatches Artifact.commitCode_1_32 longImageSpec 131072 := by
  unfold Artifact.commitCode_1_32
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_256 packed_0_257) (packed_matches_join _ _ _ _ packed_0_258 packed_0_259)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_260 packed_0_261) (packed_matches_join _ _ _ _ packed_0_262 packed_0_263)))

theorem packed_1_33 : PackedMatches Artifact.commitCode_1_33 longImageSpec 135168 := by
  unfold Artifact.commitCode_1_33
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_264 packed_0_265) (packed_matches_join _ _ _ _ packed_0_266 packed_0_267)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_268 packed_0_269) (packed_matches_join _ _ _ _ packed_0_270 packed_0_271)))

theorem packed_1_34 : PackedMatches Artifact.commitCode_1_34 longImageSpec 139264 := by
  unfold Artifact.commitCode_1_34
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_272 packed_0_273) (packed_matches_join _ _ _ _ packed_0_274 packed_0_275)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_276 packed_0_277) (packed_matches_join _ _ _ _ packed_0_278 packed_0_279)))

theorem packed_1_35 : PackedMatches Artifact.commitCode_1_35 longImageSpec 143360 := by
  unfold Artifact.commitCode_1_35
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_280 packed_0_281) (packed_matches_join _ _ _ _ packed_0_282 packed_0_283)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_284 packed_0_285) (packed_matches_join _ _ _ _ packed_0_286 packed_0_287)))

theorem packed_1_36 : PackedMatches Artifact.commitCode_1_36 longImageSpec 147456 := by
  unfold Artifact.commitCode_1_36
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_288 packed_0_289) (packed_matches_join _ _ _ _ packed_0_290 packed_0_291)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_292 packed_0_293) (packed_matches_join _ _ _ _ packed_0_294 packed_0_295)))

theorem packed_1_37 : PackedMatches Artifact.commitCode_1_37 longImageSpec 151552 := by
  unfold Artifact.commitCode_1_37
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_296 packed_0_297) (packed_matches_join _ _ _ _ packed_0_298 packed_0_299)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_300 packed_0_301) (packed_matches_join _ _ _ _ packed_0_302 packed_0_303)))

theorem packed_1_38 : PackedMatches Artifact.commitCode_1_38 longImageSpec 155648 := by
  unfold Artifact.commitCode_1_38
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_304 packed_0_305) (packed_matches_join _ _ _ _ packed_0_306 packed_0_307)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_308 packed_0_309) (packed_matches_join _ _ _ _ packed_0_310 packed_0_311)))

theorem packed_1_39 : PackedMatches Artifact.commitCode_1_39 longImageSpec 159744 := by
  unfold Artifact.commitCode_1_39
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_312 packed_0_313) (packed_matches_join _ _ _ _ packed_0_314 packed_0_315)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_316 packed_0_317) (packed_matches_join _ _ _ _ packed_0_318 packed_0_319)))

theorem packed_1_40 : PackedMatches Artifact.commitCode_1_40 longImageSpec 163840 := by
  unfold Artifact.commitCode_1_40
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_320 packed_0_321) (packed_matches_join _ _ _ _ packed_0_322 packed_0_323)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_324 packed_0_325) (packed_matches_join _ _ _ _ packed_0_326 packed_0_327)))

theorem packed_1_41 : PackedMatches Artifact.commitCode_1_41 longImageSpec 167936 := by
  unfold Artifact.commitCode_1_41
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_328 packed_0_329) (packed_matches_join _ _ _ _ packed_0_330 packed_0_331)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_332 packed_0_333) (packed_matches_join _ _ _ _ packed_0_334 packed_0_335)))

theorem packed_1_42 : PackedMatches Artifact.commitCode_1_42 longImageSpec 172032 := by
  unfold Artifact.commitCode_1_42
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_336 packed_0_337) (packed_matches_join _ _ _ _ packed_0_338 packed_0_339)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_340 packed_0_341) (packed_matches_join _ _ _ _ packed_0_342 packed_0_343)))

theorem packed_1_43 : PackedMatches Artifact.commitCode_1_43 longImageSpec 176128 := by
  unfold Artifact.commitCode_1_43
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_344 packed_0_345) (packed_matches_join _ _ _ _ packed_0_346 packed_0_347)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_348 packed_0_349) (packed_matches_join _ _ _ _ packed_0_350 packed_0_351)))

theorem packed_1_44 : PackedMatches Artifact.commitCode_1_44 longImageSpec 180224 := by
  unfold Artifact.commitCode_1_44
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_352 packed_0_353) (packed_matches_join _ _ _ _ packed_0_354 packed_0_355)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_356 packed_0_357) (packed_matches_join _ _ _ _ packed_0_358 packed_0_359)))

theorem packed_1_45 : PackedMatches Artifact.commitCode_1_45 longImageSpec 184320 := by
  unfold Artifact.commitCode_1_45
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_360 packed_0_361) (packed_matches_join _ _ _ _ packed_0_362 packed_0_363)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_364 packed_0_365) (packed_matches_join _ _ _ _ packed_0_366 packed_0_367)))

theorem packed_1_46 : PackedMatches Artifact.commitCode_1_46 longImageSpec 188416 := by
  unfold Artifact.commitCode_1_46
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_368 packed_0_369) (packed_matches_join _ _ _ _ packed_0_370 packed_0_371)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_372 packed_0_373) (packed_matches_join _ _ _ _ packed_0_374 packed_0_375)))

theorem packed_1_47 : PackedMatches Artifact.commitCode_1_47 longImageSpec 192512 := by
  unfold Artifact.commitCode_1_47
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_376 packed_0_377) (packed_matches_join _ _ _ _ packed_0_378 packed_0_379)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_380 packed_0_381) (packed_matches_join _ _ _ _ packed_0_382 packed_0_383)))

theorem packed_1_48 : PackedMatches Artifact.commitCode_1_48 longImageSpec 196608 := by
  unfold Artifact.commitCode_1_48
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_384 packed_0_385) (packed_matches_join _ _ _ _ packed_0_386 packed_0_387)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_388 packed_0_389) (packed_matches_join _ _ _ _ packed_0_390 packed_0_391)))

theorem packed_1_49 : PackedMatches Artifact.commitCode_1_49 longImageSpec 200704 := by
  unfold Artifact.commitCode_1_49
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_392 packed_0_393) (packed_matches_join _ _ _ _ packed_0_394 packed_0_395)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_396 packed_0_397) (packed_matches_join _ _ _ _ packed_0_398 packed_0_399)))

theorem packed_1_50 : PackedMatches Artifact.commitCode_1_50 longImageSpec 204800 := by
  unfold Artifact.commitCode_1_50
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_400 packed_0_401) (packed_matches_join _ _ _ _ packed_0_402 packed_0_403)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_404 packed_0_405) (packed_matches_join _ _ _ _ packed_0_406 packed_0_407)))

theorem packed_1_51 : PackedMatches Artifact.commitCode_1_51 longImageSpec 208896 := by
  unfold Artifact.commitCode_1_51
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_408 packed_0_409) (packed_matches_join _ _ _ _ packed_0_410 packed_0_411)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_412 packed_0_413) (packed_matches_join _ _ _ _ packed_0_414 packed_0_415)))

theorem packed_1_52 : PackedMatches Artifact.commitCode_1_52 longImageSpec 212992 := by
  unfold Artifact.commitCode_1_52
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_416 packed_0_417) (packed_matches_join _ _ _ _ packed_0_418 packed_0_419)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_420 packed_0_421) (packed_matches_join _ _ _ _ packed_0_422 packed_0_423)))

theorem packed_1_53 : PackedMatches Artifact.commitCode_1_53 longImageSpec 217088 := by
  unfold Artifact.commitCode_1_53
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_424 packed_0_425) (packed_matches_join _ _ _ _ packed_0_426 packed_0_427)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_428 packed_0_429) (packed_matches_join _ _ _ _ packed_0_430 packed_0_431)))

theorem packed_1_54 : PackedMatches Artifact.commitCode_1_54 longImageSpec 221184 := by
  unfold Artifact.commitCode_1_54
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_432 packed_0_433) (packed_matches_join _ _ _ _ packed_0_434 packed_0_435)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_436 packed_0_437) (packed_matches_join _ _ _ _ packed_0_438 packed_0_439)))

theorem packed_1_55 : PackedMatches Artifact.commitCode_1_55 longImageSpec 225280 := by
  unfold Artifact.commitCode_1_55
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_440 packed_0_441) (packed_matches_join _ _ _ _ packed_0_442 packed_0_443)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_444 packed_0_445) (packed_matches_join _ _ _ _ packed_0_446 packed_0_447)))

theorem packed_1_56 : PackedMatches Artifact.commitCode_1_56 longImageSpec 229376 := by
  unfold Artifact.commitCode_1_56
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_448 packed_0_449) (packed_matches_join _ _ _ _ packed_0_450 packed_0_451)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_452 packed_0_453) (packed_matches_join _ _ _ _ packed_0_454 packed_0_455)))

theorem packed_1_57 : PackedMatches Artifact.commitCode_1_57 longImageSpec 233472 := by
  unfold Artifact.commitCode_1_57
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_456 packed_0_457) (packed_matches_join _ _ _ _ packed_0_458 packed_0_459)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_460 packed_0_461) (packed_matches_join _ _ _ _ packed_0_462 packed_0_463)))

theorem packed_1_58 : PackedMatches Artifact.commitCode_1_58 longImageSpec 237568 := by
  unfold Artifact.commitCode_1_58
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_464 packed_0_465) (packed_matches_join _ _ _ _ packed_0_466 packed_0_467)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_468 packed_0_469) (packed_matches_join _ _ _ _ packed_0_470 packed_0_471)))

theorem packed_1_59 : PackedMatches Artifact.commitCode_1_59 longImageSpec 241664 := by
  unfold Artifact.commitCode_1_59
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_472 packed_0_473) (packed_matches_join _ _ _ _ packed_0_474 packed_0_475)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_476 packed_0_477) (packed_matches_join _ _ _ _ packed_0_478 packed_0_479)))

theorem packed_1_60 : PackedMatches Artifact.commitCode_1_60 longImageSpec 245760 := by
  unfold Artifact.commitCode_1_60
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_480 packed_0_481) (packed_matches_join _ _ _ _ packed_0_482 packed_0_483)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_484 packed_0_485) (packed_matches_join _ _ _ _ packed_0_486 packed_0_487)))

theorem packed_1_61 : PackedMatches Artifact.commitCode_1_61 longImageSpec 249856 := by
  unfold Artifact.commitCode_1_61
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_488 packed_0_489) (packed_matches_join _ _ _ _ packed_0_490 packed_0_491)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_492 packed_0_493) (packed_matches_join _ _ _ _ packed_0_494 packed_0_495)))

theorem packed_1_62 : PackedMatches Artifact.commitCode_1_62 longImageSpec 253952 := by
  unfold Artifact.commitCode_1_62
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_496 packed_0_497) (packed_matches_join _ _ _ _ packed_0_498 packed_0_499)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_500 packed_0_501) (packed_matches_join _ _ _ _ packed_0_502 packed_0_503)))

theorem packed_1_63 : PackedMatches Artifact.commitCode_1_63 longImageSpec 258048 := by
  unfold Artifact.commitCode_1_63
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_0_504 packed_0_505) (packed_matches_join _ _ _ _ packed_0_506 packed_0_507))

theorem packed_2_0 : PackedMatches Artifact.commitCode_2_0 longImageSpec 0 := by
  unfold Artifact.commitCode_2_0
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_0 packed_1_1) (packed_matches_join _ _ _ _ packed_1_2 packed_1_3)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_4 packed_1_5) (packed_matches_join _ _ _ _ packed_1_6 packed_1_7)))

theorem packed_2_1 : PackedMatches Artifact.commitCode_2_1 longImageSpec 32768 := by
  unfold Artifact.commitCode_2_1
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_8 packed_1_9) (packed_matches_join _ _ _ _ packed_1_10 packed_1_11)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_12 packed_1_13) (packed_matches_join _ _ _ _ packed_1_14 packed_1_15)))

theorem packed_2_2 : PackedMatches Artifact.commitCode_2_2 longImageSpec 65536 := by
  unfold Artifact.commitCode_2_2
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_16 packed_1_17) (packed_matches_join _ _ _ _ packed_1_18 packed_1_19)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_20 packed_1_21) (packed_matches_join _ _ _ _ packed_1_22 packed_1_23)))

theorem packed_2_3 : PackedMatches Artifact.commitCode_2_3 longImageSpec 98304 := by
  unfold Artifact.commitCode_2_3
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_24 packed_1_25) (packed_matches_join _ _ _ _ packed_1_26 packed_1_27)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_28 packed_1_29) (packed_matches_join _ _ _ _ packed_1_30 packed_1_31)))

theorem packed_2_4 : PackedMatches Artifact.commitCode_2_4 longImageSpec 131072 := by
  unfold Artifact.commitCode_2_4
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_32 packed_1_33) (packed_matches_join _ _ _ _ packed_1_34 packed_1_35)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_36 packed_1_37) (packed_matches_join _ _ _ _ packed_1_38 packed_1_39)))

theorem packed_2_5 : PackedMatches Artifact.commitCode_2_5 longImageSpec 163840 := by
  unfold Artifact.commitCode_2_5
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_40 packed_1_41) (packed_matches_join _ _ _ _ packed_1_42 packed_1_43)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_44 packed_1_45) (packed_matches_join _ _ _ _ packed_1_46 packed_1_47)))

theorem packed_2_6 : PackedMatches Artifact.commitCode_2_6 longImageSpec 196608 := by
  unfold Artifact.commitCode_2_6
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_48 packed_1_49) (packed_matches_join _ _ _ _ packed_1_50 packed_1_51)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_52 packed_1_53) (packed_matches_join _ _ _ _ packed_1_54 packed_1_55)))

theorem packed_2_7 : PackedMatches Artifact.commitCode_2_7 longImageSpec 229376 := by
  unfold Artifact.commitCode_2_7
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_56 packed_1_57) (packed_matches_join _ _ _ _ packed_1_58 packed_1_59)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_1_60 packed_1_61) (packed_matches_join _ _ _ _ packed_1_62 packed_1_63)))

theorem packed_complete_matches : PackedMatches Artifact.commitCode longImageSpec 0 := by
  unfold Artifact.commitCode
  exact (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_2_0 packed_2_1) (packed_matches_join _ _ _ _ packed_2_2 packed_2_3)) (packed_matches_join _ _ _ _ (packed_matches_join _ _ _ _ packed_2_4 packed_2_5) (packed_matches_join _ _ _ _ packed_2_6 packed_2_7)))

theorem candidate_image_getD_spec (index : Nat) (bounded : index<259972) :
    group341ImageWords.getD index 0=longImageSpec index := by
  unfold longImageSpec
  by_cases head : index<166
  · rw [if_pos head]
    unfold group341ImageWords
    rw [List.getD_append _ _ _ _ (by rw [group341_head_length];exact head)]
  · rw [if_neg head]
    unfold group341ImageWords
    rw [List.getD_append_right _ _ _ _ (by rw [group341_head_length];omega),group341_head_length]
    by_cases body : index<251824
    · rw [if_pos body,List.getD_append _ _ _ _ (by rw [group341_body_length];omega)]
      rw [List.getD_eq_getElem _ _ (by rw [group341_body_length];omega)]
      simp only [group341BodyWords,List.getElem_ofFn]
    · rw [if_neg body,List.getD_append_right _ _ _ _ (by rw [group341_body_length];omega),group341_body_length]
      rw [Nat.sub_sub]

theorem packed_code_matches_image :
    group341ImageWords=ArtifactEncoding.decode 32 Artifact.commitCode := by
  apply List.ext_getElem
  · rw [group341_image_length,ArtifactEncoding.length_decode]
  · intro index leftBound rightBound
    have bounded : index<259972 := by rw [group341_image_length] at leftBound;exact leftBound
    rw [← List.getD_eq_getElem _ 0 leftBound,← List.getD_eq_getElem _ 0 rightBound,
      candidate_image_getD_spec index bounded,ArtifactEncoding.getD_decode 32 Artifact.commitCode index bounded]
    simpa only [Nat.zero_add] using (packed_complete_matches ⟨index,bounded⟩).symm


theorem nonce_packed_submission_matches : nonceCompressedProgram=Artifact.submission := by
  have images : nonceCompressedProgram.image=Artifact.submission.image := by
    funext program
    cases program with
    | commit =>
      change (⟨group341ImageWords,[]⟩ : Riscv.Image)=
        ⟨ArtifactEncoding.decode 32 Artifact.commitCode,ArtifactEncoding.decode 8 Artifact.commitData⟩
      exact congrArg (fun code => (⟨code,[]⟩ : Riscv.Image)) packed_code_matches_image
    | opening => rfl
    | check => rfl
  change (Submission.mk nonceCompressedProgram.sizes nonceCompressedProgram.layout nonceCompressedProgram.image nonceCompressedProgram.steps)=
    (Submission.mk nonceCompressedProgram.sizes nonceCompressedProgram.layout Artifact.submission.image nonceCompressedProgram.steps)
  exact congrArg (fun image => Submission.mk nonceCompressedProgram.sizes nonceCompressedProgram.layout image nonceCompressedProgram.steps) images

end CommitGolfCandidate
