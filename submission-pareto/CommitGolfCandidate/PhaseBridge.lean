import CommitGolfCandidate.PhaseImage
import CommitGolfCandidate.GroupOpenImage

namespace TwoPermutationPrototype.PhaseOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 GroupedOpening
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

def validBlock (b : Nat) : Bool :=
  (List.range 32).all fun j =>
    let n:=32*b+j
    if h : 761≤n ∧ n<2680 then MaterializedArtifact.openingCode.get 32 ⟨n,h.2⟩ == (wordAt n).getD 0 else true

private theorem block_0 : validBlock 0=true := by decide
private theorem block_1 : validBlock 1=true := by decide
private theorem block_2 : validBlock 2=true := by decide
private theorem block_3 : validBlock 3=true := by decide
private theorem block_4 : validBlock 4=true := by decide
private theorem block_5 : validBlock 5=true := by decide
private theorem block_6 : validBlock 6=true := by decide
private theorem block_7 : validBlock 7=true := by decide
private theorem block_8 : validBlock 8=true := by decide
private theorem block_9 : validBlock 9=true := by decide
private theorem block_10 : validBlock 10=true := by decide
private theorem block_11 : validBlock 11=true := by decide
private theorem block_12 : validBlock 12=true := by decide
private theorem block_13 : validBlock 13=true := by decide
private theorem block_14 : validBlock 14=true := by decide
private theorem block_15 : validBlock 15=true := by decide
private theorem block_16 : validBlock 16=true := by decide
private theorem block_17 : validBlock 17=true := by decide
private theorem block_18 : validBlock 18=true := by decide
private theorem block_19 : validBlock 19=true := by decide
private theorem block_20 : validBlock 20=true := by decide
private theorem block_21 : validBlock 21=true := by decide
private theorem block_22 : validBlock 22=true := by decide
private theorem block_23 : validBlock 23=true := by decide
private theorem block_24 : validBlock 24=true := by decide
private theorem block_25 : validBlock 25=true := by decide
private theorem block_26 : validBlock 26=true := by decide
private theorem block_27 : validBlock 27=true := by decide
private theorem block_28 : validBlock 28=true := by decide
private theorem block_29 : validBlock 29=true := by decide
private theorem block_30 : validBlock 30=true := by decide
private theorem block_31 : validBlock 31=true := by decide
private theorem block_32 : validBlock 32=true := by decide
private theorem block_33 : validBlock 33=true := by decide
private theorem block_34 : validBlock 34=true := by decide
private theorem block_35 : validBlock 35=true := by decide
private theorem block_36 : validBlock 36=true := by decide
private theorem block_37 : validBlock 37=true := by decide
private theorem block_38 : validBlock 38=true := by decide
private theorem block_39 : validBlock 39=true := by decide
private theorem block_40 : validBlock 40=true := by decide
private theorem block_41 : validBlock 41=true := by decide
private theorem block_42 : validBlock 42=true := by decide
private theorem block_43 : validBlock 43=true := by decide
private theorem block_44 : validBlock 44=true := by decide
private theorem block_45 : validBlock 45=true := by decide
private theorem block_46 : validBlock 46=true := by decide
private theorem block_47 : validBlock 47=true := by decide
private theorem block_48 : validBlock 48=true := by decide
private theorem block_49 : validBlock 49=true := by decide
private theorem block_50 : validBlock 50=true := by decide
private theorem block_51 : validBlock 51=true := by decide
private theorem block_52 : validBlock 52=true := by decide
private theorem block_53 : validBlock 53=true := by decide
private theorem block_54 : validBlock 54=true := by decide
private theorem block_55 : validBlock 55=true := by decide
private theorem block_56 : validBlock 56=true := by decide
private theorem block_57 : validBlock 57=true := by decide
private theorem block_58 : validBlock 58=true := by decide
private theorem block_59 : validBlock 59=true := by decide
private theorem block_60 : validBlock 60=true := by decide
private theorem block_61 : validBlock 61=true := by decide
private theorem block_62 : validBlock 62=true := by decide
private theorem block_63 : validBlock 63=true := by decide
private theorem block_64 : validBlock 64=true := by decide
private theorem block_65 : validBlock 65=true := by decide
private theorem block_66 : validBlock 66=true := by decide
private theorem block_67 : validBlock 67=true := by decide
private theorem block_68 : validBlock 68=true := by decide
private theorem block_69 : validBlock 69=true := by decide
private theorem block_70 : validBlock 70=true := by decide
private theorem block_71 : validBlock 71=true := by decide
private theorem block_72 : validBlock 72=true := by decide
private theorem block_73 : validBlock 73=true := by decide
private theorem block_74 : validBlock 74=true := by decide
private theorem block_75 : validBlock 75=true := by decide
private theorem block_76 : validBlock 76=true := by decide
private theorem block_77 : validBlock 77=true := by decide
private theorem block_78 : validBlock 78=true := by decide
private theorem block_79 : validBlock 79=true := by decide
private theorem block_80 : validBlock 80=true := by decide
private theorem block_81 : validBlock 81=true := by decide
private theorem block_82 : validBlock 82=true := by decide
private theorem block_83 : validBlock 83=true := by decide

theorem every_block (b : Fin 84) : validBlock b.val=true := by
  fin_cases b
  · exact block_0
  · exact block_1
  · exact block_2
  · exact block_3
  · exact block_4
  · exact block_5
  · exact block_6
  · exact block_7
  · exact block_8
  · exact block_9
  · exact block_10
  · exact block_11
  · exact block_12
  · exact block_13
  · exact block_14
  · exact block_15
  · exact block_16
  · exact block_17
  · exact block_18
  · exact block_19
  · exact block_20
  · exact block_21
  · exact block_22
  · exact block_23
  · exact block_24
  · exact block_25
  · exact block_26
  · exact block_27
  · exact block_28
  · exact block_29
  · exact block_30
  · exact block_31
  · exact block_32
  · exact block_33
  · exact block_34
  · exact block_35
  · exact block_36
  · exact block_37
  · exact block_38
  · exact block_39
  · exact block_40
  · exact block_41
  · exact block_42
  · exact block_43
  · exact block_44
  · exact block_45
  · exact block_46
  · exact block_47
  · exact block_48
  · exact block_49
  · exact block_50
  · exact block_51
  · exact block_52
  · exact block_53
  · exact block_54
  · exact block_55
  · exact block_56
  · exact block_57
  · exact block_58
  · exact block_59
  · exact block_60
  · exact block_61
  · exact block_62
  · exact block_63
  · exact block_64
  · exact block_65
  · exact block_66
  · exact block_67
  · exact block_68
  · exact block_69
  · exact block_70
  · exact block_71
  · exact block_72
  · exact block_73
  · exact block_74
  · exact block_75
  · exact block_76
  · exact block_77
  · exact block_78
  · exact block_79
  · exact block_80
  · exact block_81
  · exact block_82
  · exact block_83

theorem materialized_word (n : Nat) (lo : 761≤n) (hi : n<2680) :
    MaterializedArtifact.openingCode.get 32 ⟨n,hi⟩=(wordAt n).getD 0 := by
  let b : Fin 84:=⟨n/32,by omega⟩
  have e:=List.all_eq_true.mp (every_block b) (n%32) (List.mem_range.mpr (by omega))
  have same : 32*b.val+n%32=n := by dsimp [b];omega
  have inner : 761≤n ∧ n<2680 := ⟨lo,hi⟩
  simp only [same,dite_eq_left inner,beq_iff_eq] at e
  exact e

theorem actual_stitched : openingImage=stitched openingImage := by
  have him:=image_actual
  have nlen : openingImage.code.length=2680 := by
    rw [←him]
    simp only [MaterializedArtifact.submission,ArtifactEncoding.length_decode]
  have endLen : (stitched openingImage).code.length=2680 := by simp [stitched]
  have buf : openingImage.code=(stitched openingImage).code := by
    apply List.ext_getElem
    · exact nlen.trans endLen.symm
    · intro n ha hb
      have hi:=ha.trans_eq nlen
      have y:=stitched_get openingImage n hi
      rw [List.getElem?_eq_getElem hb,Option.some.injEq] at y
      rw [y,stitchedWord]
      split
      · rw [List.getElem?_eq_getElem ha];rfl
      · rename_i high
        have w:=materialized_word n (by omega) hi
        have dec:=ArtifactEncoding.getD_decode 32 MaterializedArtifact.openingCode n hi
        have hd : openingImage.code.getD n 0=(ArtifactEncoding.decode 32 MaterializedArtifact.openingCode).getD n 0 := by
          rw [←him];rfl
        rw [←w,←dec,←hd,List.getD_eq_getElem _ _ ha]
  exact congrArg₂ Image.mk buf rfl

#print axioms actual_stitched
end TwoPermutationPrototype.PhaseOpening
