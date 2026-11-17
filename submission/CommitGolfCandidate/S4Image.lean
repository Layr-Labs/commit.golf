import CommitGolfCandidate.S3Image
import CommitGolfCandidate.UnrollShift

/-! A 512-leaf physical block for the two-permutation leaf phase. Word 54 jumps to word
252776 (PC 1015200): the five stage-3 entry words and two bias words, then four identical
128-leaf windows (PC 1015228 + 7184w, two 64-leaf halves of fourteen-word leaves followed by
four rebase words), then five block-end words (PC 1043964). Inside a half, x18/x23 stay
displaced from the reference group pointers by fixed lags, absorbed by the immediates. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def s4LeafMidInstructions (h u : Nat) : List Instr :=
  [.LD .x6 .x18 (BitVec.ofInt 12 (24 * (u : Int) + 1536 * h - 1536)), .SD .x10 .x6 72,
   .LD .x6 .x18 (BitVec.ofInt 12 (24 * (u : Int) + 1536 * h - 1528)), .SD .x10 .x6 80,
   .LD .x6 .x18 (BitVec.ofInt 12 (24 * (u : Int) + 1536 * h - 1520)), .SD .x10 .x6 88,
   .ADDI .x10 .x10 72, .ADDI .x12 .x23 (BitVec.ofInt 12 (32 * (u : Int) + 2048 * h - 2048))]

/-- Leaf `u` of half `h` of a window. -/
def s4LeafCode (h u : Nat) : List Instr :=
  s3LeafHeadInstructions ++ [.ECALL] ++ s4LeafMidInstructions h u ++ [.ECALL, .ADDI .x10 .x10 184]

def s4RebaseInstructions : List Instr :=
  [.ADDI .x18 .x18 1536, .ADDI .x18 .x18 1536, .ADD .x23 .x23 .x7, .ADD .x23 .x23 .x7]

def s4BiasInstructions : List Instr := [.ADDI .x18 .x18 1536, .ADD .x23 .x23 .x7]

def s4EndInstructions : List Instr :=
  [.BGEU .x23 .x22 8, .JAL .x0 2068412, .ADDI .x18 .x18 (-1536), .ADDI .x23 .x23 (-2048),
   .JAL .x0 2068192]

theorem s4_leaf_decoded_0_0 (i : Nat) (hi : i < 14) :
    (s4WindowWords[0 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 0)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_1 (i : Nat) (hi : i < 14) :
    (s4WindowWords[14 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 1)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_2 (i : Nat) (hi : i < 14) :
    (s4WindowWords[28 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 2)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_3 (i : Nat) (hi : i < 14) :
    (s4WindowWords[42 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 3)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_4 (i : Nat) (hi : i < 14) :
    (s4WindowWords[56 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 4)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_5 (i : Nat) (hi : i < 14) :
    (s4WindowWords[70 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 5)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_6 (i : Nat) (hi : i < 14) :
    (s4WindowWords[84 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 6)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_7 (i : Nat) (hi : i < 14) :
    (s4WindowWords[98 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 7)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_8 (i : Nat) (hi : i < 14) :
    (s4WindowWords[112 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 8)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_9 (i : Nat) (hi : i < 14) :
    (s4WindowWords[126 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 9)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_10 (i : Nat) (hi : i < 14) :
    (s4WindowWords[140 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 10)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_11 (i : Nat) (hi : i < 14) :
    (s4WindowWords[154 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 11)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_12 (i : Nat) (hi : i < 14) :
    (s4WindowWords[168 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 12)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_13 (i : Nat) (hi : i < 14) :
    (s4WindowWords[182 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 13)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_14 (i : Nat) (hi : i < 14) :
    (s4WindowWords[196 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 14)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_15 (i : Nat) (hi : i < 14) :
    (s4WindowWords[210 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 15)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_16 (i : Nat) (hi : i < 14) :
    (s4WindowWords[224 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 16)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_17 (i : Nat) (hi : i < 14) :
    (s4WindowWords[238 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 17)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_18 (i : Nat) (hi : i < 14) :
    (s4WindowWords[252 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 18)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_19 (i : Nat) (hi : i < 14) :
    (s4WindowWords[266 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 19)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_20 (i : Nat) (hi : i < 14) :
    (s4WindowWords[280 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 20)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_21 (i : Nat) (hi : i < 14) :
    (s4WindowWords[294 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 21)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_22 (i : Nat) (hi : i < 14) :
    (s4WindowWords[308 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 22)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_23 (i : Nat) (hi : i < 14) :
    (s4WindowWords[322 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 23)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_24 (i : Nat) (hi : i < 14) :
    (s4WindowWords[336 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 24)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_25 (i : Nat) (hi : i < 14) :
    (s4WindowWords[350 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 25)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_26 (i : Nat) (hi : i < 14) :
    (s4WindowWords[364 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 26)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_27 (i : Nat) (hi : i < 14) :
    (s4WindowWords[378 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 27)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_28 (i : Nat) (hi : i < 14) :
    (s4WindowWords[392 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 28)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_29 (i : Nat) (hi : i < 14) :
    (s4WindowWords[406 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 29)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_30 (i : Nat) (hi : i < 14) :
    (s4WindowWords[420 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 30)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_31 (i : Nat) (hi : i < 14) :
    (s4WindowWords[434 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 31)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_32 (i : Nat) (hi : i < 14) :
    (s4WindowWords[448 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 32)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_33 (i : Nat) (hi : i < 14) :
    (s4WindowWords[462 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 33)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_34 (i : Nat) (hi : i < 14) :
    (s4WindowWords[476 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 34)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_35 (i : Nat) (hi : i < 14) :
    (s4WindowWords[490 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 35)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_36 (i : Nat) (hi : i < 14) :
    (s4WindowWords[504 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 36)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_37 (i : Nat) (hi : i < 14) :
    (s4WindowWords[518 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 37)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_38 (i : Nat) (hi : i < 14) :
    (s4WindowWords[532 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 38)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_39 (i : Nat) (hi : i < 14) :
    (s4WindowWords[546 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 39)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_40 (i : Nat) (hi : i < 14) :
    (s4WindowWords[560 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 40)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_41 (i : Nat) (hi : i < 14) :
    (s4WindowWords[574 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 41)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_42 (i : Nat) (hi : i < 14) :
    (s4WindowWords[588 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 42)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_43 (i : Nat) (hi : i < 14) :
    (s4WindowWords[602 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 43)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_44 (i : Nat) (hi : i < 14) :
    (s4WindowWords[616 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 44)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_45 (i : Nat) (hi : i < 14) :
    (s4WindowWords[630 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 45)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_46 (i : Nat) (hi : i < 14) :
    (s4WindowWords[644 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 46)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_47 (i : Nat) (hi : i < 14) :
    (s4WindowWords[658 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 47)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_48 (i : Nat) (hi : i < 14) :
    (s4WindowWords[672 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 48)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_49 (i : Nat) (hi : i < 14) :
    (s4WindowWords[686 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 49)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_50 (i : Nat) (hi : i < 14) :
    (s4WindowWords[700 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 50)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_51 (i : Nat) (hi : i < 14) :
    (s4WindowWords[714 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 51)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_52 (i : Nat) (hi : i < 14) :
    (s4WindowWords[728 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 52)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_53 (i : Nat) (hi : i < 14) :
    (s4WindowWords[742 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 53)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_54 (i : Nat) (hi : i < 14) :
    (s4WindowWords[756 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 54)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_55 (i : Nat) (hi : i < 14) :
    (s4WindowWords[770 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 55)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_56 (i : Nat) (hi : i < 14) :
    (s4WindowWords[784 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 56)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_57 (i : Nat) (hi : i < 14) :
    (s4WindowWords[798 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 57)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_58 (i : Nat) (hi : i < 14) :
    (s4WindowWords[812 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 58)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_59 (i : Nat) (hi : i < 14) :
    (s4WindowWords[826 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 59)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_60 (i : Nat) (hi : i < 14) :
    (s4WindowWords[840 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 60)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_61 (i : Nat) (hi : i < 14) :
    (s4WindowWords[854 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 61)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_62 (i : Nat) (hi : i < 14) :
    (s4WindowWords[868 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 62)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_0_63 (i : Nat) (hi : i < 14) :
    (s4WindowWords[882 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 0 63)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_0 (i : Nat) (hi : i < 14) :
    (s4WindowWords[896 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 0)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_1 (i : Nat) (hi : i < 14) :
    (s4WindowWords[910 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 1)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_2 (i : Nat) (hi : i < 14) :
    (s4WindowWords[924 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 2)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_3 (i : Nat) (hi : i < 14) :
    (s4WindowWords[938 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 3)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_4 (i : Nat) (hi : i < 14) :
    (s4WindowWords[952 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 4)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_5 (i : Nat) (hi : i < 14) :
    (s4WindowWords[966 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 5)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_6 (i : Nat) (hi : i < 14) :
    (s4WindowWords[980 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 6)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_7 (i : Nat) (hi : i < 14) :
    (s4WindowWords[994 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 7)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_8 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1008 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 8)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_9 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1022 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 9)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_10 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1036 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 10)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_11 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1050 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 11)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_12 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1064 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 12)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_13 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1078 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 13)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_14 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1092 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 14)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_15 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1106 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 15)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_16 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1120 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 16)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_17 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1134 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 17)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_18 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1148 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 18)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_19 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1162 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 19)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_20 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1176 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 20)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_21 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1190 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 21)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_22 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1204 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 22)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_23 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1218 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 23)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_24 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1232 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 24)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_25 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1246 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 25)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_26 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1260 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 26)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_27 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1274 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 27)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_28 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1288 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 28)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_29 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1302 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 29)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_30 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1316 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 30)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_31 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1330 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 31)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_32 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1344 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 32)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_33 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1358 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 33)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_34 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1372 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 34)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_35 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1386 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 35)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_36 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1400 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 36)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_37 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1414 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 37)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_38 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1428 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 38)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_39 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1442 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 39)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_40 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1456 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 40)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_41 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1470 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 41)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_42 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1484 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 42)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_43 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1498 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 43)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_44 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1512 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 44)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_45 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1526 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 45)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_46 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1540 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 46)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_47 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1554 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 47)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_48 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1568 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 48)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_49 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1582 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 49)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_50 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1596 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 50)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_51 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1610 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 51)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_52 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1624 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 52)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_53 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1638 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 53)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_54 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1652 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 54)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_55 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1666 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 55)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_56 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1680 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 56)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_57 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1694 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 57)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_58 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1708 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 58)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_59 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1722 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 59)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_60 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1736 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 60)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_61 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1750 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 61)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_62 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1764 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 62)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_leaf_decoded_1_63 (i : Nat) (hi : i < 14) :
    (s4WindowWords[1778 + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode 1 63)[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl

theorem s4_half_decoded (h u i : Nat) (hh : h < 2) (hu : u < 64) (hi : i < 14) :
    (s4WindowWords[896 * h + 14 * u + i]?).bind decodeInstruction =
      some (.base (((s4LeafCode h u)[i]?).getD .EBREAK)) := by
  interval_cases h
  · interval_cases u
    · exact s4_leaf_decoded_0_0 i hi
    · exact s4_leaf_decoded_0_1 i hi
    · exact s4_leaf_decoded_0_2 i hi
    · exact s4_leaf_decoded_0_3 i hi
    · exact s4_leaf_decoded_0_4 i hi
    · exact s4_leaf_decoded_0_5 i hi
    · exact s4_leaf_decoded_0_6 i hi
    · exact s4_leaf_decoded_0_7 i hi
    · exact s4_leaf_decoded_0_8 i hi
    · exact s4_leaf_decoded_0_9 i hi
    · exact s4_leaf_decoded_0_10 i hi
    · exact s4_leaf_decoded_0_11 i hi
    · exact s4_leaf_decoded_0_12 i hi
    · exact s4_leaf_decoded_0_13 i hi
    · exact s4_leaf_decoded_0_14 i hi
    · exact s4_leaf_decoded_0_15 i hi
    · exact s4_leaf_decoded_0_16 i hi
    · exact s4_leaf_decoded_0_17 i hi
    · exact s4_leaf_decoded_0_18 i hi
    · exact s4_leaf_decoded_0_19 i hi
    · exact s4_leaf_decoded_0_20 i hi
    · exact s4_leaf_decoded_0_21 i hi
    · exact s4_leaf_decoded_0_22 i hi
    · exact s4_leaf_decoded_0_23 i hi
    · exact s4_leaf_decoded_0_24 i hi
    · exact s4_leaf_decoded_0_25 i hi
    · exact s4_leaf_decoded_0_26 i hi
    · exact s4_leaf_decoded_0_27 i hi
    · exact s4_leaf_decoded_0_28 i hi
    · exact s4_leaf_decoded_0_29 i hi
    · exact s4_leaf_decoded_0_30 i hi
    · exact s4_leaf_decoded_0_31 i hi
    · exact s4_leaf_decoded_0_32 i hi
    · exact s4_leaf_decoded_0_33 i hi
    · exact s4_leaf_decoded_0_34 i hi
    · exact s4_leaf_decoded_0_35 i hi
    · exact s4_leaf_decoded_0_36 i hi
    · exact s4_leaf_decoded_0_37 i hi
    · exact s4_leaf_decoded_0_38 i hi
    · exact s4_leaf_decoded_0_39 i hi
    · exact s4_leaf_decoded_0_40 i hi
    · exact s4_leaf_decoded_0_41 i hi
    · exact s4_leaf_decoded_0_42 i hi
    · exact s4_leaf_decoded_0_43 i hi
    · exact s4_leaf_decoded_0_44 i hi
    · exact s4_leaf_decoded_0_45 i hi
    · exact s4_leaf_decoded_0_46 i hi
    · exact s4_leaf_decoded_0_47 i hi
    · exact s4_leaf_decoded_0_48 i hi
    · exact s4_leaf_decoded_0_49 i hi
    · exact s4_leaf_decoded_0_50 i hi
    · exact s4_leaf_decoded_0_51 i hi
    · exact s4_leaf_decoded_0_52 i hi
    · exact s4_leaf_decoded_0_53 i hi
    · exact s4_leaf_decoded_0_54 i hi
    · exact s4_leaf_decoded_0_55 i hi
    · exact s4_leaf_decoded_0_56 i hi
    · exact s4_leaf_decoded_0_57 i hi
    · exact s4_leaf_decoded_0_58 i hi
    · exact s4_leaf_decoded_0_59 i hi
    · exact s4_leaf_decoded_0_60 i hi
    · exact s4_leaf_decoded_0_61 i hi
    · exact s4_leaf_decoded_0_62 i hi
    · exact s4_leaf_decoded_0_63 i hi
  · interval_cases u
    · exact s4_leaf_decoded_1_0 i hi
    · exact s4_leaf_decoded_1_1 i hi
    · exact s4_leaf_decoded_1_2 i hi
    · exact s4_leaf_decoded_1_3 i hi
    · exact s4_leaf_decoded_1_4 i hi
    · exact s4_leaf_decoded_1_5 i hi
    · exact s4_leaf_decoded_1_6 i hi
    · exact s4_leaf_decoded_1_7 i hi
    · exact s4_leaf_decoded_1_8 i hi
    · exact s4_leaf_decoded_1_9 i hi
    · exact s4_leaf_decoded_1_10 i hi
    · exact s4_leaf_decoded_1_11 i hi
    · exact s4_leaf_decoded_1_12 i hi
    · exact s4_leaf_decoded_1_13 i hi
    · exact s4_leaf_decoded_1_14 i hi
    · exact s4_leaf_decoded_1_15 i hi
    · exact s4_leaf_decoded_1_16 i hi
    · exact s4_leaf_decoded_1_17 i hi
    · exact s4_leaf_decoded_1_18 i hi
    · exact s4_leaf_decoded_1_19 i hi
    · exact s4_leaf_decoded_1_20 i hi
    · exact s4_leaf_decoded_1_21 i hi
    · exact s4_leaf_decoded_1_22 i hi
    · exact s4_leaf_decoded_1_23 i hi
    · exact s4_leaf_decoded_1_24 i hi
    · exact s4_leaf_decoded_1_25 i hi
    · exact s4_leaf_decoded_1_26 i hi
    · exact s4_leaf_decoded_1_27 i hi
    · exact s4_leaf_decoded_1_28 i hi
    · exact s4_leaf_decoded_1_29 i hi
    · exact s4_leaf_decoded_1_30 i hi
    · exact s4_leaf_decoded_1_31 i hi
    · exact s4_leaf_decoded_1_32 i hi
    · exact s4_leaf_decoded_1_33 i hi
    · exact s4_leaf_decoded_1_34 i hi
    · exact s4_leaf_decoded_1_35 i hi
    · exact s4_leaf_decoded_1_36 i hi
    · exact s4_leaf_decoded_1_37 i hi
    · exact s4_leaf_decoded_1_38 i hi
    · exact s4_leaf_decoded_1_39 i hi
    · exact s4_leaf_decoded_1_40 i hi
    · exact s4_leaf_decoded_1_41 i hi
    · exact s4_leaf_decoded_1_42 i hi
    · exact s4_leaf_decoded_1_43 i hi
    · exact s4_leaf_decoded_1_44 i hi
    · exact s4_leaf_decoded_1_45 i hi
    · exact s4_leaf_decoded_1_46 i hi
    · exact s4_leaf_decoded_1_47 i hi
    · exact s4_leaf_decoded_1_48 i hi
    · exact s4_leaf_decoded_1_49 i hi
    · exact s4_leaf_decoded_1_50 i hi
    · exact s4_leaf_decoded_1_51 i hi
    · exact s4_leaf_decoded_1_52 i hi
    · exact s4_leaf_decoded_1_53 i hi
    · exact s4_leaf_decoded_1_54 i hi
    · exact s4_leaf_decoded_1_55 i hi
    · exact s4_leaf_decoded_1_56 i hi
    · exact s4_leaf_decoded_1_57 i hi
    · exact s4_leaf_decoded_1_58 i hi
    · exact s4_leaf_decoded_1_59 i hi
    · exact s4_leaf_decoded_1_60 i hi
    · exact s4_leaf_decoded_1_61 i hi
    · exact s4_leaf_decoded_1_62 i hi
    · exact s4_leaf_decoded_1_63 i hi

theorem s4_rebase_decoded (k : Nat) (hk : k < 4) :
    (s4WindowWords[1792 + k]?).bind decodeInstruction =
      some (.base ((s4RebaseInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s4_entry_decoded (k : Nat) (hk : k < 7) :
    (s4EntryWords[k]?).bind decodeInstruction =
      some (.base (((s3EntryInstructions ++ s4BiasInstructions)[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s4_end_decoded (k : Nat) (hk : k < 5) :
    (s4EndWords[k]?).bind decodeInstruction =
      some (.base ((s4EndInstructions[k]?).getD .EBREAK)) := by
  interval_cases k <;> rfl

theorem s4_entry_word (k : Nat) (hk : k < 7) :
    s3AppendedWords[949 + k]? = s4EntryWords[k]? := by
  unfold s3AppendedWords
  rw [List.getElem?_append_right (by rw [s3_base_length]; omega), s3_base_length,
    show 949 + k - 949 = k by omega, List.getElem?_append_left (by rw [show s4EntryWords.length = 7 from rfl]; omega)]

theorem s4_window_word (w j : Nat) (hw : w < 4) (hj : j < 1796) :
    s3AppendedWords[956 + 1796 * w + j]? = s4WindowWords[j]? := by
  unfold s3AppendedWords
  rw [List.getElem?_append_right (by rw [s3_base_length]; omega), s3_base_length,
    List.getElem?_append_right (by rw [show s4EntryWords.length = 7 from rfl]; omega),
    show s4EntryWords.length = 7 from rfl]
  interval_cases w
  · rw [List.getElem?_append_left (by rw [s4_window_length]; omega)]
    congr 1; omega
  · rw [List.getElem?_append_right (by rw [s4_window_length]; omega), s4_window_length,
      List.getElem?_append_left (by rw [s4_window_length]; omega)]
    congr 1; omega
  · rw [List.getElem?_append_right (by rw [s4_window_length]; omega), s4_window_length,
      List.getElem?_append_right (by rw [s4_window_length]; omega), s4_window_length,
      List.getElem?_append_left (by rw [s4_window_length]; omega)]
    congr 1; omega
  · rw [List.getElem?_append_right (by rw [s4_window_length]; omega), s4_window_length,
      List.getElem?_append_right (by rw [s4_window_length]; omega), s4_window_length,
      List.getElem?_append_right (by rw [s4_window_length]; omega), s4_window_length,
      List.getElem?_append_left (by rw [s4_window_length]; omega)]
    congr 1; omega

theorem s4_end_word (k : Nat) (hk : k < 5) :
    s3AppendedWords[8140 + k]? = s4EndWords[k]? := by
  unfold s3AppendedWords
  rw [List.getElem?_append_right (by rw [s3_base_length]; omega), s3_base_length,
    List.getElem?_append_right (by rw [show s4EntryWords.length = 7 from rfl]; omega),
    show s4EntryWords.length = 7 from rfl]
  repeat rw [List.getElem?_append_right (by rw [s4_window_length]; omega), s4_window_length]
  congr 1; omega

theorem s4_image_window (w j : Nat) (hw : w < 4) (hj : j < 1796) (instruction : Instr)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (1015228 + 7184 * w + 4 * j))
    (decoded : (s4WindowWords[j]?).bind decodeInstruction = some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  apply s3_image_word (956 + 1796 * w + j) _ state (by omega)
  · rw [pc]; congr 1; omega
  · rw [s4_window_word w j hw hj]; exact decoded

theorem s4_image_entry (k : Nat) (hk : k < 7) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1015200 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base (((s3EntryInstructions ++ s4BiasInstructions)[k]?).getD .EBREAK)) := by
  apply s3_image_word (949 + k) _ state (by omega)
  · rw [pc]; congr 1; omega
  · rw [s4_entry_word k hk]; exact s4_entry_decoded k hk

theorem s4_image_end (k : Nat) (hk : k < 5) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1043964 + 4 * k)) :
    fetch (submission.image .commit) state =
      some (.base ((s4EndInstructions[k]?).getD .EBREAK)) := by
  apply s3_image_word (8140 + k) _ state (by omega)
  · rw [pc]; congr 1; omega
  · rw [s4_end_word k hk]; exact s4_end_decoded k hk

end CommitGolfCandidate
