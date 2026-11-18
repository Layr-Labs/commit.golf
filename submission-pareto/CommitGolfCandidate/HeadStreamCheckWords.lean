import CommitGolfCandidate.HeadStreamCheckBase

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

@[simp] theorem word_0 : instrAt 0=.SRLI .x18 .x16 3 := rfl
@[simp] theorem word_1 : instrAt 1=.ADD .x17 .x17 .x18 := rfl
@[simp] theorem word_2 : instrAt 2=.ADDI .x19 .x0 498 := rfl
@[simp] theorem word_3 : instrAt 3=.SLLI .x19 .x19 22 := rfl
@[simp] theorem word_4 : instrAt 4=.ADDI .x19 .x19 1920 := rfl
@[simp] theorem word_5 : instrAt 5=.SLLI .x19 .x19 2 := rfl
@[simp] theorem word_6 : instrAt 6=.BLTU .x19 .x17 7432 := rfl
@[simp] theorem word_7 : instrAt 7=.ADDI .x18 .x0 481 := rfl
@[simp] theorem word_8 : instrAt 8=.MUL .x18 .x16 .x18 := rfl
@[simp] theorem word_9 : instrAt 9=.BLTU .x17 .x18 7420 := rfl
@[simp] theorem word_10 : instrAt 10=.SUB .x18 .x17 .x16 := rfl
@[simp] theorem word_11 : instrAt 11=.ADDI .x19 .x0 1 := rfl
@[simp] theorem word_12 : instrAt 12=.SLLI .x19 .x19 33 := rfl
@[simp] theorem word_13 : instrAt 13=.ADD .x19 .x15 .x19 := rfl
@[simp] theorem word_14 : instrAt 14=.ADD .x20 .x15 .x18 := rfl
@[simp] theorem word_15 : instrAt 15=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_16 : instrAt 16=.BEQ .x22 .x16 72 := rfl
@[simp] theorem word_17 : instrAt 17=.SLLI .x24 .x22 3 := rfl
@[simp] theorem word_18 : instrAt 18=.SUB .x24 .x24 .x22 := rfl
@[simp] theorem word_19 : instrAt 19=.SRLI .x25 .x24 3 := rfl
@[simp] theorem word_20 : instrAt 20=.ANDI .x26 .x24 7 := rfl
@[simp] theorem word_21 : instrAt 21=.ADD .x27 .x20 .x25 := rfl
@[simp] theorem word_22 : instrAt 22=.LBU .x28 .x27 0 := rfl
@[simp] theorem word_23 : instrAt 23=.LBU .x29 .x27 1 := rfl
@[simp] theorem word_24 : instrAt 24=.SRL .x28 .x28 .x26 := rfl
@[simp] theorem word_25 : instrAt 25=.ADDI .x30 .x0 256 := rfl
@[simp] theorem word_26 : instrAt 26=.SRL .x30 .x30 .x26 := rfl
@[simp] theorem word_27 : instrAt 27=.MUL .x29 .x29 .x30 := rfl
@[simp] theorem word_28 : instrAt 28=.OR .x28 .x28 .x29 := rfl
@[simp] theorem word_29 : instrAt 29=.ANDI .x28 .x28 127 := rfl
@[simp] theorem word_30 : instrAt 30=.ADD .x27 .x19 .x22 := rfl
@[simp] theorem word_31 : instrAt 31=.SB .x27 .x28 0 := rfl
@[simp] theorem word_32 : instrAt 32=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_33 : instrAt 33=.JAL .x0 2097084 := rfl
@[simp] theorem word_34 : instrAt 34=.ADDI .x25 .x0 480 := rfl
@[simp] theorem word_35 : instrAt 35=.ADDI .x22 .x18 0 := rfl
@[simp] theorem word_36 : instrAt 36=.BEQ .x22 .x0 48 := rfl
@[simp] theorem word_37 : instrAt 37=.ADDI .x22 .x22 4095 := rfl
@[simp] theorem word_38 : instrAt 38=.ADDI .x23 .x22 435 := rfl
@[simp] theorem word_39 : instrAt 39=.DIVU .x23 .x23 .x25 := rfl
@[simp] theorem word_40 : instrAt 40=.BLTU .x23 .x16 8 := rfl
@[simp] theorem word_41 : instrAt 41=.ADDI .x23 .x16 0 := rfl
@[simp] theorem word_42 : instrAt 42=.ADD .x23 .x23 .x22 := rfl
@[simp] theorem word_43 : instrAt 43=.ADD .x24 .x15 .x22 := rfl
@[simp] theorem word_44 : instrAt 44=.LBU .x28 .x24 0 := rfl
@[simp] theorem word_45 : instrAt 45=.ADD .x23 .x15 .x23 := rfl
@[simp] theorem word_46 : instrAt 46=.SB .x23 .x28 0 := rfl
@[simp] theorem word_47 : instrAt 47=.JAL .x0 2097108 := rfl
@[simp] theorem word_48 : instrAt 48=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_49 : instrAt 49=.ADDI .x21 .x15 45 := rfl
@[simp] theorem word_50 : instrAt 50=.BEQ .x22 .x16 32 := rfl
@[simp] theorem word_51 : instrAt 51=.ADD .x27 .x19 .x22 := rfl
@[simp] theorem word_52 : instrAt 52=.LBU .x28 .x27 0 := rfl
@[simp] theorem word_53 : instrAt 53=.SB .x21 .x28 0 := rfl
@[simp] theorem word_54 : instrAt 54=.SB .x27 .x0 0 := rfl
@[simp] theorem word_55 : instrAt 55=.ADDI .x21 .x21 481 := rfl
@[simp] theorem word_56 : instrAt 56=.ADDI .x22 .x22 1 := rfl
@[simp] theorem word_57 : instrAt 57=.JAL .x0 2097124 := rfl
@[simp] theorem word_58 : instrAt 58=.ADDI .x18 .x0 0 := rfl
@[simp] theorem word_59 : instrAt 59=.ADDI .x19 .x0 0 := rfl
@[simp] theorem word_60 : instrAt 60=.ADDI .x20 .x0 0 := rfl
@[simp] theorem word_61 : instrAt 61=.ADDI .x21 .x0 0 := rfl
@[simp] theorem word_62 : instrAt 62=.ADDI .x22 .x0 0 := rfl
@[simp] theorem word_63 : instrAt 63=.ADDI .x23 .x0 0 := rfl
@[simp] theorem word_64 : instrAt 64=.ADDI .x24 .x0 0 := rfl
@[simp] theorem word_65 : instrAt 65=.ADDI .x25 .x0 0 := rfl
@[simp] theorem word_66 : instrAt 66=.ADDI .x26 .x0 0 := rfl
@[simp] theorem word_67 : instrAt 67=.ADDI .x27 .x0 0 := rfl
@[simp] theorem word_68 : instrAt 68=.ADDI .x28 .x0 0 := rfl
@[simp] theorem word_69 : instrAt 69=.ADDI .x29 .x0 0 := rfl
@[simp] theorem word_70 : instrAt 70=.ADDI .x30 .x0 0 := rfl
@[simp] theorem word_71 : instrAt 71=.ADDI .x31 .x0 0 := rfl
@[simp] theorem word_72 : instrAt 72=.JAL .x0 2096180 := rfl

end TwoPermutationPrototype.Packed.Checker.HeadRestore
