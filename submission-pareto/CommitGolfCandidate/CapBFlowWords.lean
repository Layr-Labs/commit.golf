import CommitGolfCandidate.CapBHandler
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.Opening (getReg_setReg getReg_setMem)
set_option maxRecDepth 12000
set_option maxHeartbeats 1100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem word661 : (openingImage.code[661]?).bind decodeInstruction=some (.base (.SLLI .x16 .x6 3)) := rfl
theorem word662 : (openingImage.code[662]?).bind decodeInstruction=some (.base (.ADD .x7 .x26 .x16)) := rfl
theorem word663 : (openingImage.code[663]?).bind decodeInstruction=some (.base (.LD .x28 .x7 0)) := rfl
theorem word664 : (openingImage.code[664]?).bind decodeInstruction=some (.base (.BEQ .x28 .x0 152)) := rfl
theorem word665 : (openingImage.code[665]?).bind decodeInstruction=some (.base (.BGEU .x16 .x27 172)) := rfl
theorem word666 : (openingImage.code[666]?).bind decodeInstruction=some (.base (.SLLI .x6 .x6 1)) := rfl
theorem word667 : (openingImage.code[667]?).bind decodeInstruction=some (.base (.JAL .x0 2097128)) := rfl
theorem word708 : (openingImage.code[708]?).bind decodeInstruction=some (.base (.JAL .x0 29936)) := rfl
theorem word8192 : (openingImage.code[8192]?).bind decodeInstruction=some (.base (.SLLI .x28 .x28 6)) := rfl
theorem word8193 : (openingImage.code[8193]?).bind decodeInstruction=some (.base (.LUI .x11 9)) := rfl
theorem word8194 : (openingImage.code[8194]?).bind decodeInstruction=some (.base (.ADD .x11 .x11 .x28)) := rfl
theorem word8195 : (openingImage.code[8195]?).bind decodeInstruction=some (.base (.JALR .x0 .x11 128)) := rfl
theorem word703 : (openingImage.code[703]?).bind decodeInstruction=some (.base (.ANDI .x7 .x6 1)) := rfl
theorem word704 : (openingImage.code[704]?).bind decodeInstruction=some (.base (.BEQ .x7 .x0 8016)) := rfl
theorem word660 : (openingImage.code[660]?).bind decodeInstruction=some (.base (.ADDI .x6 .x6 1)) := rfl
theorem word705 : (openingImage.code[705]?).bind decodeInstruction=some (.base (.SRLI .x6 .x6 1)) := rfl
theorem word706 : (openingImage.code[706]?).bind decodeInstruction=some (.base (.BNE .x6 .x23 8180)) := rfl
theorem word707 : (openingImage.code[707]?).bind decodeInstruction=some (.base (.JAL .x0 23796)) := rfl
theorem word7155 : (openingImage.code[7155]?).bind decodeInstruction=some (.base (.ADDI .x6 .x0 1)) := rfl
theorem word7156 : (openingImage.code[7156]?).bind decodeInstruction=some (.base (.LUI .x19 7)) := rfl
theorem word7157 : (openingImage.code[7157]?).bind decodeInstruction=some (.base (.ADDI .x24 .x19 0)) := rfl
theorem word7158 : (openingImage.code[7158]?).bind decodeInstruction=some (.base (.ANDI .x14 .x21 7)) := rfl
theorem word7159 : (openingImage.code[7159]?).bind decodeInstruction=some (.base (.BEQ .x14 .x0 12)) := rfl
theorem word7160 : (openingImage.code[7160]?).bind decodeInstruction=some (.base (.ADDI .x14 .x21 0)) := rfl
theorem word7161 : (openingImage.code[7161]?).bind decodeInstruction=some (.base (.LUI .x21 3)) := rfl
theorem word7162 : (openingImage.code[7162]?).bind decodeInstruction=some (.base (.JAL .x0 2071148)) := rfl
theorem word6656 : (openingImage.code[6656]?).bind decodeInstruction=some (.base (.BEQ .x19 .x24 24)) := rfl
theorem word6657 : (openingImage.code[6657]?).bind decodeInstruction=some (.base (.SUB .x6 .x19 .x24)) := rfl
theorem word6658 : (openingImage.code[6658]?).bind decodeInstruction=some (.base (.SRLI .x6 .x6 1)) := rfl
theorem word6659 : (openingImage.code[6659]?).bind decodeInstruction=some (.base (.LUI .x7 8)) := rfl
theorem word6660 : (openingImage.code[6660]?).bind decodeInstruction=some (.base (.ADD .x7 .x7 .x6)) := rfl
theorem word6661 : (openingImage.code[6661]?).bind decodeInstruction=some (.base (.JALR .x0 .x7 2144)) := rfl
theorem word6662 : (openingImage.code[6662]?).bind decodeInstruction=some (.base (.BEQ .x14 .x0 36)) := rfl
theorem word6663 : (openingImage.code[6663]?).bind decodeInstruction=some (.base (.LUI .x6 3)) := rfl
theorem word6664 : (openingImage.code[6664]?).bind decodeInstruction=some (.base (.BEQ .x6 .x21 24)) := rfl
theorem word6665 : (openingImage.code[6665]?).bind decodeInstruction=some (.base (.LBU .x7 .x6 0)) := rfl
theorem word6666 : (openingImage.code[6666]?).bind decodeInstruction=some (.base (.SB .x14 .x7 0)) := rfl
theorem word6667 : (openingImage.code[6667]?).bind decodeInstruction=some (.base (.ADDI .x6 .x6 1)) := rfl
theorem word6668 : (openingImage.code[6668]?).bind decodeInstruction=some (.base (.ADDI .x14 .x14 1)) := rfl
theorem word6669 : (openingImage.code[6669]?).bind decodeInstruction=some (.base (.BNE .x6 .x21 8176)) := rfl
theorem word6670 : (openingImage.code[6670]?).bind decodeInstruction=some (.base (.ADDI .x21 .x14 0)) := rfl
theorem word6671 : (openingImage.code[6671]?).bind decodeInstruction=some (.base (.JAL .x0 22596)) := rfl
theorem word709 : (openingImage.code[709]?).bind decodeInstruction=some (.base (.SUB .x11 .x21 .x20)) := rfl
theorem word710 : (openingImage.code[710]?).bind decodeInstruction=some (.base (.ADDI .x5 .x0 1)) := rfl
theorem word711 : (openingImage.code[711]?).bind decodeInstruction=some (.base (.ADDI .x10 .x0 0)) := rfl
end CommitGolfCandidate.CapB
