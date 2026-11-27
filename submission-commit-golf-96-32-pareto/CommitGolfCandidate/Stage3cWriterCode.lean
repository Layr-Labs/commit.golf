import CommitGolfCandidate.Stage3cTrace
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def fetchWord (partialWord : Bool) : PathCode := [(21,.BEQ .x11 .x0 80),(22,.LD .x28 .x10 0),
  (23,.ADDI .x10 .x10 8),(24,.ADDI .x31 .x0 64),(25,.BGEU .x11 .x31 8)] ++
  if partialWord then [(26,.ADDI .x31 .x11 0)] else []

def mix : PathCode := [(27,.SUB .x11 .x11 .x31),(28,.SLL .x29 .x28 .x24),(29,.OR .x23 .x23 .x29),
  (30,.ADD .x24 .x24 .x31),(31,.BLTU .x24 .x27 8152)]

def spill (exactFit : Bool) : PathCode := [(32,.SD .x19 .x23 0),(33,.ADDI .x19 .x19 8),
  (34,.ADDI .x24 .x24 4032),(35,.BEQ .x24 .x0 16)] ++
  if exactFit then [(39,.ADDI .x23 .x0 0),(40,.JAL .x0 2097076)]
  else [(36,.SUB .x30 .x31 .x24),(37,.SRL .x23 .x28 .x30),(38,.JAL .x0 2097084)]

def finish : PathCode := [(21,.BEQ .x11 .x0 80),(41,.JALR .x0 .x1 0)]

theorem fetch_sites (b : Bool) : (fetchWord b).all (matchesWord .opening) := by cases b <;> decide +kernel
theorem mix_sites : mix.all (matchesWord .opening) := by decide +kernel
theorem spill_sites (b : Bool) : (spill b).all (matchesWord .opening) := by cases b <;> decide +kernel
theorem finish_sites : finish.all (matchesWord .opening) := by decide +kernel

end CommitGolfCandidate.Chained.BinaryMachine.Writer
