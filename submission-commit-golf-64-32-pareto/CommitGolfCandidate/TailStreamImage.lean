import CommitGolfCandidate.TailStreamExec

namespace TwoPermutationPrototype.PackedOpening.TailStream
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

theorem code_matches (i : Fin 101) : Pack.packCode.getD (241+i.val) .NOP=instrAt i.val := by
  obtain ⟨i,hi⟩ := i
  interval_cases i <;> rfl

instance deliveredCode : CodeImage openingImage where
  fetched s i hi pc := by
    have fetched := Pack.fetch_pack s (241+i) (by omega) pc
    rw [code_matches ⟨i,hi⟩] at fetched
    exact fetched

end TwoPermutationPrototype.PackedOpening.TailStream
