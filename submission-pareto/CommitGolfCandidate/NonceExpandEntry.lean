import CommitGolfCandidate.NonceCompressedFetch

/-! The prospective checker starts with the actual relative jump to its
expander. It preserves all ABI registers and memory and costs one step. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_expand_entry_execute (state : MachineState) (pc : state.pc=4096)
    (fuel : Nat) :
    execute nonceExpandedImage (1+fuel) state false=
      (do let result ← execute nonceExpandedImage fuel (state.setPC 4896) false
          return result.charge 1 0) := by
  have fetched : fetch nonceExpandedImage state=some (.base (.JAL .x0 800)) := by
    apply cap_image_fetch _ state 0 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 800))=some (state.setPC 4896) := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,execInstrBr,pc]
    rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step nonceExpandedImage _ state _ fuel false fetched stepped]
  rfl

end CommitGolfCandidate
