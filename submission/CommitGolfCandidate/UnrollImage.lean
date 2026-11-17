import CommitGolfCandidate.UnrollLoop
import CommitGolfCandidate.Group341Image

/-! The sixty-four relocated bodies and their loop end are linked to the image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem unroll_slot_fetch (state : MachineState) (body slot : Nat)
    (bounded : body<64) (word : slot<33) (instruction : Instr)
    (pc : state.pc=BitVec.ofNat 64 (1011404+132*body+4*slot))
    (decoded : decodeInstruction (unrollBodyWord slot)=some (.base instruction)) :
    fetch (submission.image .commit) state=some (.base instruction) := by
  apply commit_fetch state (251827+33*body+slot) _ (by omega)
  · rw [pc]
    congr 1
    omega
  · change (group341ImageWords[251827+33*body+slot]?).bind decodeInstruction=_
    rw [unroll_body_word body slot bounded word]
    exact decoded

theorem unroll_image_body (body : Nat) (bounded : body<64) :
    UnrollBodyFetched (submission.image .commit) (1011404+132*body) := by
  refine ⟨?_,?_,?_⟩
  · intro state i hi pc
    apply unroll_slot_fetch state body i bounded (by omega) _ (by rw [pc]; congr 1)
    interval_cases i <;> rfl
  · intro state block hb
    refine ⟨?_,?_,?_⟩
    · intro pc
      apply unroll_slot_fetch state body (7+3*block) bounded (by omega) _
        (by rw [pc]; congr 1; omega)
      interval_cases block <;> rfl
    · intro pc
      apply unroll_slot_fetch state body (8+3*block) bounded (by omega) _
        (by rw [pc]; congr 1; omega)
      interval_cases block <;> rfl
    · intro pc
      apply unroll_slot_fetch state body (9+3*block) bounded (by omega) _
        (by rw [pc]; congr 1; omega)
      interval_cases block <;> rfl
  · intro state
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro pc
      exact unroll_slot_fetch state body 28 bounded (by decide) _ (by rw [pc]) rfl
    · intro pc
      exact unroll_slot_fetch state body 29 bounded (by decide) _ (by rw [pc]) rfl
    · intro pc
      exact unroll_slot_fetch state body 30 bounded (by decide) _ (by rw [pc]) rfl
    · intro pc
      exact unroll_slot_fetch state body 31 bounded (by decide) _ (by rw [pc]) rfl
    · intro pc
      exact unroll_slot_fetch state body 32 bounded (by decide) _ (by rw [pc]) rfl

theorem unroll_image_end : UnrollEndFetched (submission.image .commit) := by
  intro state
  refine ⟨?_,?_,?_⟩
  · intro pc
    apply commit_fetch state 253939 _ (by decide) pc
    change (group341ImageWords[253939]?).bind decodeInstruction=_
    rw [show 253939=253939+0 by decide,unroll_end_word 0 (by decide)]
    rfl
  · intro pc
    apply commit_fetch state 253940 _ (by decide) pc
    change (group341ImageWords[253940]?).bind decodeInstruction=_
    rw [show 253940=253939+1 by decide,unroll_end_word 1 (by decide)]
    rfl
  · intro pc
    apply commit_fetch state 253941 _ (by decide) pc
    change (group341ImageWords[253941]?).bind decodeInstruction=_
    rw [show 253941=253939+2 by decide,unroll_end_word 2 (by decide)]
    rfl

end CommitGolfCandidate
