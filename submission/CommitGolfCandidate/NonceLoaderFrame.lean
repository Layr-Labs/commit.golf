import CommitGolfCandidate.NonceExpandedInput
import CommitGolfCandidate.InputMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem nonce_loader_byte_frame (program : Submission) (input : CheckInput) (proof : Proof) (location : Nat)
    (outsideOld : ¬(program.layout.proof ≤ location ∧ location<program.layout.proof+input.proof.length))
    (outsideNew : ¬(program.layout.proof ≤ location ∧ location<program.layout.proof+proof.length)) :
    inputByte program .check {input with proof:=proof} location=inputByte program .check input location := by
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,positionsBuffer,valuesBuffer,
    outsideOld,outsideNew,decide_false,List.find?_nil]

theorem nonce_loader_word_frame (program : Submission) (input : CheckInput) (proof : Proof) (location : Nat)
    (bounded : location<2^64)
    (outsideOld : ∀ byte<8, ¬(program.layout.proof ≤ location+byte ∧
      location+byte<program.layout.proof+input.proof.length))
    (outsideNew : ∀ byte<8, ¬(program.layout.proof ≤ location+byte ∧
      location+byte<program.layout.proof+proof.length)) :
    (program.initialState .check {input with proof:=proof}).getMem (BitVec.ofNat 64 location)=
      (program.initialState .check input).getMem (BitVec.ofNat 64 location) := by
  have summed : (∑ byte ∈ Finset.range 8,
      (inputByte program .check {input with proof:=proof} (location+byte)).toNat*2^(8*byte))=
      (∑ byte ∈ Finset.range 8,
      (inputByte program .check input (location+byte)).toNat*2^(8*byte)) := by
    apply Finset.sum_congr rfl
    intro byte member
    rw [nonce_loader_byte_frame program input proof (location+byte)
      (outsideOld byte (Finset.mem_range.mp member)) (outsideNew byte (Finset.mem_range.mp member))]
  exact (initial_input_word program .check {input with proof:=proof} location bounded).trans
    ((congrArg (BitVec.ofNat 64) summed).trans (initial_input_word program .check input location bounded).symm)
end CommitGolfCandidate
