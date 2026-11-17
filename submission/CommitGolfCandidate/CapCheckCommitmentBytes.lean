import CommitGolfCandidate.CapCheckLoadedRecords
import CommitGolfCandidate.BufferRefinement

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_input_commitment (input : CheckInput) :
    readBuffer (capProgram.initialState .check input)
      capProgram.layout.commitment 32=input.commitment := by
  have decoded := read_serialized_slice (capProgram.initialState .check input)
    input.commitment capProgram.layout.commitment 0 32 (by
      intro j inside
      rw [initial_input_byte capProgram .check input _ (by
        change 4294971392+j<2^64
        omega)]
      have selected : capProgram.layout.commitment≤capProgram.layout.commitment+j ∧
          capProgram.layout.commitment+j<capProgram.layout.commitment+(DIGEST_BITS+7)/8 := by
        change _≤_ ∧ _<capProgram.layout.commitment+32
        omega
      simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,
        selected,and_self,decide_true,Nat.add_sub_cancel_left,Nat.zero_add])
  exact decoded.trans BitVec.extractLsb'_eq_self

end CommitGolfCandidate
