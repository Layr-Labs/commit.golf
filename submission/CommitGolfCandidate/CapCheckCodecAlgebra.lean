import CommitGolfCandidate.CapCheckCodecSteps

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false

theorem cap_check_then_passed (head : MachineState × Bool)
    (tail : MachineState → MachineState × Bool) (passed : head.2=true) :
    capCheckValueThen head tail=tail head.1 := by
  simp only [capCheckValueThen,passed,↓reduceIte]

theorem cap_check_then_rejected (head : MachineState × Bool)
    (tail : MachineState → MachineState × Bool) (failed : head.2=false) :
    capCheckValueThen head tail=head := by
  simp only [capCheckValueThen,failed,Bool.false_eq_true,↓reduceIte]

theorem cap_decode_node_known (compress : Compression) {height : Nat}
    (left right : CapView height) (words : List Digest)
    (present : capOccupied (.node left right)=true) :
    capDecode compress (.node left right) words=
      (do let (leftRoot,rest) ← capDecode compress left words
          let (rightRoot,rest') ← capDecode compress right rest
          return (combine compress leftRoot rightRoot,rest')) := by
  simp only [capDecode,present,↓reduceIte]

end CommitGolfCandidate
