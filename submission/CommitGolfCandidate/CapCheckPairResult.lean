import CommitGolfCandidate.CapCheckWordSuffix

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option autoImplicit false

theorem cap_check_pair_result (limit : Nat) (marked : Nat → Bool)
    (node : Nat) (result : MachineState × Bool) (next : MachineState)
    (cursor : Nat) (words : List Digest) (tailBytes : Nat) (digest : Digest)
    (equal : result=(next,true))
    (root : capReadRoot next node=digest)
    (suffix : CapCheckWordSuffix next cursor words tailBytes)
    (ready : CapCheckDfsReady limit marked (.advance node) next) :
    result.2=true ∧ capReadRoot result.1 node=digest ∧
      CapCheckWordSuffix result.1 cursor words tailBytes ∧
      CapCheckDfsReady limit marked (.advance node) result.1 := by
  rw [equal]
  exact ⟨rfl,root,suffix,ready⟩

end CommitGolfCandidate
