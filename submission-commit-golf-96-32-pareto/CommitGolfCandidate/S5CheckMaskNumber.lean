import CommitGolfCandidate.S5MaskValue
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
theorem calc_mask (h : Height) :
    (1#64 <<< ((BitVec.ofNat 64 (wireWidth h)+signExtend12 3872).toNat%64))+signExtend12 4095=heldMask h := by
  have cases : ∀ k : Height,224≤wireWidth k ∧ wireWidth k≤256:=by decide +kernel
  have test : ∀ i : Fin 33,(1#64 <<< ((BitVec.ofNat 64 (224+i.val)+18446744073709551392#64).toNat%64))+18446744073709551615#64
      =BitVec.ofNat 64 (2^i.val-1) := by decide +kernel
  obtain ⟨lo,hi⟩:=cases h
  have e:=test ⟨wireWidth h-224,by omega⟩
  dsimp only at e
  rwa [Nat.add_sub_cancel' lo] at e

end CommitGolfCandidate.S5Machine.Check
