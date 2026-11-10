import CommitGolfCandidate.Compact.NoInitLoop
import CommitGolfCandidate.Compact.FastOpeningBounds
/-! Reference memory bounds and path execution with the counter fixed at zero; the reference counter also reaches zero after twenty-four levels. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute openingPathState
theorem noInit_full_path (s : MachineState) (pc : s.pc=4248) (counter : s.getReg .x28=24)
    (heapBound : (s.getReg .x9).toNat+2^30≤MEMORY_BYTES)
    (heapAligned : (s.getReg .x9).toNat%8=0)
    (nodeBound : (s.getReg .x20).toNat<2^25)
    (outputBound : (s.getReg .x25).toNat+32*24≤MEMORY_BYTES)
    (outputAligned : (s.getReg .x25).toNat%8=0)
    (fuel : Nat) (coins : Bool) :
    execute noInitImage (312+fuel) (s.setReg .x28 0) coins=
      (do let result ← execute noInitImage fuel
            ((openingPathState^[24] s).setPC 5496) coins
          return result.charge 312 0) := by
  have reads : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] s).getReg .x9+
       (((openingPathState^[level] s).getReg .x20 ^^^ 1)<<<5)+
       BitVec.ofNat 64 (8*word.val)) 8=true := by
    intro level inside word
    apply opening_sibling_access
    · simpa only [fast_path_heap] using heapBound
    · simpa only [fast_path_heap] using heapAligned
    · exact fast_path_node_bound level s nodeBound
  have writes : ∀ level<24, ∀ word : Fin 4, accessValid
      ((openingPathState^[level] s).getReg .x25+
       BitVec.ofNat 64 (8*word.val)) 8=true := by
    intro level inside word
    have address : ((openingPathState^[level] s).getReg .x25).toNat=
        (s.getReg .x25).toNat+32*level := by
      rw [opening_path_output,BitVec.toNat_add,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 32*level<2^64),Nat.mod_eq_of_lt]
      simp only [MEMORY_BYTES] at outputBound
      omega
    apply opening_digest_access_valid
    · rw [address];omega
    · rw [address];omega
  have run := noInit_path_loop 24 0 (by decide) s 0 reads writes fuel coins
  have same : (s.setReg .x28 0).setPC (BitVec.ofNat 64 (4248+52*0))=s.setReg .x28 0 := by
    simp only [Nat.mul_zero,Nat.add_zero]
    change (s.setReg .x28 0).setPC (4248 : Word)=_
    rw [←pc]
    cases s
    rfl
  simp only [Function.iterate_zero,id_eq,Nat.zero_add] at run
  rw [same] at run
  have sameCounter : (openingPathState^[24] s).getReg .x28=0 := by
    rw [path_counter_iterate,counter]
    decide
  have unchanged : (openingPathState^[24] s).setReg .x28 0=openingPathState^[24] s := by
    rw [←sameCounter,state_set_own_register]
  rw [unchanged] at run
  simpa only [show (13*24:Nat)=312 by decide,show (4248+52*24:Nat)=5496 by decide,
    BitVec.ofNat_eq_ofNat] using run
end CommitGolfCandidate.Compact
