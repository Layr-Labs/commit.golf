import CommitGolfCandidate.Compact.SlimLoop
import CommitGolfCandidate.Compact.FastOpeningBounds
/-! Transfer reference memory bounds to each path body and execute the final counter adjustment. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute openingPathState
theorem slim_full_path (s : MachineState) (pc : s.pc=4248)
    (heapBound : (s.getReg .x9).toNat+2^30≤MEMORY_BYTES)
    (heapAligned : (s.getReg .x9).toNat%8=0)
    (nodeBound : (s.getReg .x20).toNat<2^25)
    (outputBound : (s.getReg .x25).toNat+32*24≤MEMORY_BYTES)
    (outputAligned : (s.getReg .x25).toNat%8=0)
    (fuel : Nat) (coins : Bool) :
    execute slimImage (313+fuel) s coins=
      (do let result ← execute slimImage fuel
            ((openingPathState^[24] s).setPC 5500) coins
          return result.charge 313 0) := by
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
  have run := slim_path_loop 24 0 (by decide) s (s.getReg .x28) reads writes (1+fuel) coins
  have same : (s.setReg .x28 (s.getReg .x28)).setPC (BitVec.ofNat 64 (4248+52*0))=s := by
    rw [state_set_own_register]
    simp only [Nat.mul_zero,Nat.add_zero]
    change s.setPC (4248 : Word)=s
    rw [←pc]
    cases s
    rfl
  simp only [Function.iterate_zero,id_eq,Nat.zero_add] at run
  rw [same] at run
  have sameCounter : (openingPathState^[24] s).getReg .x28=s.getReg .x28-24 := path_counter_iterate 24 s
  generalize hd : (openingPathState^[24] s)=done at run sameCounter ⊢
  let before := (done.setReg .x28 (s.getReg .x28)).setPC 5496
  have fetched : fetch slimImage before=some (.base (.ADDI .x28 .x28 4072)) := by
    apply slim_fetch before 350 _ (by decide) rfl
    rfl
  have stepped : ordinaryStep before (.base (.ADDI .x28 .x28 4072))=
      some (done.setPC 5500) := counter_cleanup_step done (s.getReg .x28) sameCounter
  have last := execute_ordinary_step slimImage (.base (.ADDI .x28 .x28 4072)) before
    (done.setPC 5500) fuel coins fetched stepped
  change execute slimImage (fuel+1) before coins=_ at last
  have framed : execute slimImage (1+fuel)
      ((done.setReg .x28 (s.getReg .x28)).setPC
        (BitVec.ofNat 64 (4248+52*24))) coins=
      (do let result ← execute slimImage fuel (done.setPC 5500) coins
          return result.charge 1 0) := by
    simpa only [before,instructionCycles,BitVec.ofNat_eq_ofNat,show 4248+52*24=5496 by decide,show 1+fuel=fuel+1 by omega] using last
  rw [show 313+fuel=312+(1+fuel) by omega,run,framed]
  simp only [bind_assoc]
  apply bind_congr
  intro result
  simp [Execution.charge]
  omega
end CommitGolfCandidate.Compact
