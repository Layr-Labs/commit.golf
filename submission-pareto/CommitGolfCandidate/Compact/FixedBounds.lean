import CommitGolfCandidate.Compact.FixedLoop
import CommitGolfCandidate.Compact.FastOpeningBounds
/-! Transfer reference memory bounds to the path with its physical PC reset to 4232. The counter remains zero and the reference counter reaches zero. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute openingPathState
theorem fixed_full_path (s : MachineState) (counter : s.getReg .x28=24)
    (heapBound : (s.getReg .x9).toNat+2^30≤MEMORY_BYTES)
    (heapAligned : (s.getReg .x9).toNat%8=0)
    (nodeBound : (s.getReg .x20).toNat<2^25)
    (outputBound : (s.getReg .x25).toNat+32*24≤MEMORY_BYTES)
    (outputAligned : (s.getReg .x25).toNat%8=0)
    (fuel : Nat) (coins : Bool) :
    execute fixedImage (289+fuel) ((s.setReg .x28 0).setPC 4232) coins=
      (do let result ← execute fixedImage fuel
            ((openingPathState^[24] s).setPC 5388) coins
          return result.charge 289 0) := by
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
  have run := fixed_path_loop 24 0 (by decide) s 0 reads writes (1+fuel) coins
  simp only [Function.iterate_zero,id_eq,Nat.zero_add] at run
  have initial : fixedFrame s (s.getReg .x25) 0 4232=(s.setReg .x28 0).setPC 4232 := by
    unfold fixedFrame
    rw [state_set_own_register]
  have sameCounter : (openingPathState^[24] s).getReg .x28=0 := by
    rw [path_counter_iterate,counter]
    decide
  have cursor := opening_path_output 24 s
  change (openingPathState^[24] s).getReg .x25=s.getReg .x25+768 at cursor
  have adjusted : ordinaryStep
      (fixedFrame (openingPathState^[24] s) (s.getReg .x25) 0 5384)
      (.base (.ADDI .x25 .x25 768))=some ((openingPathState^[24] s).setPC 5388) := by
    have zero : (openingPathState^[24] s).setReg .x28 0=openingPathState^[24] s := by
      rw [←sameCounter,state_set_own_register]
    have restore (r : MachineState) (base : Word) :
        ordinaryStep (fixedFrame r base 0 5384) (.base (.ADDI .x25 .x25 768))=
          some (((r.setReg .x25 (base+768)).setReg .x28 0).setPC 5388) := by
      cases r
      simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,fixedFrame,
        signExtend12,MachineState.setReg,MachineState.getReg,MachineState.setPC]
      funext reg
      cases reg <;> rfl
    rw [restore,←cursor,state_set_own_register,zero]
  have fetched : fetch fixedImage
      (fixedFrame (openingPathState^[24] s) (s.getReg .x25) 0 5384)=
        some (.base (.ADDI .x25 .x25 768)) := by
    apply fixed_fetch _ 322 _ (by decide) rfl
    rfl
  have adjustRun := execute_ordinary_step fixedImage _ _ _ fuel coins fetched adjusted
  rw [←show 1+fuel=fuel+1 by omega] at adjustRun
  change execute fixedImage (288+(1+fuel)) (fixedFrame s (s.getReg .x25) 0 4232) coins=
    (do let result ← execute fixedImage (1+fuel)
          (fixedFrame (openingPathState^[24] s) (s.getReg .x25) 0 5384) coins
        return result.charge 288 0) at run
  rw [initial,adjustRun] at run
  simpa [Execution.charge,instructionCycles,←Nat.add_assoc] using run
end CommitGolfCandidate.Compact
