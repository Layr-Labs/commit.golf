import CommitGolfCandidate.TwoPermutationWideLeafAccess

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute readBuffer writeBits packBuffer

theorem first_permutation_segment (s : MachineState) (slot : Fin 256) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (coins : Bool) :
    execute wideCommitImage (3+fuel) s coins =
      (do let a ← World.query (.inr (.inr (.inl (packBuffer
            (Overlap.firstInput (window (memoryView s) (start+5)))))))
          let r ← execute wideCommitImage fuel (repliedA s slot start a) coins
          return r.charge 10 1) := by
  obtain ⟨_,r10,r12,r5,r11,r13,hpc⟩ := first_execution s slot
  have atCall : (preparedA s slot).pc = leafPC slot 2 := by
    rw [preparedA,hpc,pc]; exact leaf_pc_add slot 0 2
  have room := ready.sourceBound
  have call := execute_permutation_call wideCommitImage fuel (preparedA s slot) coins (start+4) (start-8)
    (by omega) (by omega) (r10.trans ready.source) (r12.trans (by rw [ready.source,first_dest start ready.front]))
    (r5.trans ready.selector) (r11.trans ready.size) (r13.trans ready.primitive)
    (fetch_leaf slot 2 (by decide) _ atCall)
  have low := ready.front
  have eq : start-8+12=start+4 := by omega
  have input := first_call_input s slot (start-8) (eq.symm ▸ ready.source) (by omega)
  rw [eq,show start-8+13=start+5 by omega] at input
  change window (memoryView (preparedA s slot)) (start+4) = _ at input
  rw [input] at call
  rw [show 3+fuel=2+(fuel+1) by omega,first_ordinary_run _ _ _ _ pc (first_accesses _ _ _ _ _ _ ready)]
  change (do let r ← execute wideCommitImage (fuel+1) (preparedA s slot) coins; return r.charge 2 0) = _
  rw [call]
  simp [repliedA,Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

theorem second_permutation_segment (s : MachineState) (slot : Fin 256) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0)
    (a : BitVec 1600) (coins : Bool) :
    execute wideCommitImage (9+fuel) (repliedA s slot start a) coins =
      (do let b ← World.query (.inr (.inr (.inl (packBuffer
            (Overlap.secondInput index (nonceWords s slot) (replyWords a) (window (memoryView s) (start+5)))))))
          let r ← execute wideCommitImage fuel (finishedLeaf s slot start dst a b) coins
          return r.charge 16 1) := by
  let prev := repliedA s slot start a
  have src : prev.getReg .x10 = wordAddress (start+4) := after_a_input_cursor _ _ _ _ _ _ ready _
  obtain ⟨p5,p11,p13,p20,ppc⟩ := after_a_control _ _ _ _ _ _ ready pc a
  have ⟨_,r10,r12,r5,r11,r13,hpc⟩ := second_execution prev slot
  have atCall : (preparedB s slot start a).pc = leafPC slot 10 := by
    change ((secondInstructions slot).foldl execInstrBr prev).pc = _
    rw [hpc,show prev.pc=leafPC slot 3 from ppc]
    exact leaf_pc_add slot 3 7
  have inReg : (preparedB s slot start a).getReg .x10 = wordAddress (start+12) := by
    change ((secondInstructions slot).foldl execInstrBr prev).getReg .x10 = _
    rw [r10,src]; exact address_plus _ 8 _ (by omega)
  have outReg : (preparedB s slot start a).getReg .x12 = wordAddress dst := by
    change ((secondInstructions slot).foldl execInstrBr prev).getReg .x12 = _
    rw [r12,show prev.getReg .x20 = s.getReg .x20 from p20,ready.destination]
  have sb := ready.sourceBound
  have call := execute_permutation_call wideCommitImage (fuel+1) (preparedB s slot start a) coins (start+12) dst
    (by omega) ready.heapBound inReg outReg (r5.trans p5) (r11.trans p11) (r13.trans p13)
    (fetch_leaf slot 10 (by decide) _ atCall)
  rw [after_b_input _ _ _ _ _ _ ready a] at call
  have last (b : BitVec 1600) : execute wideCommitImage (fuel+1) (repliedB s slot start dst a b) coins =
      (do let r ← execute wideCommitImage fuel (finishedLeaf s slot start dst a b) coins; return r.charge 1 0) := by
    have atLast : (repliedB s slot start dst a b).pc = leafPC slot 11 := by
      unfold repliedB writeBits
      change (preparedB s slot start a).pc + 4 = _
      rw [atCall];exact leaf_pc_add slot 10 1
    exact CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf slot 11 (by decide) _ atLast) rfl
  rw [show 9+fuel=7+((fuel+1)+1) by omega,
    second_ordinary_run prev slot _ coins ppc (second_accesses prev slot start salts src ((after_a_nonce_reg ..).trans ready.nonces) ready.sourceBound ready.nonceBound)]
  change (do let r ← execute wideCommitImage ((fuel+1)+1) (preparedB s slot start a) coins; return r.charge 7 0) = _
  rw [call]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro b _
  change BitVec 1600 at b
  change (do let result ← execute wideCommitImage (fuel+1) (repliedB s slot start dst a b) coins
             pure ((result.charge 8 1).charge 7 0)) = _
  rw [last b]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

def leafTrace (s : MachineState) (slot : Fin 256) (start index dst : Nat) : OracleComp World MachineState := do
  let message := window (memoryView s) (start+5)
  let a ← World.query (.inr (.inr (.inl (packBuffer (Overlap.firstInput message)))))
  let b ← World.query (.inr (.inr (.inl (packBuffer (Overlap.secondInput index (nonceWords s slot) (replyWords a) message)))))
  return finishedLeaf s slot start dst a b

theorem execute_two_permutation_leaf (s : MachineState) (slot : Fin 256) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (coins : Bool) :
    execute wideCommitImage (12+fuel) s coins =
      (do let done ← leafTrace s slot start index dst
          let r ← execute wideCommitImage fuel done coins
          return r.charge 26 2) := by
  rw [show 12+fuel=3+(9+fuel) by omega,first_permutation_segment _ _ _ _ _ _ _ ready pc]
  simp only [leafTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change BitVec 1600 at a
  rw [second_permutation_segment _ _ _ _ _ _ _ ready pc a coins]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl


end TwoPermutationPrototype.RV64.WideLeaves
