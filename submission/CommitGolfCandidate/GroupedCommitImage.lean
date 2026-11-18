import CommitGolfCandidate.GroupedPacketDecode
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem heads_before_le (p : Nat) : headsBefore p ≤ p := by
  unfold headsBefore; split_ifs <;> omega

theorem heads_before_succ (p : Nat) : headsBefore (p+1)=headsBefore p+(if pairHead p then 1 else 0) := by
  unfold headsBefore pairHead; split_ifs <;> omega

theorem pair_packet_length (p : Nat) :
    (pairPacket p).length=22-(if pairHead p then 3 else 0)+(if p%16=15 then 1 else 0) := by
  by_cases h : pairHead p <;> by_cases r : p%16=15 <;> simp only [pairPacket,h,r,ite_true,ite_false] <;> rfl

theorem pair_word_next (p : Nat) : pairWord (p+1)=pairWord p+(pairPacket p).length := by
  rw [pair_packet_length]; unfold pairWord; rw [heads_before_succ]
  have := heads_before_le p
  split_ifs <;> omega

theorem pair_word_bound (p : Nat) (hp : p<2048) : pairWord p+23 ≤ 201767 := by
  have := heads_before_le p; unfold pairWord; omega

theorem pair_word_latch : pairWord 2048=44086 := by decide

theorem fetch_pair_packet (p : Fin 2048) (i : Nat) (hi : i<(pairPacket p.val).length)
    (state : MachineState) (pc : state.pc=wordPC (pairWord p.val+i)) :
    fetch image state=some (.base ((pairPacket p.val)[i]?.getD .EBREAK)) := by
  have hp := p.isLt
  have len : (pairPacket p.val).length≤23 := by rw [pair_packet_length]; split_ifs <;> omega
  have ix : 64*(p.val/64)+p.val%64=p.val := Nat.div_add_mod ..
  have h := pair_tiles ⟨p.val/64,by omega⟩ ⟨p.val%64,by omega⟩ ⟨i,by omega⟩
  simp only [Fin.val_mk,ix] at h
  have bnd := pair_word_bound p.val hp
  exact fetch_decoded state _ (by omega) pc _ (h hi)

end TwoPermutationPrototype.Grouped
