import CommitGolfCandidate.GroupedPacketDecode
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

theorem heads_before_le (p : Nat) : headsBefore p ≤ p := by
  unfold headsBefore; split_ifs <;> omega

theorem heads_before_succ (p : Nat) : headsBefore (p+1)=headsBefore p+(if pairHead p then 1 else 0) := by
  unfold headsBefore pairHead; split_ifs <;> omega

theorem rb_succ (n : Nat) : rb (n+1)=rb n+(if rebase n then 1 else 0) := by
  have step : rb n≤rb (n+1) ∧ rb (n+1)≤rb n+1 := by unfold rb slotOff;omega
  by_cases h : rebase n
  · rw [if_pos h];unfold rebase at h;omega
  · rw [if_neg h];unfold rebase at h;omega

theorem rb_le (n : Nat) (h : n<4096) : rb n≤91 := by unfold rb slotOff;omega
theorem rb_zero : rb 0=0 := by decide
theorem rb_last : rb 4095=91 := by decide
theorem rebase_last : rebase 4095 := by decide

/-- Two leaves of a pair are never both followed by a rebase (blocks advance at most 304 bytes in two leaves). -/
theorem no_double_rebase (p : Nat) : ¬(rebase (2*p) ∧ rebase (2*p+1)) := by
  have two : rb (2*p+2) ≤ rb (2*p)+1 := by unfold rb slotOff; omega
  rw [rb_succ,rb_succ] at two
  intro ⟨a,b⟩; rw [if_pos a,if_pos b] at two; omega

/-- Rebases over the whole vector: 92 per 4,096-leaf body plus `rb` inside the current body. -/
theorem rebases_succ (i : Nat) :
    92*((i+1)/4096)+rb ((i+1)%4096)=92*(i/4096)+rb (i%4096)+(if rebase (i%4096) then 1 else 0) := by
  by_cases last : i%4096=4095
  · rw [show (i+1)%4096=0 by omega,show (i+1)/4096=i/4096+1 by omega,last,if_pos rebase_last,rb_zero,rb_last]
    omega
  · rw [show (i+1)%4096=i%4096+1 by omega,show (i+1)/4096=i/4096 by omega,rb_succ]
    by_cases h : rebase (i%4096)
    · rw [if_pos h];omega
    · rw [if_neg h];omega

/-- Rebases over the whole vector: 92 per 2,048-pair body plus `rb (2p)` inside the current body. -/
theorem pair_rebases_succ (P : Nat) :
    92*((P+1)/2048)+rb (2*((P+1)%2048))=
      92*(P/2048)+rb (2*(P%2048))+(if rebase (2*(P%2048)) then 1 else 0)+(if rebase (2*(P%2048)+1) then 1 else 0) := by
  by_cases last : P%2048=2047
  · have n0 : ¬rebase (2*2047) := by decide
    have n1 : rebase (2*2047+1) := by decide
    rw [show (P+1)%2048=0 by omega,show (P+1)/2048=P/2048+1 by omega,last,show rb (2*0)=0 by decide,
      show rb (2*2047)=91 by decide,if_neg n0,if_pos n1]
    omega
  · rw [show (P+1)%2048=P%2048+1 by omega,show (P+1)/2048=P/2048 by omega,
      show 2*(P%2048+1)=2*(P%2048)+1+1 by omega,rb_succ,rb_succ]
    omega

/-- Words a pair packet saves against 22 (before its rebase words). -/
def pairSaving (p : Nat) : Nat :=
  if pairHead p then (if prefetchA p ∨ p%11=5 then 2 else 4) else if fromRegs p then 4 else 0

theorem pair_packet_length (p : Nat) :
    (pairPacket p).length=22-pairSaving p+(if rebase (2*p) then 1 else 0)+(if rebase (2*p+1) then 1 else 0) := by
  unfold pairSaving
  by_cases h : pairHead p <;> by_cases a : prefetchA p <;> by_cases b : p%11=5 <;> by_cases t : fromRegs p <;>
    by_cases r : rebase (2*p) <;> by_cases r' : rebase (2*p+1) <;>
    simp only [pairPacket,h,a,b,t,r,r',ite_true,ite_false,or_true,or_false,true_or,false_or] <;>
    first | rfl | (exfalso; unfold pairHead prefetchA fromRegs at *; omega)

theorem pair_saving_le (p : Nat) : pairSaving p ≤ 4 := by unfold pairSaving; split_ifs <;> omega

theorem pair_word_next (p : Nat) (hp : p<2048) : pairWord (p+1)=pairWord p+(pairPacket p).length := by
  rw [pair_packet_length]; unfold pairWord pairSaving
  rw [show 2*(p+1)=2*p+1+1 by omega,rb_succ,rb_succ,heads_before_succ]
  have := heads_before_le p
  split_ifs
  all_goals (try unfold prefetchA at *)
  all_goals (try unfold fromRegs at *)
  all_goals (try unfold pairHead at *)
  all_goals omega

theorem pair_word_bound (p : Nat) (hp : p<2048) : pairWord p+23 ≤ 201767 := by
  have := heads_before_le p; have := rb_le (2*p) (by omega); unfold pairWord; split_ifs <;> omega

theorem pair_word_latch : pairWord 2048=43677 := by decide

theorem fetch_pair_packet (p : Fin 2048) (i : Nat) (hi : i<(pairPacket p.val).length)
    (state : MachineState) (pc : state.pc=wordPC (pairWord p.val+i)) :
    fetch image state=some (.base ((pairPacket p.val)[i]?.getD .EBREAK)) := by
  have hp := p.isLt
  have len : (pairPacket p.val).length≤23 := by
    rw [pair_packet_length]; have := pair_saving_le p.val; have nd := no_double_rebase p.val
    split_ifs <;> simp_all <;> omega
  have ix : 64*(p.val/64)+p.val%64=p.val := Nat.div_add_mod ..
  have h := pair_tiles ⟨p.val/64,by omega⟩ ⟨p.val%64,by omega⟩ ⟨i,by omega⟩
  simp only [Fin.val_mk,ix] at h
  have bnd := pair_word_bound p.val hp
  exact fetch_decoded state _ (by omega) pc _ (h hi)

end TwoPermutationPrototype.Grouped
