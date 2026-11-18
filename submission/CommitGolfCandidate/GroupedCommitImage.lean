import CommitGolfCandidate.GroupedPacketDecode
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
theorem heads_succ (n : Nat) : heads (n+1)=heads n+(if rank n=0 then 1 else 0) := by
  unfold heads rank
  by_cases last : n%4096=4095
  · rw [show (n+1)/4096=n/4096+1 by omega,show (n+1)%4096=0 by omega,last]
    norm_num;omega
  · rw [show (n+1)/4096=n/4096 by omega,show (n+1)%4096=n%4096+1 by omega]
    have tab : (n%4096+1+10)/11=(n%4096+10)/11+(if n%4096%11=0 then 1 else 0) := by split <;> omega
    rw [tab]; simp only [Nat.add_assoc]

theorem pair_succ (n : Nat) : pairHeads (n+1)=pairHeads n+(if pairPos n=0 then 1 else 0) := by
  unfold pairHeads pairPos
  by_cases last : n%4096=4095
  · rw [show (n+1)/4096=n/4096+1 by omega,show (n+1)%4096=0 by omega,last];norm_num;omega
  · rw [show (n+1)/4096=n/4096 by omega,show (n+1)%4096=n%4096+1 by omega]
    have tab : (n%4096+1+21)/22=(n%4096+21)/22+(if n%4096%22=0 then 1 else 0) := by split <;> omega
    rw [tab];simp only [Nat.add_assoc]

theorem pair_head (n : Nat) (h : pairPos n=0) : rank n=0 := by unfold pairPos rank at *;omega

theorem rb_succ (n : Nat) : rb (n+1)=rb n+(if rebase n then 1 else 0) := by
  have step : rb n≤rb (n+1) ∧ rb (n+1)≤rb n+1 := by unfold rb slotOff;omega
  by_cases h : rebase n
  · rw [if_pos h];unfold rebase at h;omega
  · rw [if_neg h];unfold rebase at h;omega

theorem rb_le (n : Nat) (h : n<4096) : rb n≤91 := by unfold rb slotOff;omega

theorem rb_zero : rb 0=0 := by decide
theorem rb_last : rb 4095=91 := by decide
theorem rebase_last : rebase 4095 := by decide

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

theorem packet_next (n : Nat) : firstWord (n+1)=firstWord n+(packet n).length := by
  unfold firstWord;rw [pair_succ,rb_succ]
  by_cases p : pairPos n=0 <;> by_cases r : rank n=0 <;> by_cases sh : rebase n
  all_goals simp [packet,p,r,sh] <;> first | omega | exact False.elim (r (pair_head n p))

theorem fetch_packet (n : Fin 4096) (i : Nat) (hi : i<(packet n.val).length)
    (state : MachineState) (pc : state.pc=wordPC (firstWord n.val+i)) :
    fetch image state=some (.base ((packet n.val)[i]?.getD .EBREAK)) := by
  have hn:=n.isLt
  have len : (packet n.val).length≤13 := by by_cases r : rank n.val=0 <;> by_cases p : pairPos n.val=0 <;> by_cases sh : rebase n.val <;> simp [packet,r,p,sh]
  have ix : 64*(n.val/64)+n.val%64=n.val := Nat.div_add_mod ..
  have h := packet_tiles ⟨n.val/64,by omega⟩ ⟨n.val%64,by omega⟩ ⟨i,by omega⟩
  simp only [Fin.val_mk,ix] at h
  have rbn := rb_le n.val hn
  exact fetch_decoded state _ (by unfold firstWord pairHeads;omega) pc _ (h hi)

end TwoPermutationPrototype.Grouped
