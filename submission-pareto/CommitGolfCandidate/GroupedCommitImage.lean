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

theorem rank_lt (n : Nat) : rank n<11 := by unfold rank;omega

/-- Code words of slot `n` of rank `r`, quartet calls excluded. -/
def leafLen (r : Nat) := rankPrefix (r+1)-rankPrefix r
/-- Extra words of a quartet call: two for an even quartet, three for an odd one. -/
def extraLen (n : Nat) := if n%8=3 then 2 else if n%8=7 then 3 else 0

/-- A chained head is one word shorter than a keyed one. -/
def chainLen (n : Nat) := if rank n=0 ∧ ¬keyed n then 1 else 0

theorem packet_length (n : Nat) :
    (packet n).length+chainLen n=leafLen (rank n)+extraLen n := by
  unfold packet leafLen tailCode extraLen chainLen
  have h := rank_lt n
  by_cases a : n%4=3
  · by_cases b : (n/4)%2=0
    · have e : n%8=3 := by omega
      generalize rank n=r at *
      by_cases kd : keyed n <;> interval_cases r <;> simp [a,b,e,kd,saltCode,rankPrefix]
    · have e : n%8=7 := by omega
      have e' : n%8≠3 := by omega
      generalize rank n=r at *
      by_cases kd : keyed n <;> interval_cases r <;> simp [a,b,e,e',kd,saltCode,rankPrefix]
  · have e1 : n%8≠3 := by omega
    have e2 : n%8≠7 := by omega
    generalize rank n=r at *
    by_cases kd : keyed n <;> interval_cases r <;> simp [a,e1,e2,kd,saltCode,rankPrefix]

theorem leaf_len_le (r : Nat) (h : r<11) : leafLen r≤15 := by
  unfold leafLen;interval_cases r <;> simp [rankPrefix]

private theorem prefix_step (r : Nat) (h : r<10) : rankPrefix (r+1)=rankPrefix r+leafLen r := by
  unfold leafLen;interval_cases r <;> simp [rankPrefix]

private theorem prefix_last : rankPrefix 0+117=rankPrefix 10+leafLen 10 := by
  simp [leafLen,rankPrefix]

theorem rank_prefix_pos (r : Nat) (h : 1≤r) : 1≤rankPrefix r := by
  unfold rankPrefix;split_ifs <;> omega

theorem chained_step (n : Nat) :
    chainedBefore (n+1)=chainedBefore n+(if n%11=0 ∧ ¬(n/11)%34=0 then 1 else 0) := by
  unfold chainedBefore
  split_ifs with c <;> omega

theorem first_word_eq (n : Nat) :
    firstWord n+chainedBefore n=21+117*(n/11)+rankPrefix (n%11)+2*((n+4)/8)+3*(n/8) := by
  have cb : chainedBefore n≤117*(n/11)+rankPrefix (n%11) := by
    by_cases z : n%11=0
    · unfold chainedBefore;omega
    · have := rank_prefix_pos (n%11) (by omega);unfold chainedBefore;omega
  unfold firstWord;omega

theorem packet_next (n : Nat) (hn : n<4096) : firstWord (n+1)=firstWord n+(packet n).length := by
  have pl := packet_length n
  simp only [extraLen,chainLen,keyed,rank,Nat.mod_eq_of_lt hn,beq_iff_eq] at pl
  have f0 := first_word_eq n
  have f1 := first_word_eq (n+1)
  have cs := chained_step n
  have e1 : (n+1+4)/8=(n+4)/8+(if n%8=3 then 1 else 0) := by split <;> omega
  have e2 : (n+1)/8=n/8+(if n%8=7 then 1 else 0) := by split <;> omega
  by_cases last : n%11=10
  · rw [show (n+1)/11=n/11+1 by omega,show (n+1)%11=0 by omega] at f1
    have := prefix_last
    have l10 : leafLen (n%11)=leafLen 10 := by rw [last]
    have r10 : rankPrefix (n%11)=rankPrefix 10 := by rw [last]
    split_ifs at pl cs e1 e2 <;> omega
  · rw [show (n+1)/11=n/11 by omega,show (n+1)%11=n%11+1 by omega] at f1
    have := prefix_step (n%11) (by omega)
    split_ifs at pl cs e1 e2 <;> omega

theorem rank_prefix_le (r : Nat) : rankPrefix r≤117 := by
  unfold rankPrefix;split_ifs <;> omega

theorem first_word_le (n : Nat) (hn : n≤4096) : firstWord n≤46222 := by
  have := rank_prefix_le (n%11);unfold firstWord;omega

theorem fetch_packet (n : Fin 4096) (i : Nat) (hi : i<(packet n.val).length)
    (state : MachineState) (pc : state.pc=wordPC (firstWord n.val+i)) :
    fetch image state=some (.base ((packet n.val)[i]?.getD .EBREAK)) := by
  have hn:=n.isLt
  have len : (packet n.val).length≤18 := by
    have pl := packet_length n.val;have := leaf_len_le _ (rank_lt n.val);unfold extraLen at pl;split_ifs at pl <;> omega
  have ix : 64*(n.val/64)+n.val%64=n.val := Nat.div_add_mod ..
  have h := packet_tiles ⟨n.val/64,by omega⟩ ⟨n.val%64,by omega⟩ ⟨i,by omega⟩
  simp only [Fin.val_mk,ix] at h
  have bound := first_word_le n.val (by omega)
  exact fetch_decoded state _ (by omega) pc _ (h hi)

end TwoPermutationPrototype.Grouped
