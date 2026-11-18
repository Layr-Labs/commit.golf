import CommitGolfCandidate.GroupedPacketDecode
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
theorem heads_succ (n : Nat) : heads (n+1)=heads n+(if rank n=0 then 1 else 0) := by
  unfold heads rank
  by_cases last : n%2048=2047
  · rw [show (n+1)/2048=n/2048+1 by omega,show (n+1)%2048=0 by omega,last]
    norm_num;omega
  · rw [show (n+1)/2048=n/2048 by omega,show (n+1)%2048=n%2048+1 by omega]
    have tab : (n%2048+1+10)/11=(n%2048+10)/11+(if n%2048%11=0 then 1 else 0) := by split <;> omega
    rw [tab]; simp only [Nat.add_assoc]

theorem pair_succ (n : Nat) : pairHeads (n+1)=pairHeads n+(if pairPos n=0 then 1 else 0) := by
  unfold pairHeads pairPos
  by_cases last : n%2048=2047
  · rw [show (n+1)/2048=n/2048+1 by omega,show (n+1)%2048=0 by omega,last];norm_num;omega
  · rw [show (n+1)/2048=n/2048 by omega,show (n+1)%2048=n%2048+1 by omega]
    have tab : (n%2048+1+21)/22=(n%2048+21)/22+(if n%2048%22=0 then 1 else 0) := by split <;> omega
    rw [tab];simp only [Nat.add_assoc]

theorem pair_head (n : Nat) (h : pairPos n=0) : rank n=0 := by unfold pairPos rank at *;omega

theorem packet_next (n : Nat) : firstWord (n+1)=firstWord n+(packet n).length := by
  unfold firstWord;rw [pair_succ]
  by_cases p : pairPos n=0 <;> by_cases r : rank n=0 <;> by_cases sh : n%32=31
  all_goals simp [packet,p,r,sh] <;> first | omega | exact False.elim (r (pair_head n p))

theorem fetch_packet (n : Fin 4096) (i : Nat) (hi : i<(packet n.val).length)
    (state : MachineState) (pc : state.pc=wordPC (firstWord n.val+i)) :
    fetch image state=some (.base ((packet n.val)[i]?.getD .EBREAK)) := by
  have hn:=n.isLt
  have len : (packet n.val).length≤13 := by by_cases r : rank n.val=0 <;> by_cases p : pairPos n.val=0 <;> by_cases sh : n.val%32=31 <;> simp [packet,r,p,sh]
  have ix : 64*(n.val/64)+n.val%64=n.val := Nat.div_add_mod ..
  have h := packet_tiles ⟨n.val/64,by omega⟩ ⟨n.val%64,by omega⟩ ⟨i,by omega⟩
  simp only [Fin.val_mk,ix] at h
  exact fetch_decoded state _ (by unfold firstWord pairHeads;omega) pc _ (h hi)

end TwoPermutationPrototype.Grouped
