import CommitGolfCandidate.GroupedPacketDecode
namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
theorem heads_succ (n : Nat) : heads (n+1)=heads n+(if rank n=0 then 1 else 0) := by
  unfold heads rank
  by_cases last : n%64=63
  · rw [show (n+1)/64=n/64+1 by omega,show (n+1)%64=0 by omega,last]
    norm_num;omega
  · rw [show (n+1)/64=n/64 by omega,show (n+1)%64=n%64+1 by omega]
    have tab : ∀ j : Fin 63, (j.val+1+10)/11=(j.val+10)/11+(if j.val%11=0 then 1 else 0) := by decide
    rw [tab ⟨n%64,by omega⟩]; simp only [Fin.val_mk,Nat.add_assoc]

theorem packet_next (n : Nat) : firstWord (n+1)=firstWord n+(packet n).length := by
  unfold firstWord
  rw [heads_succ]
  unfold packet
  split <;> split <;> simp <;> omega

theorem fetch_packet (n : Fin 4096) (i : Nat) (hi : i<(packet n.val).length)
    (state : MachineState) (pc : state.pc=wordPC (firstWord n.val+i)) :
    fetch image state=some (.base ((packet n.val)[i]?.getD .EBREAK)) := by
  have hn:=n.isLt
  have len : (packet n.val).length≤13 := by unfold packet;split <;> split <;> simp
  have ix : 64*(n.val/64)+n.val%64=n.val := Nat.div_add_mod ..
  have h := packet_tiles ⟨n.val/64,by omega⟩ ⟨n.val%64,by omega⟩ ⟨i,by omega⟩
  simp only [Fin.val_mk,ix] at h
  exact fetch_decoded state _ (by unfold firstWord heads;omega) pc _ (h hi)

end TwoPermutationPrototype.Grouped
