import CommitGolfCandidate.S5RecordCycle
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape record)
attribute [local irreducible] readBuffer afterLatch ix
set_option maxRecDepth 14000
set_option maxHeartbeats 160000
private theorem first_room {a n limit : Nat} (room : a+824*(n+1)≤limit) : a+824≤limit := by omega
theorem ordinary_records (xs : List Index) (tree : Levels) (salt : SaltTape) (r n dst : Nat) (s : MachineState)
    (total : r+n=xs.length) (size : xs.length≤LENGTH) (reg : OrdinaryRegs s r xs.length dst) (tab : Capacity s)
    (src : Sources s xs tree salt) (high : proofBase≤dst) (valid : AddrOK dst (824*n)) :
    ∃ t, Runs s t (ordinaryCost xs r n) (ordinaryCost xs r n+12*n) ∧ OrdinaryRegs t xs.length xs.length (dst+824*n) ∧
      Written s t dst (records xs tree salt r n) := by
  induction n generalizing r dst s with
  | zero=>
    simp only [Nat.add_zero] at total;subst r
    exact ⟨s,Runs.refl _,by simpa using reg,Written.empty ..⟩
  | succ n ih=>
    have lt : r<xs.length := by omega
    have memBound := valid.2
    have align := valid.1
    obtain ⟨v,head,next,c,sources,data⟩:=record_cycle xs tree salt r dst s lt size reg tab src high ⟨align,first_room memBound⟩
    have later:=ih (r+1) (dst+824) v (by omega) next c sources (by omega) ⟨by omega,by omega⟩
    obtain ⟨t,tail,last,w⟩:=later
    have both:=head.trans tail
    refine ⟨t,?_,?_,?_⟩
    · change Runs s t (perRecord xs r+ordinaryCost xs (r+1) n) ((perRecord xs r+ordinaryCost xs (r+1) n)+12*(n+1))
      convert both using 1 <;> omega
    · simpa only [show dst+824+824*n=dst+824*(n+1) by omega] using last
    · change Written s t dst (_++_)
      apply data.append
      · rw [record_length];exact w
      · rw [record_length];omega
      · rw [records_length];omega
      · rw [record_length];exact first_room memBound
end CommitGolfCandidate.S5Machine.Open
