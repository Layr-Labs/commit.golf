import CommitGolfCandidate.R1bOpenTail
import CommitGolfCandidate.R1bWire

namespace CommitGolfCandidate.R1b.Opening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine TwoPermutationPrototype
open R1bPC (pcAt)

def tailSteps (n len : Nat) : Nat := if n≠128 then 8 else if len≤67488 then 11 else 11192

structure Finished (ps : Positions) (xs : Proof) (s t : MachineState) : Prop where
  run : ∀ fuel coins, execute (Code.image .opening) (tailSteps ps.card xs.length+fuel) s coins =
    pure ⟨.success,t,3+extra ps.card xs.length,0⟩
  len : t.getReg .x11=W (Hybrid.wireProof ps xs).length
  bytes : ∀ i, i<(Hybrid.wireProof ps xs).length →
    byte t (proofBase+i)=Carry.read (Hybrid.wireProof ps xs) i

theorem finish (ps : Positions) (xs : Proof) (s : MachineState) (pc : s.pc=pcAt 664)
    (nr : s.getReg .x16=W ps.card) (nb : ps.card<2^64) (lr : s.getReg .x11=W xs.length)
    (lb : xs.length<2^64) (base : s.getReg .x20=W proofBase)
    (contents : ∀ i, i<xs.length ∨ i<67840 → byte s (proofBase+i)=Carry.read xs i)
    (max : ps.card=128 → xs.length≤67840) : ∃ t,Finished ps xs s t := by
  obtain ⟨u,rt⟩:=route ps.card xs.length s pc nr nb lr lb base
  by_cases packing : packNow ps.card xs.length
  · have cond : ps.card=128 ∧ 67488<xs.length := of_decide_eq_true packing
    have batch : ps.card=BATCH:=cond.1
    have after:=rt.packet packing
    have addr:=rt.pc
    rw [if_pos packing] at addr
    obtain ⟨v,m,ip,run⟩:=Codec.realCodec false u addr after
    have lv : v.getReg .x11=W xs.length := (m.keep .x11 (by decide)).trans (rt.length.trans lr)
    obtain ⟨w,tagged,wpc,wlen,wrote⟩:=tagRun v xs.length (max cond.1) cond.2 ip lv m.tail
    let t:=haltState w
    let tag:=BitVec.ofNat 8 ((xs.length-64000)/30)
    have wire : Hybrid.wireProof ps xs=Carry.packed xs++[tag] := by
      simp only [Hybrid.wireProof,if_pos batch,Carry.batchEncode,if_neg (Nat.not_le.mpr cond.2),tag]
    have size : (Hybrid.wireProof ps xs).length=67489 := by rw [wire];simp [Carry.packed_length]
    refine ⟨t,⟨?_,?_,?_⟩⟩
    · intro fuel coins
      have chain:=((rt.run.trans run).trans tagged) (4+fuel) coins
      simp only [cond.1,ne_self_iff_false,ite_false,if_neg (Nat.not_le.mpr cond.2)] at chain
      change execute (Code.image .opening) (4+fuel+(7+11173+8)) s coins=_ at chain
      rw [tailSteps,if_neg (not_not_intro cond.1),if_neg (Nat.not_le.mpr cond.2),
        show 11192+fuel=4+fuel+(7+11173+8) by omega,chain,halt w wpc]
      simp [extra,cond.1,Nat.not_le.mpr cond.2,Execution.charge,t,Codec.bodySteps]
    · rw [size];exact wlen
    · intro i hi
      rw [size] at hi
      change byte w (proofBase+i)=_
      rw [wrote _ (by unfold proofBase;omega),wire]
      have plen:=Carry.packed_length xs
      by_cases before : i<67488
      · rw [if_neg (by omega)]
        have bytes:=m.memory.atByte i (by omega)
        have eqf (j : Nat) (hj : j<67840) : Codec.original u j=Carry.read xs j := by
          change byte u _=_
          rw [show byte u (proofBase+j)=byte s (proofBase+j) by simp only [byte,MachineState.getByte,MachineState.getMem,rt.memory]]
          exact contents j (Or.inr hj)
        rw [Carry.encoded,Codec.packed_agrees _ _ eqf i before,←Carry.packed_byte _ _ before] at bytes
        simpa only [Carry.read,List.getElem?_append_left (show i<(Carry.packed xs).length by omega)] using bytes
      · have last : i=67488 := by omega
        subst i;rw [if_pos (by omega)]
        simp [Carry.read,List.getElem?_append,plen,tag]
  · have bypass : Hybrid.wireProof ps xs=xs := by
      unfold Hybrid.wireProof
      split
      · rename_i same
        have b : ps.card=128 := same
        have h : xs.length≤67488 := by by_contra! e;exact packing (decide_eq_true ⟨b,e⟩)
        simp [Carry.batchEncode,h]
      · rfl
    have returnAt:=rt.pc
    rw [if_neg packing] at returnAt
    refine ⟨haltState u,⟨?_,?_,?_⟩⟩
    · intro fuel coins
      have chain:=rt.run (4+fuel) coins
      by_cases batch : ps.card=128
      · have short : xs.length≤67488 := by by_contra! e;exact packing (decide_eq_true ⟨batch,e⟩)
        simp only [batch,ne_self_iff_false,ite_false,if_pos short] at chain
        rw [tailSteps,if_neg (not_not_intro batch),if_pos short,show 11+fuel=4+fuel+7 by omega,chain,halt u returnAt]
        simp [extra,batch,short,Execution.charge]
      · simp only [if_pos batch] at chain
        rw [tailSteps,if_pos batch,show 8+fuel=4+fuel+4 by omega,chain,halt u returnAt]
        simp [extra,batch,Execution.charge]
    · rw [bypass];exact rt.length.trans lr
    · rw [bypass];intro i hi
      change byte u (proofBase+i)=_
      have eq : byte u (proofBase+i)=byte s (proofBase+i) := by simp only [byte,MachineState.getByte,MachineState.getMem,rt.memory]
      exact eq.trans (contents i (Or.inl hi))
end CommitGolfCandidate.R1b.Opening
