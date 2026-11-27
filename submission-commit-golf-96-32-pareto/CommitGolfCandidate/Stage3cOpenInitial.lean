import CommitGolfCandidate.Stage3cOpenEnter
import CommitGolfCandidate.Stage3cOrdinarySibling
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape)

theorem Sources.after_low {s t xs tree salt} (src : Sources s xs tree salt) (size : xs.length≤LENGTH)
    (a n : Nat) (outside : Outside s t a n) (low : a+n≤tdBase) (aligned : a%8=0) (len : n%8=0) :
    Sources t xs tree salt := by
  have bound : xs.length≤16777216:=size
  constructor
  · intro r hr;exact (outside _ (by unfold indexBase MEMORY_BYTES;omega) (by unfold indexBase;omega)
      (Or.inr (by unfold indexBase tdBase at *;omega))).trans (src.index r hr)
  · intro d hd j hj;obtain ⟨lo,up,_⟩:=node_ok d j hj
    exact (outside_read outside aligned len _ 32 (up.trans (by decide)) (Or.inr (low.trans lo))).trans (src.node d hd j hj)
  · intro i;obtain ⟨lo,up,_⟩:=salt_ok i
    exact (outside_read outside aligned len _ 24 (up.trans (by decide)) (Or.inr (low.trans lo))).trans (src.salts i)

theorem empty_mark (td : Trapdoor) (ps : Positions) (j : Nat) (hj : j<512) :
    byteAt (initial td ps) (1024+j)=0 := by
  apply (initial_input_byte Artifact.submission .opening (td,ps) (1024+j) (by omega)).trans
  unfold inputByte
  change (match [fixedBuffer tdBase td,positionsBuffer indexBase ps].find? _ with
      | some b=>b.byteAt (1024+j-b.address)
      | none=>if MEMORY_BYTES≤1024+j then _ else _)=_
  have h₁ : ¬tdBase≤1024+j := by unfold tdBase;omega
  have h₂ : ¬indexBase≤1024+j := by unfold indexBase;omega
  have h₃ : ¬MEMORY_BYTES≤1024+j := by unfold MEMORY_BYTES;omega
  simp [List.find?_cons,fixedBuffer,positionsBuffer,h₁,h₂,h₃]

theorem enter_initial (td : Trapdoor) (ps : Positions) (tree : Levels) (salt : SaltTape)
    (h : TrapdoorAgrees td tree salt) (nonempty : 0<ps.card) :
    let b:=decide (ps.card=128)
    let s:=initial td ps
    ∃ t,Runs s t (if b then 100 else 96) (if b then 100 else 96) ∧ t.pc=pcAt (if b then 126 else 460) ∧
      SeedRegs b ps.card t ∧ t.getReg .x3=W 2048 ∧ Capacity t ∧ Sources t (indices ps) tree salt ∧
      ∀ j<512,byteAt t (1024+j)=0 := by
  have size : ps.card≤LENGTH := by simpa using Finset.card_le_univ ps
  obtain ⟨t,run,pc,seed,gp,table,frame⟩:=enter_open (initial td ps) ps.card nonempty size rfl rfl rfl rfl rfl
  have src:=initial_sources td ps tree salt h
  refine ⟨t,run,pc,seed,gp,table,src.after_low (by simpa [indices] using size) _ _ frame (by decide) (by decide) (by decide),?_⟩
  intro j hj
  exact (outside_byte frame (by decide) (by decide) (by change _<2^36;omega) (Or.inl (by omega))).trans (empty_mark td ps j hj)
end CommitGolfCandidate.Chained.BinaryMachine.Open
