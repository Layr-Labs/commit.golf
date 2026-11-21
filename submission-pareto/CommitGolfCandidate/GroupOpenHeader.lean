import CommitGolfCandidate.GroupOpenHeaderCore

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open Opening (RecordMarks)
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

attribute [local irreducible] setupPrefix walkRows keyCopy header
private theorem key_outside (s : MachineState) (w : Word) (a : w≠1032) (b : w≠1040) (c : w≠1048) :
    (keyCopy s).getMem w=s.getMem w := by
  unfold keyCopy
  exact (MachineState.getMem_setMem_ne c).trans ((MachineState.getMem_setMem_ne b).trans (MachineState.getMem_setMem_ne a))

private theorem key_cell (s : MachineState) (j : Fin 3) : memoryView (keyCopy s) (129+j.val)=
    s.getMem (BitVec.ofNat 64 (9126809640+8*j.val)) := by
  fin_cases j <;> unfold memoryView keyCopy <;> rfl

theorem header_valid (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let init:=actual.initialState .opening (td,p)
    legal headerRows init ∧ Ready td p (keyOf td) (header init) 0 := by
  let init:=actual.initialState .opening (td,p)
  let t:=header init
  have nr : init.getReg .x16≠0#64 := nonempty_count p nz
  obtain ⟨b,salt,marks,mem0⟩:=original_base td p nz
  have shift0 : (setupPrefix init 15).getReg .x25=BitVec.ofNat 64 (8*p.card) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,h25,_,_,_⟩ := setup_registers init
    rw [h25, show init.getReg .x16 = BitVec.ofNat 64 p.card from rfl]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  obtain ⟨valid,⟨regs⟩,mem⟩:=header_core init p rfl nr b salt marks shift0 nz mem0 rfl
  refine ⟨valid,⟨regs.r,regs.b,?_,by simpa [lastOf] using regs.quartet,?_,?_,regs.gp,regs.sp,regs.mask,
    fun _ h => (Nat.not_lt_zero _ h).elim⟩⟩
  · simpa only [passPC,ite_eq_right (Nat.ne_of_lt nz)] using regs.pc
  · intro w fit away
    have guard : w<128 ∨ 153≤w := by
      by_contra h; exact away (Or.inl (by omega))
    have neq (j : Nat) (hj : 129≤j ∧ j≤131) : wordAddress w≠wordAddress j :=
      fun h => (by have :=wordAddress_injective_of_bound (by omega) (by omega) h;omega : False)
    change t.mem _=_;rw [mem]
    change (keyCopy init).getMem (wordAddress w)=_
    exact key_outside init _ (neq 129 (by decide)) (neq 130 (by decide)) (neq 131 (by decide))
  · intro j lo hi;change t.mem _=_;rw [mem]
    by_cases stored : j≤3
    · let ix : Fin 3 := ⟨j-1,by omega⟩
      change memoryView (keyCopy init) (128+j)=_
      rw [show 128+j=129+ix.val by dsimp [ix];omega,key_cell init ix]
      exact key_words td p ix
    · have neq (n : Nat) (hn : 129≤n ∧ n≤131) : wordAddress (128+j)≠wordAddress n :=
        fun h => (by have :=wordAddress_injective_of_bound (by omega) (by omega) h;omega : False)
      change (keyCopy init).getMem (wordAddress (128+j))=_
      rw [key_outside init _ (neq 129 (by decide)) (neq 130 (by decide)) (neq 131 (by decide))]
      change memoryView init (128+j)=_
      rw [low_zero td p _ (by omega)]
      apply BitVec.eq_of_getLsbD_eq;intro b hb
      simp [keyBlock,hb,show 192≤64*(j-1)+b by omega]

theorem header_run (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) (fuel : Nat) :
    let s:=actual.initialState .opening (td,p)
    execute openingImage (35+fuel) s true=(do let z ←execute openingImage fuel (header s) true;return z.charge 35 0) := by
  simpa only [header,show headerRows.length=35 by decide,show price headerRows=35 by decide] using
    walk_rows_run _ headerRows (header_valid td p nz).1 header_fetch fuel true

theorem certifiedHeader : HeaderFacts :=
  ⟨fun td p nz => (header_valid td p nz).2,header_run⟩

end TwoPermutationPrototype.GroupedOpening
