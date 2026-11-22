import CommitGolfCandidate.GroupOpenHeaderCore
import CommitGolfCandidate.Layout2Pass

/-! Layout 2 V2a opener, the header: today's rows 0..2 and 713..738, the jump at 739 to 3078 and the cursor row 3078
(`addi x29,x21,0`); `Ready` for ordinal 0 at word 3079, 31 cycles. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2V2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

/-- The V2a header: today's header rows, then the cursor row. -/
def header2 (s : MachineState) := walkRows (header s) cursorRows

attribute [local irreducible] setupPrefix walkRows keyCopy header
private theorem key_outside (s : MachineState) (w : Word) (a : w≠1032) (b : w≠1040) (c : w≠1048) :
    (keyCopy s).getMem w=s.getMem w := by
  unfold keyCopy
  exact (MachineState.getMem_setMem_ne c).trans ((MachineState.getMem_setMem_ne b).trans (MachineState.getMem_setMem_ne a))

private theorem key_cell (s : MachineState) (j : Fin 3) : memoryView (keyCopy s) (129+j.val)=
    s.getMem (BitVec.ofNat 64 (9126809640+8*j.val)) := by
  fin_cases j <;> unfold memoryView keyCopy <;> rfl

attribute [local semireducible] walkRows
private theorem cursor_step (t : MachineState) (pc : t.pc=address 3078) :
    legal cursorRows t ∧ (walkRows t cursorRows).pc=address 3079 ∧ (walkRows t cursorRows).mem=t.mem ∧
      (walkRows t cursorRows).getReg .x29=t.getReg .x21 ∧
      (∀ k, k≠.x29 → (walkRows t cursorRows).getReg k=t.getReg k) := by
  refine ⟨⟨pc,rfl,trivial⟩,?_,?_,?_,?_⟩
  · simp [cursorRows,walkRows,execInstrBr,pc,address,pc_of_set]
  · simp [cursorRows,walkRows,execInstrBr,mem_of_set,mem_of_reg]
  · simp [cursorRows,walkRows,execInstrBr,Opening.getReg_setReg,MachineState.getReg_setPC,show signExtend12 0#12=0#64 by decide]
  · intro k h; simp [cursorRows,walkRows,execInstrBr,Opening.getReg_setReg,MachineState.getReg_setPC,Ne.symm h]
attribute [local irreducible] walkRows

theorem header_valid (td : BitVec (8*actual.sizes.trapdoor)) (p : Positions) (nz : 0<p.card) :
    let init:=actual.initialState .opening (td,p)
    legal (headerRows++cursorRows) init ∧ Ready td p (keyOf td) (header2 init) 0 := by
  let init:=actual.initialState .opening (td,p)
  let t:=header init
  have nr : init.getReg .x16≠0#64 := nonempty_count p nz
  obtain ⟨b,salt,marks,mem0⟩:=original_base td p nz
  have shift0 : (setupPrefix init 15).getReg .x25=BitVec.ofNat 64 (8*p.card) := by
    obtain ⟨_,_,_,_,_,_,_,_,_,h25,_,_,_⟩ := setup_registers init
    rw [h25, show init.getReg .x16 = BitVec.ofNat 64 p.card from rfl]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have sp0 : init.getReg .x2=BitVec.ofNat 64 tableBase := by rw [← actual_data_base]; rfl
  obtain ⟨valid,⟨regs⟩,mem⟩:=header_core init p rfl nr b salt marks shift0 nz mem0 rfl sp0
  obtain ⟨cl,cpc,cmem,c29,ckeep⟩ := cursor_step t regs.pc
  have hk (k : Reg) (h : k≠.x29 := by decide) : (header2 init).getReg k=t.getReg k := ckeep k h
  have hmem : (header2 init).mem=(keyCopy init).mem := cmem.trans mem
  have rr := regs.r
  have bb := regs.b
  refine ⟨?_,⟨⟨(hk .x12).trans rr.output,(hk .x5).trans rr.selector,(hk .x11).trans rr.width,
      (hk .x13).trans rr.primitive,(hk .x14).trans rr.index,(hk .x17).trans rr.endReg,
      (by rw [hk .x25, rr.shift, hk .x9, Nat.sub_zero]),(hk .x22).trans rr.salt,(hk .x26).trans rr.base⟩,
    ⟨(hk .x8).trans bb.indices,(hk .x9).trans bb.heap,(hk .x18).trans bb.count,(hk .x19).trans bb.leaves,
      (hk .x20).trans bb.start,(hk .x21).trans bb.dest,(hk .x23).trans bb.mark,(hk .x24).trans bb.slots,
      (hk .x27).trans bb.capLeaves⟩,?_,?_,?_,?_,(hk .x2).trans regs.sp,(hk .x1).trans regs.mask,
    fun _ h => (Nat.not_lt_zero _ h).elim⟩⟩
  · have th : t=walkRows init headerRows := by show header init=_; unfold header; rfl
    exact legal_append _ _ _ valid (th ▸ cl)
  · rw [show passPC p 0=address 3079 by simp [passPC,Nat.ne_of_lt nz]]; exact cpc
  · show (walkRows t cursorRows).getReg .x29=_
    rw [c29, bb.dest]; congr 1
  · intro w fit away
    have guard : w<128 ∨ 153≤w := by
      by_contra h; exact away (Or.inl (by omega))
    have neq (j : Nat) (hj : 129≤j ∧ j≤131) : wordAddress w≠wordAddress j :=
      fun h => (by have :=wordAddress_injective_of_bound (by omega) (by omega) h;omega : False)
    change (header2 init).mem _=_;rw [hmem]
    change (keyCopy init).getMem (wordAddress w)=_
    exact key_outside init _ (neq 129 (by decide)) (neq 130 (by decide)) (neq 131 (by decide))
  · intro j lo hi;change (header2 init).mem _=_;rw [hmem]
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
    execute openingImage (31+fuel) s true=(do let z ←execute openingImage fuel (header2 s) true;return z.charge 31 0) := by
  intro s
  have run := walk_rows_run _ (headerRows++cursorRows) (header_valid td p nz).1
    (fun q hq => (List.mem_append.mp hq).elim (header_fetch q) (cursor_fetch q)) fuel true
  rw [show (headerRows++cursorRows).length=31 by decide, show price (headerRows++cursorRows)=31 by decide] at run
  rw [run]
  unfold header2 header
  rw [walk_join]

end TwoPermutationPrototype.GroupedOpening.Layout2V2
