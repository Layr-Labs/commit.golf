import CommitGolfCandidate.GroupOpenHeaderCore
import CommitGolfCandidate.Layout2FusedLoop

/-! Fused opener, the header: today's rows 0..2 and 713..738, the jump at 739 to 4096 and the row 4096
(`addi x25,x9,0`: `s9 = s1`, the cap stage's heap base, set once before the loop); `Ready` for ordinal 0 at word
4097, 31 cycles. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2F
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
set_option maxRecDepth 22000
set_option maxHeartbeats 2000000

/-- Word 4096: `addi x25,x9,0`. -/
def cursorRows : List Row := [(4096,.ADDI .x25 .x9 0)]

theorem cursor_fetch : presentRows cursorRows := by apply rows_present; decide +kernel

/-- The fused header: today's header rows, then row 4096. -/
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
private theorem cursor_step (t : MachineState) (pc : t.pc=address 4096) :
    legal cursorRows t ∧ (walkRows t cursorRows).pc=address 4097 ∧ (walkRows t cursorRows).mem=t.mem ∧
      (walkRows t cursorRows).getReg .x25=t.getReg .x9 ∧
      (∀ k, k≠.x25 → (walkRows t cursorRows).getReg k=t.getReg k) := by
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
  obtain ⟨cl,cpc,cmem,c25,ckeep⟩ := cursor_step t regs.pc
  have hk (k : Reg) (h : k≠.x25 := by decide) : (header2 init).getReg k=t.getReg k := ckeep k h
  have hmem : (header2 init).mem=(keyCopy init).mem := cmem.trans mem
  have rr := regs.r
  have bb := regs.b
  have card := Layout2V2.card_le p
  have viewH (w : Nat) (fit : w<2^33) (away : w≠129 ∧ w≠130 ∧ w≠131) :
      memoryView (header2 init) w=memoryView init w := by
    have neq (j : Nat) (hj : 129≤j ∧ j≤131) (ne : w≠j) : wordAddress w≠wordAddress j :=
      fun h => ne (wordAddress_injective_of_bound (by omega) (by omega) h)
    change (header2 init).mem _=_;rw [hmem]
    change (keyCopy init).getMem (wordAddress w)=_
    exact key_outside init _ (neq 129 (by decide) away.1) (neq 130 (by decide) away.2.1) (neq 131 (by decide) away.2.2)
  refine ⟨?_,⟨⟨(hk .x12).trans rr.output,(hk .x5).trans rr.selector,(hk .x11).trans rr.width,
      (hk .x13).trans rr.primitive,(hk .x8).trans bb.indices,by rw [hk .x17, rr.endReg]; simp,
      (hk .x22).trans rr.salt,(hk .x26).trans rr.base,(hk .x9).trans bb.heap,
      c25.trans bb.heap,(hk .x19).trans bb.leaves,(hk .x20).trans bb.start,(hk .x23).trans bb.mark,
      (hk .x24).trans bb.slots,(hk .x27).trans bb.capLeaves,(hk .x2).trans regs.sp,(hk .x1).trans regs.mask⟩,
    ?_,?_,fun h => absurd rfl h,?_,?_,?_,?_,fun _ h => (Nat.not_lt_zero _ h).elim⟩⟩
  · have th : t=walkRows init headerRows := by show header init=_; unfold header; rfl
    exact legal_append _ _ _ valid (th ▸ cl)
  · rw [show loopPC p 0=address 4097 by simp [loopPC,Nat.ne_of_lt nz,fphaseWord]]; exact cpc
  · rw [hk .x21, bb.dest]; rfl
  · intro a lo hi al
    have tb : trapdoorBase=4294971424 := rfl
    have ea : BitVec.ofNat 64 a=wordAddress (a/8) := by unfold wordAddress; congr 1; omega
    rw [ea]
    have pb : proofBase=13824430176 := rfl
    exact viewH (a/8) (by omega) (by omega)
  · intro e he h hh
    rw [viewH _ (by simp only [tableWord]; omega) (by simp only [tableWord]; omega)]
    exact initial_table td p e he h hh
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
  · -- the byte marks start at zero: their dwords are zero in the loaded input and the header leaves them
    intro i hi
    have hn : 32+i/8<512 := by omega
    have stable := viewH (512+(32+i/8)) (by omega) (by omega)
    have z := initial_mark_word actual actual_layout image_actual td p (32+i/8) hn
    have addr : BitVec.ofNat 64 (Opening.markBase+8*(32+i/8))=wordAddress (512+(32+i/8)) := by
      unfold Opening.markBase wordAddress;congr 1 <;> omega
    have zz : memoryView init (512+(32+i/8))=0 := by simpa only [addr,memoryView] using z
    have w0 : (header2 init).getMem (BitVec.ofNat 64 (Opening.markBase+8*(32+i/8)))=0 := by
      rw [addr]; exact stable.trans zz
    have al : alignToDword (BitVec.ofNat 64 (Opening.markBase+256+i))=BitVec.ofNat 64 (Opening.markBase+8*(32+i/8)) := by
      rw [table_align_eq (Opening.markBase+256+i) (by unfold Opening.markBase; omega)]; congr 1; unfold Opening.markBase; omega
    unfold MachineState.getByte
    rw [al, w0]
    simp [Opening.groupsBefore, Sampling.capIsMarked, extractByte]

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

end TwoPermutationPrototype.GroupedOpening.Layout2F
