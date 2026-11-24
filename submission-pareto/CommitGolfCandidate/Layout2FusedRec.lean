import CommitGolfCandidate.Layout2FusedHead

/-! Fused opener, one position after the chain: the salt rows, the phase writer and the tail (`finish_facts`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2F
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.GroupedOpening TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolfCandidate.Layout2Phase (stride writerCarry)
open CommitGolfCandidate.Permutation.CounterSalt (coord)
open TwoPermutationPrototype.Sampling (saltWords)
open TwoPermutationPrototype.GroupedOpening.Layout2V2 (linkedSalts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
attribute [local simp] pc_of_set mem_of_set mem_of_reg open_zero
attribute [local simp] MachineState.getMem_setPC MachineState.getMem_setReg

/-! ### Salt rows -/

/-- The salt source (`x28 = readAt i`, inside the chain reply) and destination (the block). -/
theorem salt_addresses (i : Index) (ord : Nat) (hj : ord ≤ 16777216) :
    accessValid (readAt i) 8=true ∧ accessValid (readAt i+8) 8=true ∧
    accessValid (wordAddress (blockW ord)) 8=true ∧ accessValid (wordAddress (blockW ord+1)) 8=true ∧
    readAt i+8≠wordAddress (blockW ord) := by
  have hi : i.val<16777216:=i.isLt
  have r : rank i.val<11 := by unfold rank;omega
  have off : offAt i<200 ∧ offAt i%8=0 := by unfold offAt;split_ifs <;> constructor <;> omega
  have room := block_room ord hj
  have pb : proofBase=13824430176 := rfl
  unfold readAt wordAddress
  rw [show (8 : Word)=BitVec.ofNat 64 8 from rfl,←BitVec.ofNat_add]
  refine ⟨Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),
    Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),
    Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),
    Opening.aligned_access _ (by omega) (by unfold MEMORY_BYTES; omega),?_⟩
  intro eq
  have := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 1536+offAt i+8<2^64),
    Nat.mod_eq_of_lt (by omega : 8*blockW ord<2^64)] at this
  omega

/-- The block's salt words after the salt rows. -/
def saltInstalled (u : MachineState) (ord : Nat) (i : Index) : MachineState :=
  (u.setMem (wordAddress (blockW ord)) (u.getMem (readAt i))).setMem (wordAddress (blockW ord+1))
    (u.getMem (readAt i+8))

private theorem z12 : signExtend12 0#12=0#64 := by decide
private theorem e12 : signExtend12 8#12=8#64 := by decide

theorem salt_step (u : MachineState) (i : Index) (ord : Nat) (hj : ord ≤ 16777216)
    (pc : u.pc=address (4156+272*(ord%4))) (src : u.getReg .x28=readAt i)
    (cur : u.getReg .x21=BitVec.ofNat 64 (destOf ord)) :
    let v:=walkRows u (saltRows (ord%4))
    legal (saltRows (ord%4)) u ∧ v.pc=address (fwriterWord (ord%4)) ∧ v.mem=(saltInstalled u ord i).mem ∧
      (∀ k, k≠.x31 → v.getReg k=u.getReg k) := by
  intro v
  obtain ⟨ph,hph⟩ : ∃ ph, ord%4=ph := ⟨_,rfl⟩
  have hp : ph<4 := hph ▸ Nat.mod_lt _ (by decide)
  rw [hph] at pc
  obtain ⟨a0,a8,d0,d1,ne⟩ := salt_addresses i ord hj
  have d1' : u.getReg .x21+signExtend12 8#12=wordAddress (blockW ord+1) := by
    rw [cur, e12, show (8#64 : Word)=BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
    unfold wordAddress; congr 1; have := block_mul ord; omega
  have d0' : u.getReg .x21+signExtend12 0#12=wordAddress (blockW ord) := by
    rw [cur, z12, BitVec.add_zero, block_address]
  have s8 : u.getReg .x28+signExtend12 8#12=readAt i+8 := by rw [src, e12]; rfl
  have s0 : u.getReg .x28+signExtend12 0#12=readAt i := by rw [src, z12, BitVec.add_zero]
  have a8' : accessValid (readAt i+8#64) 8=true := a8
  have ne' : readAt i+8#64≠wordAddress (blockW ord) := ne
  have vdef : v=walkRows u (saltRows ph) := by rw [← hph]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hph]
    interval_cases ph <;>
    · simp [saltRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,address,a0,a8,a8',d0,d1,
        s0,s8,d0',d1']
      all_goals first | exact ⟨d1,ne⟩ | decide | skip
  · rw [vdef, hph]; unfold fwriterWord
    interval_cases ph <;> simp [saltRows,walkRows,execInstrBr,pc,address]
  · rw [vdef]
    simp [saltRows,walkRows,execInstrBr,saltInstalled,MachineState.getMem_setMem_ne ne',mem_of_store,s0,s8,d0',d1']
  · intro k h31; rw [vdef]; simp [saltRows,walkRows,execInstrBr,Ne.symm h31]

theorem salt_view (u : MachineState) (ord : Nat) (i : Index) (hj : ord ≤ 16777216) (w : Nat) (fit : w<2^33)
    (apart : w≠blockW ord ∧ w≠blockW ord+1) : memoryView (saltInstalled u ord i) w=memoryView u w := by
  have room := block_room ord hj
  have distinct (v : Nat) (hv : v<2^33) (ne : w≠v) : wordAddress w≠wordAddress v :=
    fun h => ne (wordAddress_injective_of_bound (by omega) (by omega) h)
  change (saltInstalled u ord i).getMem (wordAddress w)=_
  rw [saltInstalled,MachineState.getMem_setMem_ne (distinct _ (by omega) apart.2),
    MachineState.getMem_setMem_ne (distinct _ (by omega) apart.1)]; rfl

theorem salt_words_at (u : MachineState) (ord : Nat) (i : Index) (hj : ord ≤ 16777216) (j : Fin 2) :
    memoryView (saltInstalled u ord i) (blockW ord+j.val)=u.getMem (readAt i+BitVec.ofNat 64 (8*j.val)) := by
  have room := block_room ord hj
  have ne : wordAddress (blockW ord+1)≠wordAddress (blockW ord) :=
    fun h => (by have := wordAddress_injective_of_bound (by omega) (by omega) h; omega : False)
  change (saltInstalled u ord i).getMem (wordAddress (blockW ord+j.val))=_
  fin_cases j
  · simp only [saltInstalled, Fin.zero_eta, Fin.val_zero, Nat.add_zero, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]
    rw [MachineState.getMem_setMem_ne (Ne.symm ne), MachineState.getMem_setMem_eq]
  · simp only [saltInstalled, MachineState.getMem_setMem_eq]
    congr 1

/-! ### Record rows: salt, writer, tail -/

def finish (t : MachineState) (ord left : Nat) : MachineState := walkRows t (recRows (ord%4) (decide (left=1)))

def finalPC (ord left : Nat) := if left=1 then address (fexitWord (ord%4)) else address (fphaseWord ((ord+1)%4))

/-- The cap-leaf mark of position `i`. -/
def markAt (i : Index) : Word := BitVec.ofNat 64 (Opening.markBase+(256+i.val/65536))

/-- Words a position may write besides its mark byte: the generator counter (128), the scratch reply, its block. -/
def Writes (ord : Nat) (w : Nat) : Prop :=
  w=128 ∨ (192≤w ∧ w<217) ∨ (blockW ord≤w ∧ w<blockW ord+stride (ord%4)/8)

theorem index_at (j : Nat) : indexAt j=BitVec.ofNat 64 (indicesBase+8*j) := rfl

theorem stride_words (p : Nat) : stride p/8 ≤ 67 ∧ 25 ≤ stride p/8 ∧ 8*(stride p/8)=stride p := by
  unfold stride; split <;> decide

/-- The record rows from the end of the link block (`4156 + 272 ph`): the salt to `B+0..15`, the phase writer, the tail.
`t` is the state the chain left. -/
theorem finish_facts (t : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (bound : ord+left≤16777216)
    (pc : t.pc=address (4156+272*(ord%4))) (regs : Regs t ord left) (src : t.getReg .x28=readAt i)
    (cur : t.getReg .x21=BitVec.ofNat 64 (destOf ord)) (x6 : t.getReg .x6=BitVec.ofNat 64 i.val)
    (x18 : t.getReg .x18=wordAddress (nodeWordOf (i.val/4^^^1))) :
    let u:=finish t ord left
    let sv:=saltInstalled t ord i
    legal (recRows (ord%4) (decide (left=1))) t ∧ u.pc=finalPC ord left ∧
      u.getReg .x21=BitVec.ofNat 64 (destOf (ord+1)) ∧ u.getReg .x8=indexAt (ord+1) ∧
      u.getReg .x4=writerCarry (ord%4) (Layout2Phase.recordSource sv (quadAddress i.val) i.val) (t.getReg .x4) ∧
      (∀ k, k≠.x4 → k≠.x6 → k≠.x7 → k≠.x8 → k≠.x10 → k≠.x21 → k≠.x28 → k≠.x31 → u.getReg k=t.getReg k) ∧
      (∃ W : MachineState, u.mem=(W.setByte (markAt i) 1#8).mem ∧
        (∀ x : Word, x.toNat<destOf ord ∨ destOf ord+stride (ord%4) ≤ x.toNat → W.getMem x=sv.getMem x) ∧
        (∀ b<stride (ord%4), Layout2Phase2.written (i.val%4) (b/8) →
          W.getByte (BitVec.ofNat 64 (destOf ord+b))=
            Layout2Phase2.writtenByte (ord%4) (Layout2Phase.recordSource sv (quadAddress i.val) i.val) (t.getReg .x4) b) ∧
        (∀ b<stride (ord%4), Layout2Phase2.written (i.val%4) (b/8)=false →
          W.getByte (BitVec.ofNat 64 (destOf ord+b))=sv.getByte (BitVec.ofNat 64 (destOf ord+b)))) := by
  intro u sv
  have hj : ord ≤ 16777216 := by omega
  have hp : ord%4<4 := Nat.mod_lt _ (by decide)
  have ix : i.val<16777216 := i.isLt
  obtain ⟨sl,spc,smem,skeep⟩ := salt_step t i ord hj pc src cur
  set v:=walkRows t (saltRows (ord%4)) with hv
  have quad := quad_address_inside i.val (by unfold LENGTH LOG_LENGTH; omega)
  have db := dest_bound ord
  have mem36 : proofBase+534*(ord+1) ≤ MEMORY_BYTES := by
    have : proofBase+534*16777216 ≤ 68719476736 := by decide
    unfold MEMORY_BYTES; omega
  have vk (k : Reg) (h : k≠.x31 := by decide) : v.getReg k=t.getReg k := skeep k h
  have e3 : Layout2Writer3.Entry3 v (ord%4) i.val (destOf ord) (quadAddress i.val) (t.getReg .x4) :=
    { phase := hp, index := ix, posReg := (vk .x6).trans x6, dest := (vk .x21).trans cur,
      aligned := dest_aligned ord, room := ⟨by rw [record_base0]; exact db.1, by omega⟩,
      carry := vk .x4, heap := by rw [vk .x9, regs.heap, ← heap_base],
      leaves := (vk .x19).trans regs.leaves,
      ptr := by rw [vk .x18, x18, quad_address_node]; rfl,
      quad := ⟨quad.1, by rw [heap_base]; exact quad.2.1, by rw [salt_base]; exact quad.2.2⟩ }
  obtain ⟨wl,wpc,wbytes,wcarry,w6,wkeep,wframeB,wframe⟩ := Layout2Writer3.writer3_run (fwriterWord (ord%4)) e3 spc
  set W:=walkRows v (writerRowsF (ord%4)) with hW
  have wk (k : Reg) (h6 : k≠.x6) (h7 : k≠.x7) (h10 : k≠.x10) (h4 : k≠.x4) (h28 : k≠.x28) (h31 : k≠.x31) :
      W.getReg k=t.getReg k := (wkeep k h6 h7 h10 h4 h28 h31).trans (skeep k h31)
  have wpc' : W.pc=address (ftailWord (ord%4)) := wpc
  have dlast : decide (left=1)=decide (ord+1=ord+left) := by
    by_cases h : left=1 <;> simp [h] <;> omega
  obtain ⟨tl,tpc,t21,t8,tmem,tkeep⟩ := tail_step (ord%4) hp W (destOf ord) i.val ord (ord+left) wpc'
    (by rw [wk .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact cur)
    w6 ix
    (by rw [wk .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs.index, index_at])
    (by rw [wk .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs.endReg, index_at])
    (by omega) bound
    (by rw [wk .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs.base]; rfl)
    (by rw [wk .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), regs.mark]; rfl)
  have uEq : u=walkRows W (ftailRows (ord%4) (decide (ord+1=ord+left))) := by
    show walkRows t (recRows (ord%4) (decide (left=1)))=_
    rw [recRows, walk_join, walk_join, dlast]
  have svmem : sv.mem=v.mem := smem.symm
  have mb : MEMORY_BYTES=68719476736 := rfl
  have fx0 : ∀ b<stride (ord%4), destOf ord+b<2^64 := fun b hb => by omega
  refine ⟨?_,?_,?_,?_,?_,?_,⟨W,?_,?_,?_,?_⟩⟩
  · rw [recRows, dlast]
    exact legal_append _ _ _ (legal_append _ _ _ sl wl) (by rw [walk_join]; exact tl)
  · rw [uEq, tpc]; unfold finalPC
    by_cases h : left=1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, show (ord%4+1)%4=(ord+1)%4 by omega]
  · rw [uEq, t21, dest_next]
  · rw [uEq, t8, index_at]
  · rw [uEq, tkeep _ (by decide) (by decide) (by decide) (by decide)]
    exact wcarry.trans (by
      congr 1; funext k; simp only [Layout2Phase.recordSource, MachineState.getByte, MachineState.getMem, svmem])
  · intro k h4 h6 h7 h8 h10 h21 h28 h31
    rw [uEq, tkeep k h21 h6 h7 h8]; exact wk k h6 h7 h10 h4 h28 h31
  · rw [uEq]; exact tmem
  · intro x hx; exact (wframe x hx).trans (mem_reads v sv smem x)
  · intro b hb hw
    exact (wbytes b hb hw).trans (by
      congr 1; funext k; simp only [Layout2Phase.recordSource, MachineState.getByte, MachineState.getMem, svmem])
  · intro b hb hw
    have fx : destOf ord+b<2^64 := fx0 b hb
    exact (wframeB _ fx (fun h => by
      rw [show destOf ord+b-destOf ord=b by omega, hw] at h; exact Bool.false_ne_true h.2.2)).trans
      (byte_reads v sv smem _)


end TwoPermutationPrototype.GroupedOpening.Layout2F
