import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.K6Chain
import CommitGolfCandidate.GroupOpenTable

/-! Opener prefix, salt regeneration of one position on the linked (chain) schedule: rows
`chainStart .. chainStart+8` (3097..3105) and the link block at words 3106..3138, after which the salt rows
follow directly (3139). The head left `x3 = 16 i` and `x30 =` the table entry of `e = i % 4096`
(`GroupOpenTable`): it gives the counter offset `tabD e`, the chain entry `tabT e` (link-block word
`3139 - j`, `j = (e % 374) / 11` links after the keyed restart) and the salt source `tabS e = readAt i`:
```
ld x7,8(x30) ; slli x31,x3,4 ; add x7,x7,x31 ; sd x7,0(x10) ; lhu x28,2(x30) ; lhu x7,0(x30) ; ecall ;
addi x10,x12,0 ; jalr x0,0(x7) ; [3106..3138: 33 x ecall]
```
(the `jalr` enters the unrolled link block `j` words before its end, so link calls cost no ordinary instructions
and the last one falls through to the salt rows) the keyed generator call of head `h - j` (counter = base of its
C leaf, K1 input layout at word 128, reply at `[1536, 1736)`), then `j` in-place links on `[1536, 1736)`.
The counter arithmetic and the reply of the restart-plus-links walk are S9-K6P's `K6Chain.restart_counter` /
`K6Chain.opener_chain`. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
@[local simp] theorem chain_zero_reg (state : MachineState) : state.getReg .x0=0#64 := rfl

/-- First row of the chain block (the `remu x28,x6,x26`). -/
abbrev chainStart : Nat := 3097
/-- Links of position `i`: its head is `chainLinks i` heads after the keyed restart. -/
def chainLinks (i : Index) : Nat := ((i.val%4096)/11)%34
/-- Steps: 6 table/counter rows, the keyed call, 2 entry rows and one call per link. -/
def chainSteps (i : Index) : Nat := 9+chainLinks i
def chainCalls (i : Index) : Nat := 1+chainLinks i
/-- One cycle per ordinary row and 8 cycles per call. -/
def chainCycles (i : Index) : Nat := chainSteps i+7*chainCalls i

/-- The reply the chain ends with: the linked schedule's reply of the head of `i`. -/
noncomputable def chainReply (o : Oracle) (k : BitVec 192) (i : Index) : BitVec 1600 :=
  (Permutation.LinkedSalt.schedule Permutation.LinkedSalt.period).reply o.permutation
    Permutation.CounterSalt.input k (coord i).1

/-- State at the chain block (after the head of the position). -/
structure ChainEntry (h : MachineState) (i : Index) : Prop where
  pc : h.pc=address chainStart
  input : h.getReg .x10=1024
  output : h.getReg .x12=1536
  selector : h.getReg .x5=0
  width : h.getReg .x11=200
  primitive : h.getReg .x13=1
  idx : h.getReg .x6=BitVec.ofNat 64 i.val
  x3 : h.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat)
  entry : h.getReg .x30=wordAddress (tableWord (i.val%4096))
  table : TableAt h

/-- K1 generator input words 129..152 (word 128 is the counter): key words 1..3, then zeros. -/
def KeyWords (h : MachineState) (k : BitVec 192) : Prop :=
  ∀ j, 0<j → j<25 → memoryView h (128+j)=keyBlock k j

/-! ### Rows -/

def chainPreRows : List Row := [(3097,.LD .x7 .x30 8),(3098,.SLLI .x31 .x3 4),(3099,.ADD .x7 .x7 .x31),
  (3100,.SD .x10 .x7 0),(3101,.LHU .x28 .x30 2),(3102,.LHU .x7 .x30 0)]
def chainEnterRows : List Row := [(3104,.ADDI .x10 .x12 0),(3105,.JALR .x0 .x7 0)]
/-- First word after the unrolled link block: the salt rows. -/
abbrev linkEnd : Nat := 3139
/-- No exit rows: the link block falls through to the salt rows. -/
def chainExitRows : List Row := []

/-- `presentRows` for rows anywhere in the opener. -/
theorem rows_present_any (rows : List Row)
    (raw : ∀ i : Fin rows.length, rows[i].1<6144 ∧ (openingImage.code[rows[i].1]?).bind Opening.decodeBase=some rows[i].2) :
    presentRows rows := by
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact fun st pc => packed_fetch_far st _ _ (raw ⟨i,hi⟩).1 pc (raw ⟨i,hi⟩).2

theorem chain_pre_fetch : presentRows chainPreRows := by apply rows_present; decide +kernel
theorem chain_enter_fetch : presentRows chainEnterRows := by apply rows_present; decide +kernel
theorem chain_exit_fetch : presentRows chainExitRows := by intro p hp; simp [chainExitRows] at hp

theorem keyed_fetch (s : MachineState) (pc : s.pc=address 3103) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_far _ 3103 _ (by decide) pc (by decide +kernel)

private theorem link_words : ∀ k : Fin 33,
    (openingImage.code[3106+k.val]?).bind Opening.decodeBase=some .ECALL := by decide +kernel

/-- Words `linkEnd-c` (`1 ≤ c ≤ 33`) of the link block are `ecall`s. -/
theorem link_fetch (s : MachineState) (c : Nat) (lo : 0<c) (hc : c<34) (pc : s.pc=address (linkEnd-c)) :
    fetch openingImage s=some (.base .ECALL) := by
  refine packed_fetch_far _ (linkEnd-c) _ (by unfold linkEnd; omega) pc ?_
  have h := link_words ⟨33-c,by omega⟩
  rwa [show 3106+(33-c)=linkEnd-c by unfold linkEnd; omega] at h

theorem chain_lengths : chainPreRows.length=6 ∧ price chainPreRows=6 ∧
    chainEnterRows.length=2 ∧ price chainEnterRows=2 ∧ chainExitRows.length=0 ∧ price chainExitRows=0 := by decide

/-! ### Arithmetic of the counter rows -/

theorem tile_mask (i : Index) :
    BitVec.ofNat 64 i.val &&& 4095#64=BitVec.ofNat 64 (i.val%4096) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (4095#64).toNat=2^12-1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat]
  have hi : i.val<16777216 := i.isLt
  omega

theorem tile_shift (i : Index) :
    (BitVec.ofNat 64 i.val <<< 52) >>> 52=BitVec.ofNat 64 (i.val%4096) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

theorem remu_374 (i : Index) :
    rv64_remu (BitVec.ofNat 64 (i.val%4096)) 374#64=BitVec.ofNat 64 ((i.val%4096)%374) := by
  unfold rv64_remu
  apply BitVec.eq_of_toNat_eq
  have h : i.val%4096<4096:=Nat.mod_lt _ (by decide)
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat] <;> omega

theorem divu_11 (i : Index) :
    rv64_divu (BitVec.ofNat 64 ((i.val%4096)%374)) 11#64=BitVec.ofNat 64 (((i.val%4096)%374)/11) := by
  unfold rv64_divu
  apply BitVec.eq_of_toNat_eq
  have h : (i.val%4096)%374<374:=Nat.mod_lt _ (by decide)
  simp [BitVec.toNat_udiv,BitVec.toNat_ofNat] <;> omega

theorem remu_11 (i : Index) :
    rv64_remu (BitVec.ofNat 64 ((i.val%4096)%374)) 11#64=BitVec.ofNat 64 (((i.val%4096)%374)%11) := by
  unfold rv64_remu
  apply BitVec.eq_of_toNat_eq
  have h : (i.val%4096)%374<374:=Nat.mod_lt _ (by decide)
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat] <;> omega

theorem mod374_head (i : Index) : ((i.val%4096)%374)/11=chainLinks i := by
  unfold chainLinks; omega
theorem mod374_rank (i : Index) : ((i.val%4096)%374)%11=rank i.val := by
  unfold rank; omega
theorem mod374_addr (i : Index) :
    i.val-((i.val%4096)%374)+1=i.val-(i.val%4096)%11-11*chainLinks i+1 := by
  have h1 : ((i.val%4096)%374)/11=((i.val%4096)/11)%34 := by omega
  have h2 : ((i.val%4096)%374)%11=(i.val%4096)%11 := by omega
  have h3 : (i.val%4096)%374=11*((i.val%4096)%374/11)+((i.val%4096)%374)%11 := by
    omega
  unfold chainLinks
  omega

theorem links_lt (i : Index) : chainLinks i<34 := by unfold chainLinks; omega

theorem slli_two (n : Nat) : BitVec.ofNat 64 n <<< (2:Nat)=BitVec.ofNat 64 (4*n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]
  omega

/-! ### The counter rows -/

def chainBefore (h : MachineState) := walkRows h chainPreRows

theorem chain_counter (i : Index) :
    ((((BitVec.ofNat 64 i.val - BitVec.ofNat 64 ((i.val%4096)%374)) + 1#64) <<< (8:Nat)) + 4096#64)
      = Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1) := by
  have hi : i.val<16777216 := i.isLt
  have hm : (((i.val % 4096) % 374) ≤ i.val) := by omega
  have hsub : BitVec.ofNat 64 i.val - BitVec.ofNat 64 ((i.val%4096)%374)
      = BitVec.ofNat 64 (i.val - ((i.val%4096)%374)) :=
    BitVec.ofNat_sub_ofNat_of_le (i.val) ((i.val%4096)%374) (by omega) hm
  rw [hsub,← BitVec.ofNat_add]
  rw [show BitVec.ofNat 64 (i.val - (i.val % 4096) % 374 + 1) <<< (8:Nat)
      = BitVec.ofNat 64 ((i.val - (i.val % 4096) % 374 + 1)*256) by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq]]
  rw [← BitVec.ofNat_add]
  unfold Permutation.CounterSalt.ctr
  rw [K6Chain.restart_first_leaf]
  congr 1
  have hh := mod374_addr i
  unfold chainLinks at hh
  rw [hh]
  simp only [K6Chain.links,chainLinks,K6Chain.head]
  omega

theorem chain_counter' (i : Index) :
    ((((BitVec.ofNat 64 i.val - BitVec.ofNat 64 ((i.val%4096)%374)) <<< (8:Nat)) + 256#64) + 4096#64)
      = Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1) := by
  have h1 : ((BitVec.ofNat 64 i.val - BitVec.ofNat 64 ((i.val%4096)%374) + 1#64) <<< (8:Nat))
      = ((BitVec.ofNat 64 i.val - BitVec.ofNat 64 ((i.val%4096)%374)) <<< (8:Nat)) + 256#64 := by
    rw [BitVec.shiftLeft_add_distrib]
    norm_num
  rw [←h1]
  simpa only [Nat.add_assoc] using chain_counter i

/-- The counter with `x2 = 4352 = 256 + 4096` (row 784). -/
theorem chain_counter_sp (i : Index) :
    (((BitVec.ofNat 64 i.val - BitVec.ofNat 64 ((i.val%4096)%374)) <<< (8:Nat)) + 4352#64)
      = Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1) := by
  rw [← chain_counter' i, BitVec.add_assoc, show (256#64 + 4096#64 : BitVec 64) = 4352#64 by decide]

/-! ### The table rows -/

/-- `16 i & 65520 = 16 (i % 4096)` (row 778). -/
theorem tile16 (i : Index) :
    (BitVec.ofNat 64 i.val <<< (4:Nat)) &&& 65520#64=BitVec.ofNat 64 (16*(i.val%4096)) := by
  rw [show (65520#64 : BitVec 64)=4095#64 <<< (4:Nat) by decide, ← BitVec.shiftLeft_and_distrib, tile_mask i]
  apply BitVec.eq_of_toNat_eq
  have hi : i.val<16777216 := i.isLt
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The entry address (row 779). -/
theorem entry_address (e : Nat) (he : e<4096) :
    BitVec.ofNat 64 (16*e)+BitVec.ofNat 64 tableBase=wordAddress (tableWord e) := by
  rw [← BitVec.ofNat_add]; unfold wordAddress; congr 1; simp only [tableBase, tableWord]; omega

/-- `256 i + tabD (i % 4096)` is the keyed generator's counter (rows 781..782). -/
theorem counter_table (i : Index) :
    BitVec.ofNat 64 (tabD (i.val%4096))+((BitVec.ofNat 64 i.val <<< (4:Nat)) <<< (4:Nat))
      =Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1) := by
  rw [← chain_counter_sp i]
  have hi : i.val<16777216 := i.isLt
  have hm : (i.val%4096)%374 ≤ i.val := by omega
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, tabD]
  omega

private def preB : List Row := [(3097,.LD .x7 .x30 8),(3098,.SLLI .x31 .x3 4),(3099,.ADD .x7 .x7 .x31),
  (3100,.SD .x10 .x7 0)]
private def preC : List Row := [(3101,.LHU .x28 .x30 2),(3102,.LHU .x7 .x30 0)]
private theorem pre_split : chainPreRows=preB++preC := rfl

private theorem pre_b (a : MachineState) (i : Index) (pc : a.pc=address 3097)
    (x3 : a.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat)) (x30 : a.getReg .x30=wordAddress (tableWord (i.val%4096)))
    (x10 : a.getReg .x10=1024) (d : a.getMem (wordAddress (tableWord (i.val%4096)+1))=BitVec.ofNat 64 (tabD (i.val%4096))) :
    let b:=walkRows a preB
    legal preB a ∧ b.pc=address 3101 ∧
      b.mem=(a.setMem 1024 (Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1))).mem ∧
      b.getReg .x3=a.getReg .x3 ∧ b.getReg .x30=a.getReg .x30 ∧
      (∀ r, r≠.x7 → r≠.x31 → b.getReg r=a.getReg r) := by
  have hi : i.val<16777216 := i.isLt
  have e8 : wordAddress (tableWord (i.val%4096))+signExtend12 8#12=wordAddress (tableWord (i.val%4096)+1) := by
    rw [show signExtend12 8#12=BitVec.ofNat 64 8 by decide]; unfold wordAddress
    rw [← BitVec.ofNat_add]; congr 1
  have ld : accessValid (wordAddress (tableWord (i.val%4096)+1)) 8=true :=
    table_access _ 8 (by simp only [tableWord]; omega) (by simp only [tableWord]; omega)
  have st : accessValid (1024#64) 8=true := Opening.aligned_access 1024 (by decide) (by decide)
  have val : a.getMem (a.getReg .x30+signExtend12 8#12)+(a.getReg .x3 <<< (4:Nat))=
      Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1) := by
    rw [x30, e8, d, x3]; exact counter_table i
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp [preB,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,x30,x10,e8,ld,st,address,
      show signExtend12 0#12=0#64 by decide]
  · simp [preB,walkRows,execInstrBr,pc,address]
  · simp [preB,walkRows,execInstrBr,mem_of_store]
    simp only [val, x10, show signExtend12 0#12=0#64 by decide, BitVec.add_zero]
    rfl
  · simp [preB,walkRows,execInstrBr]
  · simp [preB,walkRows,execInstrBr]
  · intro r a b; simp [preB,walkRows,execInstrBr,Ne.symm a,Ne.symm b]

theorem half_setPC (s : MachineState) (p a : Word) : (s.setPC p).getHalfword a=s.getHalfword a := rfl
theorem half_setReg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getHalfword a=s.getHalfword a := by
  cases r <;> rfl

private theorem pre_c (b : MachineState) (i : Index) (pc : b.pc=address 3101)
    (x30 : b.getReg .x30=wordAddress (tableWord (i.val%4096)))
    (w0 : b.getMem (wordAddress (tableWord (i.val%4096)))=BitVec.ofNat 64 (tabEntry (i.val%4096) 0)) :
    let c:=walkRows b preC
    legal preC b ∧ c.pc=address 3103 ∧ c.mem=b.mem ∧ c.getReg .x28=BitVec.ofNat 64 (tabS (i.val%4096)) ∧
      c.getReg .x7=BitVec.ofNat 64 (tabT (i.val%4096)) ∧ (∀ r, r≠.x7 → r≠.x28 → c.getReg r=b.getReg r) := by
  have hi : i.val<16777216 := i.isLt
  have fit : 8*tableWord (i.val%4096)+8 ≤ 2^64 := by simp only [tableWord]; omega
  have a2 : wordAddress (tableWord (i.val%4096))+signExtend12 2#12=BitVec.ofNat 64 (8*tableWord (i.val%4096)+2*1) := by
    rw [show signExtend12 2#12=BitVec.ofNat 64 2 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add]
  have a0 : wordAddress (tableWord (i.val%4096))+signExtend12 0#12=BitVec.ofNat 64 (8*tableWord (i.val%4096)+2*0) := by
    rw [show signExtend12 0#12=BitVec.ofNat 64 0 by decide]; unfold wordAddress; rw [← BitVec.ofNat_add]
  have low : tabEntry (i.val%4096) 0=tabT (i.val%4096)+65536*tabS (i.val%4096)+4294967296*tabR (i.val%4096)+
      281474976710656*tabG (i.val%4096) := by simp [tabEntry]
  have h28 : (b.getHalfword (wordAddress (tableWord (i.val%4096))+signExtend12 2#12)).zeroExtend 64=
      BitVec.ofNat 64 (tabS (i.val%4096)) := by
    rw [a2, table_half b _ 1 fit (by decide)]
    change ((b.getMem (wordAddress (tableWord (i.val%4096))) >>> (1*16)).truncate 16).zeroExtend 64=_
    rw [w0, low]
    exact half1 _ _ _ _ (tab_t_lt _) (tab_s_lt _) (tab_r_lt _) (tab_g_lt _)
  have h7 : (b.getHalfword (wordAddress (tableWord (i.val%4096))+signExtend12 0#12)).zeroExtend 64=
      BitVec.ofNat 64 (tabT (i.val%4096)) := by
    rw [a0, table_half b _ 0 fit (by decide)]
    change ((b.getMem (wordAddress (tableWord (i.val%4096))) >>> (0*16)).truncate 16).zeroExtend 64=_
    rw [w0, low]
    exact half0 _ _ _ _ (tab_t_lt _) (tab_s_lt _) (tab_r_lt _) (tab_g_lt _)
  have v2 : accessValid (wordAddress (tableWord (i.val%4096))+signExtend12 2#12) 2=true := by
    rw [a2]; exact table_access _ 2 (by omega) (by simp only [tableWord]; omega)
  have v0 : accessValid (wordAddress (tableWord (i.val%4096))+signExtend12 0#12) 2=true := by
    rw [a0]; exact table_access _ 2 (by omega) (by simp only [tableWord]; omega)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp [preC,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,x30,v2,v0,address]
  · simp [preC,walkRows,execInstrBr,pc,address]
  · simp [preC,walkRows,execInstrBr]
  · have c1 : (walkRows b preC).getReg .x28=(b.getHalfword (b.getReg .x30+signExtend12 2#12)).zeroExtend 64 := rfl
    rw [c1, x30]; exact h28
  · have c2 : (walkRows b preC).getReg .x7=(b.getHalfword (b.getReg .x30+signExtend12 0#12)).zeroExtend 64 := rfl
    rw [c2, x30]; exact h7
  · intro r a c; simp [preC,walkRows,execInstrBr,Ne.symm a,Ne.symm c]

theorem chain_before (h : MachineState) (i : Index) (e : ChainEntry h i) :
    let t:=chainBefore h
    legal chainPreRows h ∧ t.pc=address 3103 ∧ t.getReg .x28=BitVec.ofNat 64 (tabS (i.val%4096)) ∧
      t.getReg .x7=BitVec.ofNat 64 (tabT (i.val%4096)) ∧
      t.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) ∧
      t.mem=(h.setMem 1024 (Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1))).mem ∧
      (∀ r, r≠.x3 → r≠.x7 → r≠.x28 → r≠.x30 → r≠.x31 → t.getReg r=h.getReg r) := by
  dsimp only
  have hi : i.val<16777216 := i.isLt
  have he : i.val%4096<4096 := Nat.mod_lt _ (by decide)
  have d : h.getMem (wordAddress (tableWord (i.val%4096)+1))=BitVec.ofNat 64 (tabD (i.val%4096)) := by
    have t1 := e.table _ he 1 (by decide)
    simp only [tabEntry, show (1:Nat)≠0 by decide, if_false] at t1
    exact t1
  obtain ⟨lb,bpc,bmem,b3,b30,bkeep⟩ := pre_b h i e.pc e.x3 e.entry e.input d
  have ne : wordAddress (tableWord (i.val%4096))≠(1024 : Word) := by
    intro eq
    have := wordAddress_injective_of_bound (a:=tableWord (i.val%4096)) (b:=128) (by simp only [tableWord]; omega)
      (by decide) eq
    simp only [tableWord] at this; omega
  have w0 : (walkRows h preB).getMem (wordAddress (tableWord (i.val%4096)))=
      BitVec.ofNat 64 (tabEntry (i.val%4096) 0) := by
    change (walkRows h preB).mem _=_
    rw [bmem]
    change (h.setMem 1024 _).getMem _=_
    rw [MachineState.getMem_setMem_ne ne]
    have t0 := e.table _ he 0 (by decide)
    rw [Nat.add_zero] at t0
    exact t0
  obtain ⟨lc,cpc,cmem,c28,c7,ckeep⟩ := pre_c (walkRows h preB) i bpc (b30.trans e.entry) w0
  have split : chainBefore h=walkRows (walkRows h preB) preC := by
    unfold chainBefore; rw [pre_split, walk_join]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [pre_split]
    exact legal_append _ _ _ lb lc
  · rw [split]; exact cpc
  · rw [split]; exact c28
  · rw [split]; exact c7
  · rw [split, ckeep _ (by decide) (by decide), b3]; exact e.x3
  · rw [split, cmem, bmem]
  · intro r r3 r7 r28 r30 r31
    rw [split, ckeep r r7 r28, bkeep r r7 r31]

/-! ### The link loop -/

def linkQuery (s : MachineState) := packBuffer (window (memoryView s) 192)

/-- `c` in-place links from a state in the link block: query the reply window, write the answer back
(the `ecall` only moves the PC by one word). -/
def linkTrace : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | c+1,s => do
      let z ← World.query (.inr (.inr (.inl (linkQuery s))))
      linkTrace c (writeBits s (wordAddress 192) z)

/-- One in-place link with the oracle fixed. -/
noncomputable def linkStep (o : Oracle) (s : MachineState) : MachineState :=
  writeBits s (wordAddress 192) (o.permutation (linkQuery s))

/-- `c` in-place links with the oracle fixed (an iterate, so unfolding never reduces the reply write). -/
noncomputable def linkState (o : Oracle) (c : Nat) (s : MachineState) : MachineState := (linkStep o)^[c] s

theorem linkState_zero (o : Oracle) (s : MachineState) : linkState o 0 s=s := rfl

theorem linkState_succ (o : Oracle) (c : Nat) (s : MachineState) :
    linkState o (c+1) s=linkState o c (linkStep o s) := Function.iterate_succ_apply _ _ _

/-- Registers the link block relies on, with `c` links still to go (PC `c` words before `linkEnd`). -/
structure LinkReady (s : MachineState) (c : Nat) : Prop where
  pc : s.pc=address (linkEnd-c)
  input : s.getReg .x10=1536
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1

/-- A reply write moves the PC by one row and keeps every register. -/
theorem write_pc {bits : Nat} (s : MachineState) (dst : Word) (z : BitVec bits) :
    (writeBits s dst z).pc=s.pc+4 := by simp only [writeBits,MachineState.setPC]

/-! ### The block -/

/-- The keyed generator query (counter word 128, key words 129..131, zeros). -/
def keyedQuery (h : MachineState) := packBuffer (window (memoryView (chainBefore h)) 128)

/-- The block's oracle trace: the keyed call, then `chainLinks i` in-place links; returns the state at
`chainStart+14`. -/
def chainTrace (h : MachineState) (i : Index) : OracleComp World MachineState := do
  let z ← World.query (.inr (.inr (.inl (keyedQuery h))))
  let b ← linkTrace (chainLinks i) (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows)
  return walkRows b chainExitRows

/-- The block's result when the oracle is fixed. -/
noncomputable def chainState (o : Oracle) (h : MachineState) (i : Index) : MachineState :=
  walkRows (linkState o (chainLinks i)
    (walkRows (writeBits (chainBefore h) (wordAddress 192) (o.permutation (keyedQuery h))) chainEnterRows))
    chainExitRows

theorem after_keyed {bits : Nat} (h : MachineState) (i : Index) (e : ChainEntry h i) (z : BitVec bits) :
    let a:=writeBits (chainBefore h) (wordAddress 192) z
    a.pc=address 3104 ∧ (∀ x, x≠.x3 → x≠.x7 → x≠.x28 → x≠.x30 → x≠.x31 → a.getReg x=h.getReg x) ∧
      a.getReg .x28=BitVec.ofNat 64 (tabS (i.val%4096)) ∧ a.getReg .x7=BitVec.ofNat 64 (tabT (i.val%4096)) ∧
      a.getReg .x3=BitVec.ofNat 64 i.val <<< (4:Nat) := by
  obtain ⟨_,pc,r28,r7,r3,_,keep⟩ := chain_before h i e
  have regs (x : Reg) : (writeBits (chainBefore h) (wordAddress 192) z).getReg x=(chainBefore h).getReg x :=
    writeBits_register ..
  refine ⟨?_,fun x a b c d f => (regs x).trans (keep x a b c d f),(regs _).trans r28,(regs _).trans r7,(regs _).trans r3⟩
  rw [write_pc,pc]; exact address_succ 3103

/-- The entry target: `tabT e & ~1 = address (linkEnd - c)`. -/
theorem enter_target (c : Nat) (hc : c<34) :
    (BitVec.ofNat 64 (4096+4*(3139-c))+signExtend12 0#12) &&& ~~~1#64=address (linkEnd-c) := by
  interval_cases c <;> decide

theorem tab_t_links (i : Index) : tabT (i.val%4096)=4096+4*(3139-chainLinks i) := by
  unfold tabT chainLinks; congr 2; omega

theorem enter_walk (a : MachineState) :
    walkRows a chainEnterRows =
      ((a.setReg .x10 (a.getReg .x12+0)).setPC ((a.getReg .x7+signExtend12 0#12) &&& ~~~1#64)) := rfl

theorem enter_rows (a : MachineState) (c : Nat) (pc : a.pc=address 3104)
    (target : a.getReg .x7=BitVec.ofNat 64 (4096+4*(3139-c))) (hc : c<34) :
    legal chainEnterRows a ∧ (walkRows a chainEnterRows).pc=address (linkEnd-c) ∧
      (walkRows a chainEnterRows).getReg .x10=a.getReg .x12 ∧
      (∀ x, x≠.x10 → (walkRows a chainEnterRows).getReg x=a.getReg x) ∧
      (walkRows a chainEnterRows).mem=a.mem := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine ⟨pc,rfl,?_,rfl,trivial⟩
    change a.pc+4=address 3105
    rw [pc];rfl
  · rw [enter_walk,pc_of_set,target]
    exact enter_target c hc
  · rw [enter_walk]
    simp
  · intro x h10
    rw [enter_walk]
    simp [Ne.symm h10]
  · rw [enter_walk]
    rfl

end TwoPermutationPrototype.GroupedOpening
