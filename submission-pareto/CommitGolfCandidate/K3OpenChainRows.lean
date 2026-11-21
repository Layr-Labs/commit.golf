import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.K6Chain

/-! Opener prefix, salt regeneration of one position on the linked (chain) schedule: rows
`chainStart .. chainStart+12` (777..789) and the link block at words 896..929, whose `jal` returns to row 791. The header
sets `x18 = 8192` (row 715), `x3 = 374` (`gp`), `x2 = 4352` (`sp`), and `x1 = 4095` once (rows 755..757); no opener row writes them afterwards. With `n = i % 4096`, `r = n % 11` (rank), `h = n / 11` (head in the tile),
`j = h % 34` (links after the keyed restart):
```
and x30,x6,x1 ; remu x31,x30,x3 ; divu x30,x31,x29 ; remu x28,x31,x29 ;
sub x7,x6,x31 ; slli x7,x7,8 ; add x7,x7,x2 ; sd x7,0(x10) ; slli x31,x30,2 ; ecall ;
sub x7,x18,x31 ; addi x10,x12,0 ; jalr x0,-380(x7) ;
[896..928: 33 x ecall] ; 929: jal x0,<791>
```
(the `jalr` enters the unrolled link block `j` words before its end, so link calls cost no ordinary instructions)
the keyed generator call of head `h - j` (counter = base of its C leaf, K1 input layout at word 128, reply at
`[1536, 1736)`), then `j` in-place links on `[1536, 1736)`. The counter arithmetic and the reply of the
restart-plus-links walk are S9-K6P's `K6Chain.restart_counter` / `K6Chain.opener_chain`. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
@[local simp] theorem chain_zero_reg (state : MachineState) : state.getReg .x0=0#64 := rfl

/-- First row of the chain block (the `remu x28,x6,x26`). -/
abbrev chainStart : Nat := 777
/-- Links of position `i`: its head is `chainLinks i` heads after the keyed restart. -/
def chainLinks (i : Index) : Nat := ((i.val%4096)/11)%34
/-- Steps: 9 counter rows, the keyed call, 3 entry rows, one call per link and the `jal` back to row 791. -/
def chainSteps (i : Index) : Nat := 14+chainLinks i
def chainCalls (i : Index) : Nat := 1+chainLinks i
/-- One `remu`, one `divu`, one `remu` (4 cycles each) and 8 cycles per call. -/
def chainCycles (i : Index) : Nat := chainSteps i+9+7*chainCalls i

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
  base : h.getReg .x26=4096
  divReg : h.getReg .x29=11
  idx : h.getReg .x6=BitVec.ofNat 64 i.val
  gp : h.getReg .x3=374
  sp : h.getReg .x2=4352
  mask : h.getReg .x1=4095
  linkBase : h.getReg .x18=8192

/-- K1 generator input words 129..152 (word 128 is the counter): key words 1..3, then zeros. -/
def KeyWords (h : MachineState) (k : BitVec 192) : Prop :=
  ∀ j, 0<j → j<25 → memoryView h (128+j)=keyBlock k j

/-! ### Rows -/

def chainPreRows : List Row := [(777,.AND .x30 .x6 .x1),
  (778,.REMU .x31 .x30 .x3),(779,.DIVU .x30 .x31 .x29),(780,.REMU .x28 .x31 .x29),
  (781,.SUB .x7 .x6 .x31),(782,.SLLI .x7 .x7 8),(783,.ADD .x7 .x7 .x2),
  (784,.SD .x10 .x7 0),(785,.SLLI .x31 .x30 2)]
def chainEnterRows : List Row := [(787,.SUB .x7 .x18 .x31),
  (788,.ADDI .x10 .x12 0),(789,.JALR .x0 .x7 3716)]
/-- First word after the unrolled link block (the `jal` back to the exit row). -/
abbrev linkEnd : Nat := 929
def chainExitRows : List Row := [(929,.JAL .x0 2096600)]

/-- `presentRows` for rows anywhere in the opener (`rows_present` stops at 813). -/
theorem rows_present_any (rows : List Row)
    (raw : ∀ i : Fin rows.length, rows[i].1<1062 ∧ (openingImage.code[rows[i].1]?).bind Opening.decodeBase=some rows[i].2) :
    presentRows rows := by
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact fun st pc => packed_fetch_base_any st _ _ (raw ⟨i,hi⟩).1 pc (raw ⟨i,hi⟩).2

theorem chain_pre_fetch : presentRows chainPreRows := by apply rows_present; decide +kernel
theorem chain_enter_fetch : presentRows chainEnterRows := by apply rows_present; decide +kernel
theorem chain_exit_fetch : presentRows chainExitRows := by apply rows_present_any; decide +kernel

theorem keyed_fetch (s : MachineState) (pc : s.pc=address 786) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_base _ 786 _ (by decide) pc (by decide +kernel)

private theorem link_words : ∀ k : Fin 33,
    (openingImage.code[896+k.val]?).bind Opening.decodeBase=some .ECALL := by decide +kernel

/-- Words `linkEnd-c` (`1 ≤ c ≤ 33`) of the link block are `ecall`s. -/
theorem link_fetch (s : MachineState) (c : Nat) (lo : 0<c) (hc : c<34) (pc : s.pc=address (linkEnd-c)) :
    fetch openingImage s=some (.base .ECALL) := by
  refine packed_fetch_base_any _ (linkEnd-c) _ (by unfold linkEnd; omega) pc ?_
  have h := link_words ⟨33-c,by omega⟩
  rwa [show 896+(33-c)=linkEnd-c by unfold linkEnd; omega] at h

theorem chain_lengths : chainPreRows.length=9 ∧ price chainPreRows=18 ∧
    chainEnterRows.length=3 ∧ price chainEnterRows=3 ∧ chainExitRows.length=1 ∧ price chainExitRows=1 := by decide

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

theorem chain_before (h : MachineState) (i : Index) (e : ChainEntry h i) :
    let t:=chainBefore h
    legal chainPreRows h ∧ t.pc=address 786 ∧ t.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧
      t.getReg .x30=BitVec.ofNat 64 (chainLinks i) ∧
      t.getReg .x31=BitVec.ofNat 64 (4*chainLinks i) ∧
      t.mem=(h.setMem 1024 (Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1))).mem ∧
      (∀ r, r≠.x7 → r≠.x28 → r≠.x30 → r≠.x31 → t.getReg r=h.getReg r) := by
  dsimp only
  have pc0 : h.pc=address 777 := e.pc
  have simple (r : Reg) (a : r≠.x7) (b : r≠.x28) (c : r≠.x30) (d : r≠.x31) :
      (chainBefore h).getReg r=h.getReg r := by
    simp [chainBefore,walkRows,chainPreRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d]
  refine ⟨?_,?_,?_,?_,?_,?_,simple⟩
  · simp [chainPreRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc0,e.input,
      Opening.aligned_access 1024 (by decide) (by decide),show signExtend12 0#12=0#64 by decide,address]
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,pc0,address]
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,e.idx,e.divReg,e.gp,e.mask]
    simp only [tile_mask i,remu_374 i,remu_11 i,mod374_rank i]
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,e.idx,e.divReg,e.gp,e.mask]
    simp only [tile_mask i,remu_374 i,divu_11 i,mod374_head i]
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,e.idx,e.divReg,e.gp,e.mask]
    simp only [tile_mask i,remu_374 i,divu_11 i]
    rw [slli_two]
    congr 1
    rw [mod374_head i]
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,e.idx,e.divReg,e.gp,e.sp,e.mask,e.input,mem_of_store,
      show signExtend12 0#12=0#64 by decide,address]
    simp only [tile_mask i,remu_374 i,divu_11 i]
    rw [chain_counter_sp i]

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
    a.pc=address 787 ∧ (∀ x, x≠.x7 → x≠.x28 → x≠.x30 → x≠.x31 → a.getReg x=h.getReg x) ∧
      a.getReg .x30=BitVec.ofNat 64 (chainLinks i) ∧ a.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧
      a.getReg .x31=BitVec.ofNat 64 (4*chainLinks i) := by
  obtain ⟨_,pc,r28,r30,r31,_,keep⟩ := chain_before h i e
  have regs (x : Reg) : (writeBits (chainBefore h) (wordAddress 192) z).getReg x=(chainBefore h).getReg x :=
    writeBits_register ..
  refine ⟨?_,fun x a b c d => (regs x).trans (keep x a b c d),(regs _).trans r30,(regs _).trans r28,(regs _).trans r31⟩
  rw [write_pc,pc]; exact address_succ 786

/-- The entry target: `(8192 - 4c - 380) & ~1 = address (linkEnd - c)`. -/
theorem enter_target (c : Nat) (hc : c<34) :
    (8192#64-(BitVec.ofNat 64 c <<< (2#6).toNat)
      +signExtend12 3716#12) &&& ~~~1#64=address (linkEnd-c) := by
  interval_cases c <;> decide

theorem enter_walk (a : MachineState) :
    walkRows a chainEnterRows =
      (((a.setReg .x7 (a.getReg .x18-a.getReg .x31)).setReg .x10 (a.getReg .x12+0)).setPC
        ((a.getReg .x18-a.getReg .x31+signExtend12 3716#12) &&& ~~~1#64)) := rfl

theorem enter_rows (a : MachineState) (c : Nat) (pc : a.pc=address 787)
    (cnt : a.getReg .x31=BitVec.ofNat 64 c <<< (2#6).toNat) (base : a.getReg .x18=8192) (hc : c<34) :
    legal chainEnterRows a ∧ (walkRows a chainEnterRows).pc=address (linkEnd-c) ∧
      (walkRows a chainEnterRows).getReg .x10=a.getReg .x12 ∧
      (∀ x, x≠.x7 → x≠.x10 → x≠.x31 → (walkRows a chainEnterRows).getReg x=a.getReg x) ∧
      (walkRows a chainEnterRows).mem=a.mem := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine ⟨pc,rfl,?_,rfl,?_,rfl,trivial⟩
    · change a.pc+4=address 788
      rw [pc];rfl
    · change a.pc+4+4=address 789
      rw [pc];rfl
  · rw [enter_walk,pc_of_set,base,cnt]
    exact enter_target c hc
  · rw [enter_walk]
    simp
  · intro x h7 h10 h31
    rw [enter_walk]
    simp [Ne.symm h7,Ne.symm h10]
  · rw [enter_walk]
    rfl

end TwoPermutationPrototype.GroupedOpening
