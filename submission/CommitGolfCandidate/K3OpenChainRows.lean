import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.K6Chain

/-! Opener prefix, salt regeneration of one position on the linked (chain) schedule: rows
`chainStart .. chainStart+18`. With `n = i % 4096`, `r = n % 11` (rank), `h = n / 11` (head in the tile),
`j = h % 34` (links after the keyed restart):
```
remu x28,x6,x26 ; divu x30,x28,x29 ; remu x28,x28,x29 ; addi x31,x0,34 ; remu x30,x30,x31 ; mul x31,x30,x29 ;
sub x7,x6,x28 ; sub x7,x7,x31 ; addi x7,x7,1 ; slli x7,x7,8 ; add x7,x7,x26 ; sd x7,0(x10) ; ecall ;
beq x30,x0,+24 ; addi x10,x12,0 ; L: ecall ; addi x30,x30,-1 ; bne x30,x0,L ; addi x10,x0,1024
```
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
/-- Steps: 14 rows and calls without links (`beq` taken), else 16 + 3 per link. -/
def chainSteps (i : Index) : Nat := if chainLinks i=0 then 14 else 16+3*chainLinks i
def chainCalls (i : Index) : Nat := 1+chainLinks i
/-- Three `remu`, one `divu`, one `mul` (4 cycles each) and 8 cycles per call. -/
def chainCycles (i : Index) : Nat := chainSteps i+15+7*chainCalls i

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

/-- K1 generator input words 129..152 (word 128 is the counter): key words 1..3, then zeros. -/
def KeyWords (h : MachineState) (k : BitVec 192) : Prop :=
  ∀ j, 0<j → j<25 → memoryView h (128+j)=keyBlock k j

/-! ### Rows -/

def chainPreRows : List Row := [(777,.REMU .x28 .x6 .x26),(778,.DIVU .x30 .x28 .x29),(779,.REMU .x28 .x28 .x29),
  (780,.ADDI .x31 .x0 34),(781,.REMU .x30 .x30 .x31),(782,.MUL .x31 .x30 .x29),(783,.SUB .x7 .x6 .x28),
  (784,.SUB .x7 .x7 .x31),(785,.ADDI .x7 .x7 1),(786,.SLLI .x7 .x7 8),(787,.ADD .x7 .x7 .x26),(788,.SD .x10 .x7 0)]
def chainSkipRows : List Row := [(790,.BEQ .x30 .x0 24)]
def chainEnterRows : List Row := [(790,.BEQ .x30 .x0 24),(791,.ADDI .x10 .x12 0)]
def chainLinkRows : List Row := [(793,.ADDI .x30 .x30 (-1)),(794,.BNE .x30 .x0 8184)]
def chainExitRows : List Row := [(795,.ADDI .x10 .x0 1024)]

theorem chain_pre_fetch : presentRows chainPreRows := by apply rows_present; decide +kernel
theorem chain_skip_fetch : presentRows chainSkipRows := by apply rows_present; decide +kernel
theorem chain_enter_fetch : presentRows chainEnterRows := by apply rows_present; decide +kernel
theorem chain_link_fetch : presentRows chainLinkRows := by apply rows_present; decide +kernel
theorem chain_exit_fetch : presentRows chainExitRows := by apply rows_present; decide +kernel

theorem keyed_fetch (s : MachineState) (pc : s.pc=address 789) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_base _ 789 _ (by decide) pc (by decide +kernel)

theorem link_fetch (s : MachineState) (pc : s.pc=address 792) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_base _ 792 _ (by decide) pc (by decide +kernel)

theorem chain_lengths : chainPreRows.length=12 ∧ price chainPreRows=27 ∧
    chainSkipRows.length=1 ∧ price chainSkipRows=1 ∧ chainEnterRows.length=2 ∧ price chainEnterRows=2 ∧
    chainLinkRows.length=2 ∧ price chainLinkRows=2 ∧ chainExitRows.length=1 ∧ price chainExitRows=1 := by decide

/-! ### Arithmetic of the counter rows -/

theorem tile_word (i : Index) : rv64_remu (BitVec.ofNat 64 i.val) 4096#64=BitVec.ofNat 64 (i.val%4096) := by
  unfold rv64_remu
  apply BitVec.eq_of_toNat_eq
  have h : i.val<16777216:=i.isLt
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat] <;> omega

theorem rank_word (i : Index) :
    rv64_remu (BitVec.ofNat 64 (i.val%4096)) 11#64=BitVec.ofNat 64 ((i.val%4096)%11) := by
  unfold rv64_remu
  apply BitVec.eq_of_toNat_eq
  have h : i.val<16777216:=i.isLt
  simp [BitVec.toNat_umod,BitVec.toNat_ofNat] <;> omega

theorem links_lt (i : Index) : chainLinks i<34 := by unfold chainLinks; omega

/-! ### The counter rows -/

def chainBefore (h : MachineState) := walkRows h chainPreRows

theorem chain_before (h : MachineState) (i : Index) (e : ChainEntry h i) :
    let t:=chainBefore h
    legal chainPreRows h ∧ t.pc=address 789 ∧ t.getReg .x28=BitVec.ofNat 64 (rank i.val) ∧
      t.getReg .x30=BitVec.ofNat 64 (chainLinks i) ∧
      t.mem=(h.setMem 1024 (Permutation.CounterSalt.ctr (K6Chain.restart (coord i).1))).mem ∧
      (∀ r, r≠.x7 → r≠.x28 → r≠.x30 → r≠.x31 → t.getReg r=h.getReg r) := by
  dsimp only
  have pc0 : h.pc=address 777 := e.pc
  have simple (r : Reg) (a : r≠.x7) (b : r≠.x28) (c : r≠.x30) (d : r≠.x31) :
      (chainBefore h).getReg r=h.getReg r := by
    simp [chainBefore,walkRows,chainPreRows,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d]
  refine ⟨?_,?_,?_,?_,?_,simple⟩
  · simp [chainPreRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc0,e.input,
      Opening.aligned_access 1024 (by decide) (by decide),show signExtend12 0#12=0#64 by decide,address]
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,pc0,address]
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,e.idx,e.divReg,e.base]
    simp only [tile_word i,rank_word i]
    rfl
  · simp [chainBefore,walkRows,chainPreRows,execInstrBr,e.idx,e.divReg,e.base,
      show signExtend12 34#12=34#64 by decide]
    simp only [tile_word i,K6Chain.divu_head i,K6Chain.remu_links i]
    rfl
  · rw [← K6Chain.restart_counter i]
    simp [chainBefore,walkRows,chainPreRows,execInstrBr,e.idx,e.divReg,e.base,e.input,mem_of_store,
      show signExtend12 0#12=0#64 by decide,show signExtend12 1#12=1#64 by decide,
      show signExtend12 34#12=34#64 by decide]
    simp only [tile_word i,rank_word i,K6Chain.divu_head i,K6Chain.remu_links i]
    try rfl

/-! ### The link loop -/

def linkQuery (s : MachineState) := packBuffer (window (memoryView s) 192)

/-- `c` in-place links from a state at row 792: query the reply window, write the answer back, `addi; bne`. -/
def linkTrace : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | c+1,s => do
      let z ← World.query (.inr (.inr (.inl (linkQuery s))))
      linkTrace c (walkRows (writeBits s (wordAddress 192) z) chainLinkRows)

/-- One in-place link with the oracle fixed. -/
noncomputable def linkStep (o : Oracle) (s : MachineState) : MachineState :=
  walkRows (writeBits s (wordAddress 192) (o.permutation (linkQuery s))) chainLinkRows

/-- `c` in-place links with the oracle fixed (an iterate, so unfolding never reduces the reply write). -/
noncomputable def linkState (o : Oracle) (c : Nat) (s : MachineState) : MachineState := (linkStep o)^[c] s

theorem linkState_zero (o : Oracle) (s : MachineState) : linkState o 0 s=s := rfl

theorem linkState_succ (o : Oracle) (c : Nat) (s : MachineState) :
    linkState o (c+1) s=linkState o c (linkStep o s) := Function.iterate_succ_apply _ _ _

/-- Registers the loop relies on, with `c` links still to go. -/
structure LinkReady (s : MachineState) (c : Nat) : Prop where
  pc : s.pc=address 792
  count : s.getReg .x30=BitVec.ofNat 64 c
  input : s.getReg .x10=1536
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1

/-- A reply write moves the PC by one row and keeps every register. -/
theorem write_pc {bits : Nat} (s : MachineState) (dst : Word) (z : BitVec bits) :
    (writeBits s dst z).pc=s.pc+4 := by simp only [writeBits,MachineState.setPC]

theorem dec_word (c : Nat) (hc : c+1<34) : BitVec.ofNat 64 (c+1)+signExtend12 4095#12=BitVec.ofNat 64 c := by
  have small : c<33 := by omega
  interval_cases c <;> decide

theorem small_ne (c : Nat) (hc : c<34) (nz : c≠0) : BitVec.ofNat 64 c≠0#64 := by
  intro e
  have t := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show c<2^64 by omega)] at t
  exact nz t

/-! ### The block -/

/-- The keyed generator query (counter word 128, key words 129..131, zeros). -/
def keyedQuery (h : MachineState) := packBuffer (window (memoryView (chainBefore h)) 128)

/-- The block's oracle trace: the keyed call, then `chainLinks i` in-place links; returns the state at
`chainStart+19`. -/
def chainTrace (h : MachineState) (i : Index) : OracleComp World MachineState := do
  let z ← World.query (.inr (.inr (.inl (keyedQuery h))))
  if chainLinks i=0 then
    return walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainSkipRows
  else do
    let b ← linkTrace (chainLinks i) (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows)
    return walkRows b chainExitRows

/-- The block's result when the oracle is fixed. -/
noncomputable def chainState (o : Oracle) (h : MachineState) (i : Index) : MachineState :=
  if chainLinks i=0 then
    walkRows (writeBits (chainBefore h) (wordAddress 192) (o.permutation (keyedQuery h))) chainSkipRows
  else
    walkRows (linkState o (chainLinks i)
      (walkRows (writeBits (chainBefore h) (wordAddress 192) (o.permutation (keyedQuery h))) chainEnterRows))
      chainExitRows

theorem after_keyed {bits : Nat} (h : MachineState) (i : Index) (e : ChainEntry h i) (z : BitVec bits) :
    let a:=writeBits (chainBefore h) (wordAddress 192) z
    a.pc=address 790 ∧ (∀ x, x≠.x7 → x≠.x28 → x≠.x30 → x≠.x31 → a.getReg x=h.getReg x) ∧
      a.getReg .x30=BitVec.ofNat 64 (chainLinks i) ∧ a.getReg .x28=BitVec.ofNat 64 (rank i.val) := by
  obtain ⟨_,pc,r28,r30,_,keep⟩ := chain_before h i e
  have regs (x : Reg) : (writeBits (chainBefore h) (wordAddress 192) z).getReg x=(chainBefore h).getReg x :=
    writeBits_register ..
  refine ⟨?_,fun x a b c d => (regs x).trans (keep x a b c d),(regs _).trans r30,(regs _).trans r28⟩
  rw [write_pc,pc]; exact address_succ 789

theorem skip_rows (a : MachineState) (pc : a.pc=address 790) (zero : a.getReg .x30=0#64) :
    legal chainSkipRows a ∧ (walkRows a chainSkipRows).pc=address 796 ∧
      (∀ x, (walkRows a chainSkipRows).getReg x=a.getReg x) ∧ (walkRows a chainSkipRows).mem=a.mem := by
  refine ⟨?_,?_,?_,?_⟩
  · simp [chainSkipRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc]
  · simp [chainSkipRows,walkRows,execInstrBr,pc,zero,address]
    decide
  · intro x
    simp only [chainSkipRows,walkRows,List.foldl,execInstrBr]
    split <;> simp
  · simp only [chainSkipRows,walkRows,List.foldl,execInstrBr]
    split <;> simp

theorem enter_rows (a : MachineState) (c : Nat) (pc : a.pc=address 790)
    (cnt : a.getReg .x30=BitVec.ofNat 64 (c+1)) (hc : c+1<34) :
    legal chainEnterRows a ∧ (walkRows a chainEnterRows).pc=address 792 ∧
      (walkRows a chainEnterRows).getReg .x10=a.getReg .x12 ∧
      (∀ x, x≠.x10 → (walkRows a chainEnterRows).getReg x=a.getReg x) ∧
      (walkRows a chainEnterRows).mem=a.mem := by
  have ne := small_ne (c+1) hc (by omega)
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [chainEnterRows,legal,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,cnt,ne,address]
  · simp [chainEnterRows,walkRows,execInstrBr,pc,cnt,ne,address]
  · simp [chainEnterRows,walkRows,execInstrBr,cnt,ne,show signExtend12 0#12=0#64 by decide]
  · intro x hx
    simp [chainEnterRows,walkRows,execInstrBr,cnt,ne,Ne.symm hx]
  · simp [chainEnterRows,walkRows,execInstrBr,cnt,ne]

end TwoPermutationPrototype.GroupedOpening
