import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.K6Chain

/-! Opener prefix, salt regeneration of one position on the linked (chain) schedule: rows
`chainStart .. chainStart+18` and the link groups at rows 4..14. With `n = i % 4096`, `r = n % 11` (rank),
`h = n / 11` (head in the tile), `j = h % 34` (links after the keyed restart):
```
777: remu x28,x6,x26 ; divu x30,x28,x29 ; remu x28,x28,x29 ; addi x31,x0,34 ; remu x30,x30,x31 ; mul x31,x30,x29 ;
     sub x7,x6,x28 ; sub x7,x7,x31 ; addi x7,x7,1 ; slli x7,x7,8 ; add x7,x7,x26 ; sd x7,0(x10) ; ecall ;
790: beq x30,x0,796 ; addi x10,x12,0 ; jal x0,4
  4: addi x30,x30,-4 ; blt x30,x0,11 ; ecall ; ecall ; ecall ; ecall ; jal x0,4
 11: addi x30,x30,4 ; beq x30,x0,795 ; ecall ; jal x0,793
793: addi x30,x30,-1 ; bne x30,x0,13 ; addi x10,x0,1024
```
the keyed generator call of head `h - j` (counter = base of its C leaf, K1 input layout at word 128, reply at
`[1536, 1736)`), then `j` in-place links on `[1536, 1736)`: `j / 4` groups of four calls (rows 4..10), then `j % 4`
single calls (rows 13, 14, 793, 794). Rows 4..14 were the dead copy of the setup rows in the base image. The counter
arithmetic and the reply of the restart-plus-links walk are S9-K6P's `K6Chain.restart_counter` /
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
abbrev chainStart : Nat := 777
/-- Links of position `i`: its head is `chainLinks i` heads after the keyed restart. -/
def chainLinks (i : Index) : Nat := ((i.val%4096)/11)%34
/-- Steps: 14 rows and calls without links (`beq` taken); else 21, plus 7 per group of four links and 4 per
remaining link. -/
def chainSteps (i : Index) : Nat := if chainLinks i=0 then 14 else 21+7*(chainLinks i/4)+4*(chainLinks i%4)
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
def chainEnterRows : List Row := [(790,.BEQ .x30 .x0 24),(791,.ADDI .x10 .x12 0),(792,.JAL .x0 0x1ff3b0)]
/-- Head of a group: `addi x30,x30,-4 ; blt x30,x0,11`. -/
def groupTestRows : List Row := [(4,.ADDI .x30 .x30 0xffc),(5,.BLT .x30 .x0 0x18)]
/-- End of a group: `jal x0,4`. -/
def groupBackRows : List Row := [(10,.JAL .x0 0x1fffe8)]
/-- Leaving the groups with `c < 4` links left: the group head (taken `blt`), `addi x30,x30,4 ; beq x30,x0,795`. -/
def groupOutRows : List Row := [(4,.ADDI .x30 .x30 0xffc),(5,.BLT .x30 .x0 0x18),(11,.ADDI .x30 .x30 4),
  (12,.BEQ .x30 .x0 0xc3c)]
/-- After a single link call at row 13: `jal x0,793 ; addi x30,x30,-1 ; bne x30,x0,13`. -/
def restRows : List Row := [(14,.JAL .x0 0xc2c),(793,.ADDI .x30 .x30 0xfff),(794,.BNE .x30 .x0 0x13cc)]
def chainExitRows : List Row := [(795,.ADDI .x10 .x0 1024)]

theorem chain_pre_fetch : presentRows chainPreRows := by apply rows_present; decide +kernel
theorem chain_skip_fetch : presentRows chainSkipRows := by apply rows_present; decide +kernel
theorem chain_enter_fetch : presentRows chainEnterRows := by apply rows_present; decide +kernel
theorem group_test_fetch : presentRows groupTestRows := by apply rows_present; decide +kernel
theorem group_back_fetch : presentRows groupBackRows := by apply rows_present; decide +kernel
theorem group_out_fetch : presentRows groupOutRows := by apply rows_present; decide +kernel
theorem rest_fetch : presentRows restRows := by apply rows_present; decide +kernel
theorem chain_exit_fetch : presentRows chainExitRows := by apply rows_present; decide +kernel

theorem keyed_fetch (s : MachineState) (pc : s.pc=address 789) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_base _ 789 _ (by decide) pc (by decide +kernel)

/-- The link calls: rows 6..9 (a group) and 13 (a single link). -/
theorem call_fetch (s : MachineState) (n : Nat) (hn : n=6 ∨ n=7 ∨ n=8 ∨ n=9 ∨ n=13) (pc : s.pc=address n) :
    fetch openingImage s=some (.base .ECALL) := by
  rcases hn with rfl|rfl|rfl|rfl|rfl
  all_goals exact packed_fetch_base _ _ _ (by decide) pc (by decide +kernel)

theorem pre_len : chainPreRows.length=12 := rfl
theorem pre_price : price chainPreRows=27 := by decide
theorem skip_len : chainSkipRows.length=1 := rfl
theorem skip_price : price chainSkipRows=1 := by decide
theorem enter_len : chainEnterRows.length=3 := rfl
theorem enter_price : price chainEnterRows=3 := by decide
theorem test_len : groupTestRows.length=2 := rfl
theorem test_price : price groupTestRows=2 := by decide
theorem back_len : groupBackRows.length=1 := rfl
theorem back_price : price groupBackRows=1 := by decide
theorem out_len : groupOutRows.length=4 := rfl
theorem out_price : price groupOutRows=4 := by decide
theorem rest_len : restRows.length=3 := rfl
theorem rest_price : price restRows=3 := by decide
theorem exit_len : chainExitRows.length=1 := rfl
theorem exit_price : price chainExitRows=1 := by decide

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

/-! ### The link calls -/

def linkQuery (s : MachineState) := packBuffer (window (memoryView s) 192)

/-- One in-place link call: query the reply window, write the answer back (the PC moves one row). -/
def callTrace (s : MachineState) : OracleComp World MachineState := do
  let z ← World.query (.inr (.inr (.inl (linkQuery s))))
  return writeBits s (wordAddress 192) z

/-- `q` groups of four calls from row 4 (each: group head, four calls, `jal` back to row 4). -/
def linkGroupTrace : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | q+1,s => do
      let a ← callTrace (walkRows s groupTestRows)
      let b ← callTrace a
      let c ← callTrace b
      let d ← callTrace c
      linkGroupTrace q (walkRows d groupBackRows)

/-- `r` single calls from row 13 (each: the call, `jal; addi; bne`). -/
def restTrace : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | r+1,s => do
      let a ← callTrace s
      restTrace r (walkRows a restRows)

/-- One link call with the oracle fixed. -/
noncomputable def callState (o : Oracle) (s : MachineState) : MachineState :=
  writeBits s (wordAddress 192) (o.permutation (linkQuery s))

/-- One group with the oracle fixed. -/
noncomputable def linkGroupStep (o : Oracle) (s : MachineState) : MachineState :=
  walkRows (callState o (callState o (callState o (callState o (walkRows s groupTestRows))))) groupBackRows

/-- `q` groups with the oracle fixed (an iterate, so unfolding never reduces the reply writes). -/
noncomputable def linkGroupState (o : Oracle) (q : Nat) (s : MachineState) : MachineState := (linkGroupStep o)^[q] s

/-- One single link with the oracle fixed. -/
noncomputable def restStep (o : Oracle) (s : MachineState) : MachineState := walkRows (callState o s) restRows

/-- `r` single links with the oracle fixed. -/
noncomputable def restState (o : Oracle) (r : Nat) (s : MachineState) : MachineState := (restStep o)^[r] s

/-- Registers every link call relies on. -/
structure CallRegs (s : MachineState) : Prop where
  input : s.getReg .x10=1536
  output : s.getReg .x12=1536
  selector : s.getReg .x5=0
  width : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem CallRegs.keep {s t : MachineState} (r : CallRegs s) (keep : ∀ x, x≠.x30 → t.getReg x=s.getReg x) :
    CallRegs t :=
  ⟨(keep _ (by decide)).trans r.input,(keep _ (by decide)).trans r.output,(keep _ (by decide)).trans r.selector,
    (keep _ (by decide)).trans r.width,(keep _ (by decide)).trans r.primitive⟩

/-- At the group head (row 4) with `c` links still to go. -/
structure LinkGroupReady (s : MachineState) (c : Nat) : Prop where
  pc : s.pc=address 4
  count : s.getReg .x30=BitVec.ofNat 64 c
  regs : CallRegs s

/-- At a single link (row 13) with `c` links still to go, or at the exit row 795 when none is left. -/
structure RestReady (s : MachineState) (c : Nat) : Prop where
  pc : s.pc=(if c=0 then address 795 else address 13)
  count : s.getReg .x30=BitVec.ofNat 64 c
  regs : CallRegs s

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

/-- The block's oracle trace: the keyed call, then `chainLinks i` in-place links (`/ 4` groups, `% 4` singles);
returns the state at `chainStart+19`. -/
def chainTrace (h : MachineState) (i : Index) : OracleComp World MachineState := do
  let z ← World.query (.inr (.inr (.inl (keyedQuery h))))
  if chainLinks i=0 then
    return walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainSkipRows
  else do
    let g ← linkGroupTrace (chainLinks i/4) (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows)
    let b ← restTrace (chainLinks i%4) (walkRows g groupOutRows)
    return walkRows b chainExitRows

/-- The block's result when the oracle is fixed. -/
noncomputable def chainState (o : Oracle) (h : MachineState) (i : Index) : MachineState :=
  if chainLinks i=0 then
    walkRows (writeBits (chainBefore h) (wordAddress 192) (o.permutation (keyedQuery h))) chainSkipRows
  else
    walkRows (restState o (chainLinks i%4) (walkRows (linkGroupState o (chainLinks i/4)
      (walkRows (writeBits (chainBefore h) (wordAddress 192) (o.permutation (keyedQuery h))) chainEnterRows))
      groupOutRows)) chainExitRows

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

/-! ### Row segments of the link loop (only the PC and `x30` move) -/

/-- `t` is `s` with only the PC and `x30` changed. -/
structure Pt (s t : MachineState) (p v : Word) : Prop where
  pc : t.pc=p
  r30 : t.getReg .x30=v
  keep : ∀ x, x≠.x30 → t.getReg x=s.getReg x
  mem : t.mem=s.mem

theorem pt_start (s : MachineState) (p v : Word) (hp : s.pc=p) (hv : s.getReg .x30=v) : Pt s s p v :=
  ⟨hp,hv,fun _ _ => rfl,rfl⟩

theorem Pt.congr {s t : MachineState} {p v p' v' : Word} (h : Pt s t p v) (hp : p=p') (hv : v=v') : Pt s t p' v' :=
  hp ▸ hv ▸ h

theorem pt_addi {s t : MachineState} {p v : Word} (h : Pt s t p v) (imm : BitVec 12) :
    Pt s (execInstrBr t (.ADDI .x30 .x30 imm)) (p+4) (v+signExtend12 imm) := by
  have form : execInstrBr t (.ADDI .x30 .x30 imm)=(t.setReg .x30 (t.getReg .x30+signExtend12 imm)).setPC (t.pc+4) :=
    rfl
  rw [form]
  refine ⟨?_,?_,?_,?_⟩
  · rw [pc_of_set,h.pc]
  · rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_pos ⟨rfl,by decide⟩,h.r30]
  · intro x hx
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_neg (fun e => hx e.1.symm)]
    exact h.keep x hx
  · rw [mem_of_set,mem_of_reg,h.mem]

theorem pt_jal {s t : MachineState} {p v : Word} (h : Pt s t p v) (off : BitVec 21) :
    Pt s (execInstrBr t (.JAL .x0 off)) (p+signExtend21 off) v := by
  have form : execInstrBr t (.JAL .x0 off)=t.setPC (t.pc+signExtend21 off) := rfl
  rw [form]
  exact ⟨by rw [pc_of_set,h.pc],by rw [MachineState.getReg_setPC,h.r30],
    fun x hx => by rw [MachineState.getReg_setPC]; exact h.keep x hx,by rw [mem_of_set,h.mem]⟩

theorem pt_blt {s t : MachineState} {p v : Word} (h : Pt s t p v) (off : BitVec 13) :
    Pt s (execInstrBr t (.BLT .x30 .x0 off)) (if BitVec.slt v 0#64 then p+signExtend13 off else p+4) v := by
  have form : execInstrBr t (.BLT .x30 .x0 off)=
      t.setPC (if BitVec.slt (t.getReg .x30) 0#64 then t.pc+signExtend13 off else t.pc+4) := by
    rw [apply_ite (MachineState.setPC t)]; rfl
  rw [form]
  exact ⟨by rw [pc_of_set,h.pc,h.r30],by rw [MachineState.getReg_setPC,h.r30],
    fun x hx => by rw [MachineState.getReg_setPC]; exact h.keep x hx,by rw [mem_of_set,h.mem]⟩

theorem pt_beq {s t : MachineState} {p v : Word} (h : Pt s t p v) (off : BitVec 13) :
    Pt s (execInstrBr t (.BEQ .x30 .x0 off)) (if (v == 0#64)=true then p+signExtend13 off else p+4) v := by
  have form : execInstrBr t (.BEQ .x30 .x0 off)=
      t.setPC (if (t.getReg .x30 == 0#64)=true then t.pc+signExtend13 off else t.pc+4) := by
    rw [apply_ite (MachineState.setPC t)]; rfl
  rw [form]
  exact ⟨by rw [pc_of_set,h.pc,h.r30],by rw [MachineState.getReg_setPC,h.r30],
    fun x hx => by rw [MachineState.getReg_setPC]; exact h.keep x hx,by rw [mem_of_set,h.mem]⟩

theorem pt_bne {s t : MachineState} {p v : Word} (h : Pt s t p v) (off : BitVec 13) :
    Pt s (execInstrBr t (.BNE .x30 .x0 off)) (if (v != 0#64)=true then p+signExtend13 off else p+4) v := by
  have form : execInstrBr t (.BNE .x30 .x0 off)=
      t.setPC (if (t.getReg .x30 != 0#64)=true then t.pc+signExtend13 off else t.pc+4) := by
    rw [apply_ite (MachineState.setPC t)]; rfl
  rw [form]
  exact ⟨by rw [pc_of_set,h.pc,h.r30],by rw [MachineState.getReg_setPC,h.r30],
    fun x hx => by rw [MachineState.getReg_setPC]; exact h.keep x hx,by rw [mem_of_set,h.mem]⟩

/-- PC and counter arithmetic of the segments, case by case over the 34 link counts. -/
theorem test_arith (c : Nat) (lo : 4≤c) (hc : c<34) :
    BitVec.ofNat 64 c+signExtend12 (0xffc : BitVec 12)=BitVec.ofNat 64 (c-4) ∧
      (if BitVec.slt (BitVec.ofNat 64 (c-4)) 0#64 then address 4+4+signExtend13 (0x18 : BitVec 13) else address 4+4+4)=
        address 6 := by
  interval_cases c <;> decide

theorem out_arith (c : Nat) (hc : c<4) :
    BitVec.slt (BitVec.ofNat 64 c+signExtend12 (0xffc : BitVec 12)) 0#64=true ∧
      BitVec.ofNat 64 c+signExtend12 (0xffc : BitVec 12)+signExtend12 (4 : BitVec 12)=BitVec.ofNat 64 c ∧
      (if (BitVec.ofNat 64 c == 0#64)=true then address 4+4+signExtend13 (0x18 : BitVec 13)+4+signExtend13 (0xc3c : BitVec 13)
        else address 4+4+signExtend13 (0x18 : BitVec 13)+4+4)=(if c=0 then address 795 else address 13) := by
  interval_cases c <;> decide

theorem rest_arith (c : Nat) (hc : c+1<34) :
    BitVec.ofNat 64 (c+1)+signExtend12 (0xfff : BitVec 12)=BitVec.ofNat 64 c ∧
      (if (BitVec.ofNat 64 c != 0#64)=true then address 14+signExtend21 (0xc2c : BitVec 21)+4+signExtend13 (0x13cc : BitVec 13)
        else address 14+signExtend21 (0xc2c : BitVec 21)+4+4)=(if c=0 then address 795 else address 13) := by
  have small : c<33 := by omega
  interval_cases c <;> decide

theorem back_arith : address 10+signExtend21 (0x1fffe8 : BitVec 21)=address 4 := by decide

theorem enter_arith : address 790+4+4+signExtend21 (0x1ff3b0 : BitVec 21)=address 4 := by decide

/-- Row walks for abstract instructions (the kernel never evaluates the immediates). -/
private theorem walk_one (w : MachineState) (a : Nat) (p : Instr) : walkRows w [(a,p)]=execInstrBr w p := rfl
private theorem walk_two (w : MachineState) (a b : Nat) (p q : Instr) :
    walkRows w [(a,p),(b,q)]=execInstrBr (execInstrBr w p) q := rfl
private theorem walk_three (w : MachineState) (a b c : Nat) (p q r : Instr) :
    walkRows w [(a,p),(b,q),(c,r)]=execInstrBr (execInstrBr (execInstrBr w p) q) r := rfl
private theorem walk_four (w : MachineState) (a b c d : Nat) (p q r u : Instr) :
    walkRows w [(a,p),(b,q),(c,r),(d,u)]=execInstrBr (execInstrBr (execInstrBr (execInstrBr w p) q) r) u := rfl

theorem test_walk (s : MachineState) : walkRows s groupTestRows=
    execInstrBr (execInstrBr s (.ADDI .x30 .x30 0xffc)) (.BLT .x30 .x0 0x18) := by
  unfold groupTestRows; exact walk_two s _ _ _ _
theorem out_walk (s : MachineState) : walkRows s groupOutRows=
    execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.ADDI .x30 .x30 0xffc)) (.BLT .x30 .x0 0x18))
      (.ADDI .x30 .x30 4)) (.BEQ .x30 .x0 0xc3c) := by
  unfold groupOutRows; exact walk_four s _ _ _ _ _ _ _ _
theorem back_walk (s : MachineState) : walkRows s groupBackRows=execInstrBr s (.JAL .x0 0x1fffe8) := by
  unfold groupBackRows; exact walk_one s _ _
theorem rest_walk (s : MachineState) : walkRows s restRows=
    execInstrBr (execInstrBr (execInstrBr s (.JAL .x0 0xc2c)) (.ADDI .x30 .x30 0xfff)) (.BNE .x30 .x0 0x13cc) := by
  unfold restRows; exact walk_three s _ _ _ _ _ _
theorem enter_walk (s : MachineState) : walkRows s chainEnterRows=
    execInstrBr (execInstrBr (execInstrBr s (.BEQ .x30 .x0 24)) (.ADDI .x10 .x12 0)) (.JAL .x0 0x1ff3b0) := by
  unfold chainEnterRows; exact walk_three s _ _ _ _ _ _

/-- Rows that touch neither memory nor an `ecall`. -/
private theorem rows_plain (rows : List Row) (nm : rows.all (fun p => plain p.2 && noMemOp p.2)=true)
    (s : MachineState) (c : pcChain rows s) : legal rows s := legal_of_chain rows s nm c

theorem test_rows (s : MachineState) (c : Nat) (lo : 4≤c) (hc : c<34) (pc : s.pc=address 4)
    (cnt : s.getReg .x30=BitVec.ofNat 64 c) :
    legal groupTestRows s ∧ Pt s (walkRows s groupTestRows) (address 6) (BitVec.ofNat 64 (c-4)) := by
  obtain ⟨sub,goes⟩ := test_arith c lo hc
  have p1 := pt_addi (pt_start s _ _ pc cnt) 0xffc
  have p2 := pt_blt (p1.congr rfl sub) 0x18
  refine ⟨rows_plain _ (by decide) s ⟨pc,p1.pc.trans (address_succ 4),trivial⟩,?_⟩
  rw [test_walk]
  exact p2.congr goes rfl

theorem out_rows (s : MachineState) (c : Nat) (hc : c<4) (pc : s.pc=address 4)
    (cnt : s.getReg .x30=BitVec.ofNat 64 c) :
    legal groupOutRows s ∧
      Pt s (walkRows s groupOutRows) (if c=0 then address 795 else address 13) (BitVec.ofNat 64 c) := by
  obtain ⟨neg,back,goes⟩ := out_arith c hc
  have p1 := pt_addi (pt_start s _ _ pc cnt) 0xffc
  have p2 := pt_blt p1 0x18
  rw [if_pos neg] at p2
  have p3 := pt_addi p2 4
  have p4 := pt_beq (p3.congr rfl back) 0xc3c
  refine ⟨rows_plain _ (by decide) s ⟨pc,p1.pc.trans (address_succ 4),?_,?_,trivial⟩,?_⟩
  rotate_left 2
  · rw [out_walk]; exact p4.congr goes rfl
  · rw [p2.pc]; decide
  · rw [p3.pc]; decide

theorem back_rows (s : MachineState) (pc : s.pc=address 10) :
    legal groupBackRows s ∧ Pt s (walkRows s groupBackRows) (address 4) (s.getReg .x30) := by
  have p1 := pt_jal (pt_start s _ _ pc rfl) 0x1fffe8
  refine ⟨rows_plain _ (by decide) s ⟨pc,trivial⟩,?_⟩
  rw [back_walk]; exact p1.congr back_arith rfl

theorem rest_rows (s : MachineState) (c : Nat) (hc : c+1<34) (pc : s.pc=address 14)
    (cnt : s.getReg .x30=BitVec.ofNat 64 (c+1)) :
    legal restRows s ∧
      Pt s (walkRows s restRows) (if c=0 then address 795 else address 13) (BitVec.ofNat 64 c) := by
  obtain ⟨dec,goes⟩ := rest_arith c hc
  have p1 := pt_jal (pt_start s _ _ pc cnt) 0xc2c
  have p2 := pt_addi p1 0xfff
  have p3 := pt_bne (p2.congr rfl dec) 0x13cc
  refine ⟨rows_plain _ (by decide) s ⟨pc,?_,?_,trivial⟩,?_⟩
  rotate_left 2
  · rw [rest_walk]; exact p3.congr goes rfl
  · rw [p1.pc]; decide
  · rw [p2.pc]; decide

theorem enter_rows (a : MachineState) (c : Nat) (pc : a.pc=address 790)
    (cnt : a.getReg .x30=BitVec.ofNat 64 (c+1)) (hc : c+1<34) :
    legal chainEnterRows a ∧ (walkRows a chainEnterRows).pc=address 4 ∧
      (walkRows a chainEnterRows).getReg .x10=a.getReg .x12 ∧
      (∀ x, x≠.x10 → (walkRows a chainEnterRows).getReg x=a.getReg x) ∧
      (walkRows a chainEnterRows).mem=a.mem := by
  have ne := small_ne (c+1) hc (by omega)
  have b0 : execInstrBr a (.BEQ .x30 .x0 24)=a.setPC (a.pc+4) := by
    simp [execInstrBr,cnt,ne]
  let b := a.setPC (a.pc+4)
  have b1 : execInstrBr b (.ADDI .x10 .x12 0)=(b.setReg .x10 (b.getReg .x12+signExtend12 0)).setPC (b.pc+4) := rfl
  let d := (b.setReg .x10 (b.getReg .x12+signExtend12 0)).setPC (b.pc+4)
  have b2 : execInstrBr d (.JAL .x0 0x1ff3b0)=d.setPC (d.pc+signExtend21 0x1ff3b0) := rfl
  have walk : walkRows a chainEnterRows=d.setPC (d.pc+signExtend21 0x1ff3b0) := by
    rw [enter_walk,b0,b1,b2]
  have dpc : d.pc=address 790+4+4 := by
    show b.pc+4=_; rw [show b.pc=a.pc+4 from rfl,pc]
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine rows_plain _ (by decide) a ⟨pc,?_,?_,trivial⟩
    · rw [b0,pc_of_set,pc]; exact address_succ 790
    · rw [b0,b1,pc_of_set,pc_of_set,pc,address_succ 790]; exact address_succ 791
  · rw [walk,pc_of_set,dpc]; exact enter_arith
  · rw [walk]
    simp [d,b,show signExtend12 0#12=0#64 by decide]
  · intro x hx
    rw [walk]
    simp [d,b,Ne.symm hx]
  · rw [walk]; simp [d,b]

end TwoPermutationPrototype.GroupedOpening
