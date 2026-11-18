import CommitGolfCandidate.GroupOpenWalk
import CommitGolfCandidate.K1OpenSalt
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.K6Chain

/-! Opener prefix, salt regeneration of one position on the linked (chain) schedule: rows
`chainStart .. chainStart+18`, the 33 link calls at rows 896..928 and the return at 929. With `n = i % 4096`,
`r = n % 11` (rank), `h = n / 11` (head in the tile), `j = h % 34` (links after the keyed restart):
```
777: remu x28,x6,x26 ; divu x30,x28,x29 ; remu x28,x28,x29 ; addi x31,x0,34 ; remu x30,x30,x31 ; mul x31,x30,x29 ;
     sub x7,x6,x28 ; sub x7,x7,x31 ; addi x7,x7,1 ; slli x7,x7,8 ; add x7,x7,x26 ; sd x7,0(x10) ; ecall ;
790: addi x10,x12,0 ; slli x31,x30,2 ; auipc x7,0 ; sub x7,x7,x31 ; jalr x0,548(x7)
896: ecall ×33 ; 929: jal x0,795 ; 795: addi x10,x0,1024
```
the keyed generator call of head `h - j` (counter = base of its C leaf, K1 input layout at word 128, reply at
`[1536, 1736)`), then a computed jump to row `929 - j`, which runs exactly `j` in-place links on `[1536, 1736)`.
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
abbrev chainStart : Nat := 777
/-- Links of position `i`: its head is `chainLinks i` heads after the keyed restart. -/
def chainLinks (i : Index) : Nat := ((i.val%4096)/11)%34
/-- Steps: 12 counter rows, the keyed call, 5 jump rows, one row per link, `jal` back and the exit row. -/
def chainSteps (i : Index) : Nat := 20+chainLinks i
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
/-- `addi x10,x12,0 ; slli x31,x30,2 ; auipc x7,0 ; sub x7,x7,x31 ; jalr x0,548(x7)`: to row `929 - links`. -/
def chainEnterRows : List Row := [(790,.ADDI .x10 .x12 0),(791,.SLLI .x31 .x30 2),(792,.AUIPC .x7 0),
  (793,.SUB .x7 .x7 .x31),(794,.JALR .x0 .x7 0x224)]
/-- `jal x0,795 ; addi x10,x0,1024`. -/
def chainOutRows : List Row := [(929,.JAL .x0 0x1ffde8),(795,.ADDI .x10 .x0 1024)]

/-- `rows_present` for rows anywhere in the 930-word image. -/
theorem rows_present_ext (rows : List Row)
    (raw : ∀ i : Fin rows.length, rows[i].1<930 ∧ (openingImage.code[rows[i].1]?).bind Opening.decodeBase=some rows[i].2) :
    presentRows rows := by
  intro p hp;obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hp
  subst p
  exact fun st pc => packed_fetch_ext st _ _ (raw ⟨i,hi⟩).1 pc (raw ⟨i,hi⟩).2

theorem chain_pre_fetch : presentRows chainPreRows := by apply rows_present; decide +kernel
theorem chain_enter_fetch : presentRows chainEnterRows := by apply rows_present; decide +kernel
theorem chain_out_fetch : presentRows chainOutRows := by apply rows_present_ext; decide +kernel

theorem keyed_fetch (s : MachineState) (pc : s.pc=address 789) : fetch openingImage s=some (.base .ECALL) :=
  packed_fetch_base _ 789 _ (by decide) pc (by decide +kernel)

private theorem calls_decoded : ∀ j : Fin 33, (openingImage.code[896+j.val]?).bind Opening.decodeBase=some .ECALL := by
  decide +kernel

/-- The link calls: rows 896..928. -/
theorem call_fetch (s : MachineState) (n : Nat) (lo : 896≤n) (hi : n<929) (pc : s.pc=address n) :
    fetch openingImage s=some (.base .ECALL) := by
  have e := calls_decoded ⟨n-896,by omega⟩
  rw [show 896+(n-896)=n by omega] at e
  exact packed_fetch_ext _ n _ (by omega) pc e

theorem pre_len : chainPreRows.length=12 := rfl
theorem pre_price : price chainPreRows=27 := by decide
theorem enter_len : chainEnterRows.length=5 := rfl
theorem enter_price : price chainEnterRows=5 := by decide
theorem out_len : chainOutRows.length=2 := rfl
theorem out_price : price chainOutRows=2 := by decide

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

/-- `c` consecutive link calls. -/
def callsTrace : Nat → MachineState → OracleComp World MachineState
  | 0,s => pure s
  | c+1,s => do
      let a ← callTrace s
      callsTrace c a

/-- One link call with the oracle fixed. -/
noncomputable def callState (o : Oracle) (s : MachineState) : MachineState :=
  writeBits s (wordAddress 192) (o.permutation (linkQuery s))

/-- Registers every link call relies on. -/
structure CallRegs (s : MachineState) : Prop where
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

/-- The block's oracle trace: the keyed call, the jump, `chainLinks i` in-place links, the return and the exit
row; returns the state at `chainStart+19`. -/
def chainTrace (h : MachineState) (i : Index) : OracleComp World MachineState := do
  let z ← World.query (.inr (.inr (.inl (keyedQuery h))))
  let t ← callsTrace (chainLinks i) (walkRows (writeBits (chainBefore h) (wordAddress 192) z) chainEnterRows)
  return walkRows t chainOutRows

/-- The block's result when the oracle is fixed. -/
noncomputable def chainState (o : Oracle) (h : MachineState) (i : Index) : MachineState :=
  walkRows ((callState o)^[chainLinks i]
    (walkRows (writeBits (chainBefore h) (wordAddress 192) (o.permutation (keyedQuery h))) chainEnterRows))
    chainOutRows

theorem after_keyed {bits : Nat} (h : MachineState) (i : Index) (e : ChainEntry h i) (z : BitVec bits) :
    let a:=writeBits (chainBefore h) (wordAddress 192) z
    a.pc=address 790 ∧ (∀ x, x≠.x7 → x≠.x28 → x≠.x30 → x≠.x31 → a.getReg x=h.getReg x) ∧
      a.getReg .x30=BitVec.ofNat 64 (chainLinks i) ∧ a.getReg .x28=BitVec.ofNat 64 (rank i.val) := by
  obtain ⟨_,pc,r28,r30,_,keep⟩ := chain_before h i e
  have regs (x : Reg) : (writeBits (chainBefore h) (wordAddress 192) z).getReg x=(chainBefore h).getReg x :=
    writeBits_register ..
  refine ⟨?_,fun x a b c d => (regs x).trans (keep x a b c d),(regs _).trans r30,(regs _).trans r28⟩
  rw [write_pc,pc]; exact address_succ 789

/-! ### The jump rows -/

/-- The jump target, case by case over the 34 link counts. -/
theorem jump_arith (k : Nat) (hk : k<34) :
    (address 790+4+4+(((0 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)-
      (BitVec.ofNat 64 k <<< (2 : BitVec 6).toNat)+signExtend12 (0x224 : BitVec 12)) &&& ~~~1#64=
      address (929-k) := by
  interval_cases k <;> decide

private theorem walk_five (w : MachineState) (a b c d e : Nat) (p q r u v : Instr) :
    walkRows w [(a,p),(b,q),(c,r),(d,u),(e,v)]=
      execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr w p) q) r) u) v := rfl

private theorem walk_two (w : MachineState) (a b : Nat) (p q : Instr) :
    walkRows w [(a,p),(b,q)]=execInstrBr (execInstrBr w p) q := rfl

theorem enter_walk (s : MachineState) : walkRows s chainEnterRows=
    execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.ADDI .x10 .x12 0)) (.SLLI .x31 .x30 2))
      (.AUIPC .x7 0)) (.SUB .x7 .x7 .x31)) (.JALR .x0 .x7 0x224) := by
  unfold chainEnterRows; exact walk_five s _ _ _ _ _ _ _ _ _ _

theorem out_walk (s : MachineState) : walkRows s chainOutRows=
    execInstrBr (execInstrBr s (.JAL .x0 0x1ffde8)) (.ADDI .x10 .x0 1024) := by
  unfold chainOutRows; exact walk_two s _ _ _ _

/-- Rows that touch neither memory nor an `ecall`. -/
private theorem rows_plain (rows : List Row) (nm : rows.all (fun p => plain p.2 && noMemOp p.2)=true)
    (s : MachineState) (c : pcChain rows s) : legal rows s := legal_of_chain rows s nm c

theorem enter_rows (a : MachineState) (k : Nat) (hk : k<34) (pc : a.pc=address 790)
    (cnt : a.getReg .x30=BitVec.ofNat 64 k) :
    legal chainEnterRows a ∧ (walkRows a chainEnterRows).pc=address (929-k) ∧
      (walkRows a chainEnterRows).getReg .x10=a.getReg .x12 ∧
      (∀ x, x≠.x7 → x≠.x10 → x≠.x31 → (walkRows a chainEnterRows).getReg x=a.getReg x) ∧
      (walkRows a chainEnterRows).mem=a.mem := by
  let b1 := execInstrBr a (.ADDI .x10 .x12 0)
  let b2 := execInstrBr b1 (.SLLI .x31 .x30 2)
  let b3 := execInstrBr b2 (.AUIPC .x7 0)
  let b4 := execInstrBr b3 (.SUB .x7 .x7 .x31)
  have p1 : b1.pc=address 790+4 := by show a.pc+4=_; rw [pc]
  have p2 : b2.pc=address 790+4+4 := by show b1.pc+4=_; rw [p1]
  have p3 : b3.pc=address 790+4+4+4 := by show b2.pc+4=_; rw [p2]
  have p4 : b4.pc=address 790+4+4+4+4 := by show b3.pc+4=_; rw [p3]
  have k1 (x : Reg) (hx : x≠.x10) : b1.getReg x=a.getReg x := by
    show ((a.setReg .x10 _).setPC _).getReg x=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_neg (fun e => hx e.1.symm)]
  have k2 (x : Reg) (hx : x≠.x31) : b2.getReg x=b1.getReg x := by
    show ((b1.setReg .x31 _).setPC _).getReg x=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_neg (fun e => hx e.1.symm)]
  have k3 (x : Reg) (hx : x≠.x7) : b3.getReg x=b2.getReg x := by
    show ((b2.setReg .x7 _).setPC _).getReg x=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_neg (fun e => hx e.1.symm)]
  have k4 (x : Reg) (hx : x≠.x7) : b4.getReg x=b3.getReg x := by
    show ((b3.setReg .x7 _).setPC _).getReg x=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_neg (fun e => hx e.1.symm)]
  have v31 : b2.getReg .x31=BitVec.ofNat 64 k <<< (2 : BitVec 6).toNat := by
    show ((b1.setReg .x31 (b1.getReg .x30 <<< (2 : BitVec 6).toNat)).setPC _).getReg .x31=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_pos ⟨rfl,by decide⟩,k1 _ (by decide),cnt]
  have v7 : b3.getReg .x7=b2.pc+(((0 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64) := by
    show ((b2.setReg .x7 _).setPC _).getReg .x7=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_pos ⟨rfl,by decide⟩]
  have v7' : b4.getReg .x7=b2.pc+(((0 : BitVec 20).zeroExtend 32 <<< 12).signExtend 64)-
      (BitVec.ofNat 64 k <<< (2 : BitVec 6).toNat) := by
    show ((b3.setReg .x7 (b3.getReg .x7-b3.getReg .x31)).setPC _).getReg .x7=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_pos ⟨rfl,by decide⟩,v7,k3 _ (by decide),v31]
  have jal : execInstrBr b4 (.JALR .x0 .x7 0x224)=
      b4.setPC ((b4.getReg .x7+signExtend12 (0x224 : BitVec 12)) &&& ~~~1#64) := rfl
  have walk : walkRows a chainEnterRows=b4.setPC ((b4.getReg .x7+signExtend12 (0x224 : BitVec 12)) &&& ~~~1#64) :=
    (enter_walk a).trans jal
  have m4 : b4.mem=a.mem := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine rows_plain _ (by decide) a ⟨pc,?_,?_,?_,?_,trivial⟩
    · rw [p1]; exact address_succ 790
    · rw [p2,address_succ 790]; exact address_succ 791
    · rw [p3,address_succ 790,address_succ 791]; exact address_succ 792
    · rw [p4,address_succ 790,address_succ 791,address_succ 792]; exact address_succ 793
  · rw [walk,pc_of_set,v7',p2]; exact jump_arith k hk
  · rw [walk,MachineState.getReg_setPC,k4 _ (by decide),k3 _ (by decide),k2 _ (by decide)]
    show ((a.setReg .x10 (a.getReg .x12+signExtend12 0)).setPC _).getReg .x10=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_pos ⟨rfl,by decide⟩,
      show signExtend12 (0 : BitVec 12)=0#64 from by decide,BitVec.add_zero]
  · intro x h7 h10 h31
    rw [walk,MachineState.getReg_setPC,k4 _ h7,k3 _ h7,k2 _ h31,k1 _ h10]
  · rw [walk,mem_of_set]; exact m4

theorem out_rows (b : MachineState) (pc : b.pc=address 929) :
    legal chainOutRows b ∧ (walkRows b chainOutRows).pc=address 796 ∧
      (walkRows b chainOutRows).getReg .x10=1024 ∧
      (∀ x, x≠.x10 → (walkRows b chainOutRows).getReg x=b.getReg x) ∧
      (walkRows b chainOutRows).mem=b.mem := by
  let j := execInstrBr b (.JAL .x0 0x1ffde8)
  have jform : j=b.setPC (b.pc+signExtend21 0x1ffde8) := rfl
  have jpc : j.pc=address 795 := by rw [jform,pc_of_set,pc]; decide
  have walk := out_walk b
  refine ⟨rows_plain _ (by decide) b ⟨pc,jpc,trivial⟩,?_,?_,?_,?_⟩
  · rw [walk]; show j.pc+4=_; rw [jpc]; exact address_succ 795
  · rw [walk]; show ((j.setReg .x10 (j.getReg .x0+signExtend12 1024)).setPC _).getReg .x10=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_pos ⟨rfl,by decide⟩,chain_zero_reg]; decide
  · intro x hx
    rw [walk]; show ((j.setReg .x10 _).setPC _).getReg x=_
    rw [MachineState.getReg_setPC,Opening.getReg_setReg,if_neg (fun e => hx e.1.symm),jform,
      MachineState.getReg_setPC]
  · rw [walk]; show ((j.setReg .x10 _).setPC _).mem=_
    rw [mem_of_set,mem_of_reg,jform,mem_of_set]

end TwoPermutationPrototype.GroupedOpening
