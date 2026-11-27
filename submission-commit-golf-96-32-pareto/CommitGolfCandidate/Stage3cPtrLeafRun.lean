import CommitGolfCandidate.Stage3cPtrLeafHash
import CommitGolfCandidate.Stage3cPtrLeafGap
import CommitGolfCandidate.Stage3cRuns

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option Elab.async false

private theorem tail_word (k e : Nat) (he : e < 6) :
    Site .commit (leafPC k + 12 + e) (tailAt (k % 128) e) := by
  have eq : leafPC k + 12 + e = 4123 + localIndex (k % 128) + 12 + e := by
    rw [leaf_pc_local]
  rw [eq]
  exact tail_site ⟨k % 128, Nat.mod_lt k (by decide)⟩ e he

private theorem fetch_tail (k e : Nat) (he : e < 6) (op : Instr)
    (eq : tailAt (k % 128) e = op) (s : MachineState)
    (pc : s.pc = pcAt (leafPC k + 12 + e)) :
    fetch commitImage s = some (.base op) := by
  have site := tail_word k e he
  rw [eq] at site
  exact site s pc

private theorem add_pres (s : MachineState) (rd rs1 rs2 r : Reg) (h : rd ≠ r) :
    (execInstrBr s (.ADD rd rs1 rs2)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h]

private theorem addi_pres (s : MachineState) (rd rs r : Reg) (imm : BitVec 12) (h : rd ≠ r) :
    (execInstrBr s (.ADDI rd rs imm)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h]

private theorem beq_pres (s : MachineState) (r : Reg) :
    (execInstrBr s (.BEQ .x20 .x0 (BitVec.ofNat 13 8))).getReg r = s.getReg r := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.getReg_setPC]

private theorem jal_pres (s : MachineState) (r : Reg) (h : .x0 ≠ r) :
    (execInstrBr s (.JAL .x0 (BitVec.ofNat 21 2090936))).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h]

private theorem step_pc (s : MachineState) (op : Instr) (n : Nat)
    (pc : s.pc = pcAt n) (h : (execInstrBr s op).pc = s.pc + 4) :
    (execInstrBr s op).pc = pcAt (n + 1) := by
  rw [h, pc, pc_succ]

private theorem sext1536 :
    signExtend12 (BitVec.ofNat 12 1536) = BitVec.ofNat 64 1536 := by
  decide

private theorem tile_end_pc (k : Nat) (z : k % 128 = 127) : leafPC k = 5660 := by
  unfold leafPC
  rw [z]

theorem hashed_leaf (h : Compression) {s : MachineState} {k : Nat}
    (a : AtLeaf s k) (hk : k < LENGTH) :
    LeafRegs (finalLeaf h s k) k ∧ (finalLeaf h s k).pc = pcAt (leafPC k + 12) := by
  have pc0 : s.pc = pcAt (leafPC k) := by rw [a.pc, ite_eq_left hk]
  let c0 : Fin 4 := 0
  let c1 : Fin 4 := 1
  let c2 : Fin 4 := 2
  let c3 : Fin 4 := 3
  let u := siteResult h s k c0.val
  let b := siteResult h u k c1.val
  let c := siteResult h b k c2.val
  have ru : LeafRegs u k := reply_regs a.toLeafRegs c0 _
  have rb : LeafRegs b k := reply_regs ru c1 _
  have rc : LeafRegs c k := reply_regs rb c2 _
  have last : LeafRegs (siteResult h c k c3.val) k := reply_regs rc c3 _
  have pc1 : u.pc = pcAt (leafPC k + 3) := leafReplyPC s k c0.val (leafPC k) _ pc0
  have pc2 : b.pc = pcAt (leafPC k + 6) := leafReplyPC u k c1.val (leafPC k + 3) _ pc1
  have pc3 : c.pc = pcAt (leafPC k + 9) := leafReplyPC b k c2.val (leafPC k + 6) _ pc2
  have pc4 : (siteResult h c k c3.val).pc = pcAt (leafPC k + 9 + 3) :=
    leafReplyPC c k c3.val (leafPC k + 9) _ pc3
  have fin : siteResult h c k c3.val = finalLeaf h s k := by
    simp only [finalLeaf, c0, c1, c2, c3]
    rfl
  rw [fin] at last pc4
  refine ⟨last, ?_⟩
  rw [show leafPC k + 9 + 3 = leafPC k + 12 by omega] at pc4
  exact pc4

theorem leafDecPublic (k : Nat) (hk:k<LENGTH) (wrap:(k+1)%128=0) :
    BitVec.ofNat 64 (tileCounter k)+signExtend12 4095=BitVec.ofNat 64 (tileCounter (k+1)) := by
  have b:k<16777216:=hk
  have nz:1≤tileCounter k:=by unfold tileCounter;omega
  rw [counter_succ k hk,if_pos wrap]
  rw [show signExtend12 (4095:BitVec 12)= -(1:Word) by decide,←BitVec.sub_eq_add_neg]
  change BitVec.ofNat 64 (tileCounter k)-BitVec.ofNat 64 1=_
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) nz

theorem leafZeroTest (k : Nat) (hk:k<LENGTH) (wrap:(k+1)%128=0) :
    (BitVec.ofNat 64 (tileCounter (k+1))==0)=decide (k+1=LENGTH) := by
  have b:k<16777216:=hk
  by_cases stop:k+1=LENGTH
  · rw [stop];decide
  · have lim : 0<tileCounter (k+1) ∧ tileCounter (k+1)<2^64:=by
      change k+1≠16777216 at stop;unfold tileCounter;omega
    have ne : BitVec.ofNat 64 (tileCounter (k+1))≠0:=by
      intro e;have q:=congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lim.2] at q
      change tileCounter (k+1)=0 at q;omega
    rw [decide_eq_false stop];exact beq_eq_false_iff_ne.mpr ne


/-- One stage of the deterministic cursor tail. -/
def advanceWhen (on : Prop) [Decidable on] (s : MachineState) (rd : Reg) (v : Word) :=
  if on then (s.setReg rd v).setPC (s.pc+4) else s

theorem advanceRead (on : Prop) [Decidable on] (s : MachineState) (rd q : Reg) (v : Word) (nz:rd≠.x0) :
    (advanceWhen on s rd v).getReg q=(if rd=q ∧ on then v else s.getReg q) := by
  by_cases b:on
  · rw [advanceWhen,if_pos b,MachineState.getReg_setPC]
    by_cases e:rd=q
    · subst rd;rw [if_pos ⟨rfl,b⟩];exact MachineState.getReg_setReg_eq nz
    · rw [if_neg (fun h=>e h.1)];exact MachineState.getReg_setReg_ne _ _ _ _ e
  · rw [advanceWhen,if_neg b,if_neg (fun h=>b h.2)]

def movedMsg (s : MachineState) (k : Nat) :=
  advanceWhen ((k+1)%16=0) s .x21 (s.getReg .x21+s.getReg .x25)
def movedRow (s : MachineState) (k : Nat) :=
  advanceWhen ((k+1)%32=0) (movedMsg s k) .x22 (s.getReg .x22+s.getReg .x26)
def movedNode (s : MachineState) (k : Nat) :=
  advanceWhen ((k+1)%32=0) (movedRow s k) .x23 (s.getReg .x23+signExtend12 1536)
def movedCount (s : MachineState) (k : Nat) :=
  advanceWhen ((k+1)%128=0) (movedNode s k) .x20 (s.getReg .x20+signExtend12 4095)

def leafTail (s : MachineState) (k : Nat) :=
  (movedCount s k).setPC (pcAt (if k+1<LENGTH then leafPC (k+1) else 5678))
def afterLeaf (h : Compression) (s : MachineState) (k : Nat) := leafTail (finalLeaf h s k) k

theorem movedRead (s : MachineState) (k : Nat) (q : Reg) :
    (movedCount s k).getReg q=
      (if .x20=q ∧ (k+1)%128=0 then s.getReg .x20+signExtend12 4095 else
       if .x23=q ∧ (k+1)%32=0 then s.getReg .x23+signExtend12 1536 else
       if .x22=q ∧ (k+1)%32=0 then s.getReg .x22+s.getReg .x26 else
       if .x21=q ∧ (k+1)%16=0 then s.getReg .x21+s.getReg .x25 else s.getReg q) := by
  unfold movedCount movedNode movedRow movedMsg
  rw [advanceRead _ _ .x20 q _ (by decide),advanceRead _ _ .x23 q _ (by decide),
      advanceRead _ _ .x22 q _ (by decide),advanceRead _ _ .x21 q _ (by decide)]

theorem after_at (h : Compression) {s : MachineState} {k : Nat} (a : AtLeaf s k) (hk:k<LENGTH) :
    AtLeaf (afterLeaf h s k) (k+1) := by
  obtain ⟨r,pc⟩:=hashed_leaf h a hk
  let t:=finalLeaf h s k
  have get (q : Reg) : (afterLeaf h s k).getReg q=(movedCount t k).getReg q:=MachineState.getReg_setPC
  refine ⟨?_,rfl⟩
  constructor <;> rw [get,movedRead] <;> simp only [reduceCtorEq,false_and,true_and,ite_false,ite_true]
  · rw [msg_succ k hk,r.msg,r.strideMsg];split <;> first | exact (BitVec.ofNat_add ..).symm | rfl
  · rw [row_succ k hk,r.row,r.strideRow];split <;> first | exact (BitVec.ofNat_add ..).symm | rfl
  · rw [node_succ k hk,r.node,show signExtend12 (1536:BitVec 12)=BitVec.ofNat 64 1536 by decide];split <;> first | exact (BitVec.ofNat_add ..).symm | rfl
  · rw [r.counter];split
    next yes=>exact leafDecPublic k hk yes
    next no=>rw [counter_succ k hk,if_neg no,Nat.sub_zero]
  · exact r.mode
  · exact r.len
  · exact r.kind
  · exact r.baseMsg
  · exact r.root
  · exact r.td
  · exact r.rows
  · exact r.scratch
  · exact r.strideMsg
  · exact r.strideRow
  · exact r.spare
end CommitGolfCandidate.Chained.BinaryMachine
