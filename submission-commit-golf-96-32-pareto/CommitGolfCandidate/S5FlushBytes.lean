import CommitGolfCandidate.S5BatchFrame
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Writer (PackedPrefix)
open Reader (window)
def byteOf (v j : Nat) : Byte:=BitVec.ofNat 8 (v/2^(8*j))

theorem packed_byte {s : MachineState} {n v : Nat} (c : PackedPrefix s proofBase n v) (j : Nat) (bound : j<8*(n/64)) :
    byteAt s (proofBase+j)=byteOf v j := by
  have base : proofBase%8=0:=by decide
  have ix : 8*((proofBase+j)/8)=proofBase+8*(j/8):=by omega
  have rem : (proofBase+j)%8=j%8:=by omega
  rw [byte_word,ix,rem]
  apply BitVec.eq_of_toNat_eq
  change (((wordAt s (proofBase+8*(j/8))) >>> ((j%8)*8)).truncate 8).toNat=_
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,byteOf,BitVec.toNat_ofNat]
  rw [Nat.mul_comm (j%8) 8]
  rw [c.words _ (by omega),Reader.window_high _ _ _ _ (by omega)]
  rw [Reader.window_low _ _ _ _ (by omega)]
  change window v (64*(j/8)+8*(j%8)) 8=window v (8*j) 8
  rw [show 64*(j/8)+8*(j%8)=8*j by omega]

structure FlushState (s : MachineState) (valid : Prop) (v i : Nat) : Prop where
  pc : s.pc=pcAt 381
  dest : s.getReg .x19=W (proofBase+69392+i)
  bits : s.getReg .x24=W (34-8*i)
  base : s.getReg .x18=W proofBase
  held : valid → (s.getReg .x23).toNat=v/2^(8*(69392+i))
  bytes : valid → ∀ j<69392+i,byteAt s (proofBase+j)=byteOf v j

theorem flush_start {s : MachineState} {valid : Prop} {v : Nat} (cur : ProofCursor valid s 555170 v)
    (pc : s.pc=pcAt 381) (base : s.getReg .x18=W proofBase) : FlushState s valid v 0 :=
  ⟨pc,cur.ptr,cur.count,base,fun yes=>(cur.payload yes).held,fun yes j hj=>packed_byte (cur.payload yes) j hj⟩

def flushPath : PathCode := [(381,.ADDI .x6 .x0 8),(382,.BLTU .x24 .x6 24),(383,.SB .x19 .x23 0),
  (384,.ADDI .x19 .x19 1),(385,.SRLI .x23 .x23 8),(386,.ADDI .x24 .x24 4088),(387,.JAL .x0 2097128)]
def flushStop : PathCode := [(381,.ADDI .x6 .x0 8),(382,.BLTU .x24 .x6 24)]

private theorem guard (s : MachineState) (hold : Nat) (small : hold≤34) (pc : s.pc=pcAt 381) (bits : s.getReg .x24=W hold) :
    let t:=pathEnd s flushStop
    pathReady s flushStop ∧ t= (execInstrBr s (.ADDI .x6 .x0 8)).setPC (pcAt (if hold<8 then 388 else 383)) := by
  let u:=execInstrBr s (.ADDI .x6 .x0 8)
  have ip : u.pc=pcAt 382:=by change s.pc+4=_;rw [pc];rfl
  have cond : BitVec.ult (u.getReg .x24) (u.getReg .x6)=decide (hold<8) := by
    change BitVec.ult (s.getReg .x24) 8#64=_
    rw [bits];simp only [BitVec.ult,W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show hold<2^64 by omega)]
  refine ⟨⟨pc,rfl,rfl,ip,rfl,rfl,True.intro⟩,?_⟩
  change (if BitVec.ult (u.getReg .x24) (u.getReg .x6) then u.setPC (u.pc+signExtend13 24) else u.setPC (u.pc+4))=_
  rw [cond,ip];by_cases b : hold<8 <;> simp only [b,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false] <;> rfl

theorem flush_guard (s : MachineState) (hold : Nat) (small : hold≤34) (pc : s.pc=pcAt 381) (bits : s.getReg .x24=W hold) :
    let t:=pathEnd s flushStop
    Runs s t 2 2 ∧ t.pc=pcAt (if hold<8 then 388 else 383) ∧ t.mem=s.mem ∧
      ∀ q,q≠.x6 → t.getReg q=s.getReg q := by
  obtain ⟨ready,last⟩:=guard s hold small pc bits
  refine ⟨path_run _ true _ _ (by decide +kernel) ready,?_,?_,?_⟩
  · rw [last];rfl
  · rw [last];rfl
  · intro q h;rw [last];exact MachineState.getReg_setPC.trans (MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ h.symm))
end CommitGolfCandidate.S5Machine.Open
