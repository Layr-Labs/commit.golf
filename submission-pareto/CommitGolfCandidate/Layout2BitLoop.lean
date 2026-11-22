import CommitGolfCandidate.Layout2EffectsBits
import CommitGolfCandidate.Layout2Invariant

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.GroupedOpening.Wide
set_option maxRecDepth 8000
open TwoPermutationPrototype.GroupedOpening (access_ok)
set_option maxHeartbeats 2000000

def bitScratch : List Reg := [.x6,.x19,.x28,.x29,.x30]

private theorem index_word (x : Nat) (small : x<65536) :
    (BitVec.ofNat 16 x).zeroExtend 64=addr x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (show x<2^64 by omega)]

private theorem index_addr (x : Nat) (small : x<65536) :
    ((addr x >>> (3:Nat)) + addr scratchBase)=addr (scratchBase+x/8) := by
  have shift : addr x >>> (3:Nat)=addr (x/8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show x<2^64 by omega),
      Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt (show x/8<2^64 by omega)]
  rw [shift,addr_add,Nat.add_comm]

private theorem index_lane (x : Nat) (small : x<65536) :
    ((addr x &&& 7#64).toNat % 64)=x%8 := by
  rw [BitVec.toNat_and,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show x<2^64 by omega),
    show (7#64).toNat=2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by omega)

structure BitCursor (τ : Tables) (r tb j : Nat) (source : Nat→Byte) (s m : MachineState) (b : Nat) : Prop where
  next : m.pc=(if b=8 then pc 782 else pc 770)
  table : m.getReg .x19=addr (tb+2*(8*j+b))
  lane : m.getReg .x28=addr b
  value : m.getReg .x6=acc τ r source j b
  memory : m.mem=s.mem
  kept : Kept bitScratch s m

theorem bit_loop {I τ r p tb B} (program : Program I) (cfg : Span τ r p tb B)
    (s : MachineState) (j : Nat) (source : Nat→Byte) (inside : j<B)
    (here : s.pc=pc 770) (scratch : s.getReg .x10=addr scratchBase)
    (eight : s.getReg .x21=8) (head : s.getReg .x19=addr (tb+2*(8*j)))
    (lane : s.getReg .x28=0) (empty : s.getReg .x6=0)
    (table : SpanTable τ r tb B s) (copied : ∀ q, q<B → byte s (scratchBase+q)=source q) :
    ∃ t, Runs I s t 96 96 ∧ BitCursor τ r tb j source s t 8 := by
  have initial : BitCursor τ r tb j source s s 0 :=
    ⟨by simpa using here,by simpa using head,lane,empty,rfl,Kept.refl _ _⟩
  apply loop 8 12 12 (fun b t=>BitCursor τ r tb j source s t b) s initial
  intro b small m h
  have start : m.pc=pc Block.bitStep.start := by simpa [Block.start,show b≠8 by omega] using h.next
  obtain ⟨regs,mem,pcE,access⟩:=effects_bitStep m start
  let fromBit:=τ r (8*j+b)
  have iFit : 8*j+b<8*B := by omega
  obtain ⟨idx,wordFit⟩:=cfg.index (8*j+b) iFit
  change fromBit<8*B at idx
  change fromBit<65536 at wordFit
  have half : (m.getHalfword (m.getReg .x19)).zeroExtend 64=addr fromBit := by
    rw [h.table, (table.mem h.memory) _ iFit]
    exact index_word _ wordFit
  have sreg : m.getReg .x10=addr scratchBase := (h.kept _ (by decide)).trans scratch
  have ad : (((m.getHalfword (m.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + m.getReg .x10=addr (scratchBase+fromBit/8) := by
    rw [half,sreg,index_addr _ wordFit]
  have load : m.getByte (addr (scratchBase+fromBit/8))=source (fromBit/8) := by
    simpa only [byte,MachineState.getByte,MachineState.getMem,h.memory] using copied (fromBit/8) (by omega)
  have ready : Ready m Block.bitStep.ops := by
    apply access.mpr
    change accessValid (m.getReg .x19) 2=true ∧ accessValid _ 1=true
    rw [ad,h.table]
    have e:=cfg.even;have room:=cfg.room;have separated:=cfg.separated;have below:=cfg.tableAfter
    exact ⟨access_ok _ 2 (by omega) (by omega),access_ok _ 1 (by omega) (by omega)⟩
  let t:=after .bitStep m
  refine ⟨t,runBlock program .bitStep m start ready,?_,?_,?_,?_,mem.trans h.memory,?_⟩
  · rw [pcE]
    have lim : m.getReg .x21=8#64 := (h.kept _ (by decide)).trans eight
    simp only [pcOut,h.lane,lim,show addr b+1#64=addr (b+1) from addr_add _ _]
    by_cases endByte : b+1=8
    · simp [endByte,addr]
    · have diff : addr (b+1)≠8#64 := (addr_ne (a:=b+1) (b:=8) (by omega) (by decide)).2 endByte
      simp [diff,endByte]
  · rw [regs];simp only [regOut,ite_true,reduceCtorEq,ite_false,h.table]
    change addr _+addr 2=_
    rw [addr_add];congr 1 <;> omega
  · rw [regs];simp only [regOut,ite_true,h.lane];exact addr_add _ _
  · rw [regs]
    simp only [regOut,reduceCtorEq,ite_false,ite_true,half,sreg,index_addr fromBit wordFit,load,h.lane,h.value]
    have shiftLane : (addr b).toNat%64=b := by simp [addr,Nat.mod_eq_of_lt (show b<2^64 by omega),Nat.mod_eq_of_lt (show b<64 by omega)]
    rw [index_lane _ wordFit,shiftLane];rfl
  · apply h.kept.trans
    intro reg free
    have avoid : reg≠.x6 ∧ reg≠.x19 ∧ reg≠.x28 ∧ reg≠.x29 ∧ reg≠.x30 := by
      simpa [bitScratch] using free
    rw [regs]
    simp only [regOut,if_neg (Ne.symm avoid.1),if_neg (Ne.symm avoid.2.1),if_neg (Ne.symm avoid.2.2.1),
      if_neg (Ne.symm avoid.2.2.2.1),if_neg (Ne.symm avoid.2.2.2.2)]

end CommitGolfCandidate.Layout2
