import CommitGolfCandidate.Stage3cPairDraw
import CommitGolfCandidate.Stage3cRow

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option Elab.async false

def pairCount := 8388608
def pairAddress (p : Nat) := rowBase+184*p+72
abbrev destination := pairAddress
private theorem pair_address_valid (p : Nat) (hi : p<pairCount) :
    pairAddress p%8=0 ∧ pairAddress p+40≤MEMORY_BYTES := by
  change p<8388608 at hi
  change (5905588224+184*p+72)%8=0 ∧ 5905588224+184*p+72+40≤2^36
  omega


structure AtPair (s : MachineState) (p : Nat) : Prop where
  pc : s.pc = pcAt (if p < pairCount then 12+2*(p%2048) else 4111)
  counter : s.getReg .x20 = BitVec.ofNat 64 (4096-p/2048)
  selector : s.getReg .x5 = 2
  bytes : s.getReg .x11 = 40
  dest : s.getReg .x10 = BitVec.ofNat 64 (destination p)

def decrement (s : MachineState) := execInstrBr s (.ADDI .x20 .x20 4095)
def latchState (s : MachineState) (p : Nat) :=
  (decrement s).setPC (pcAt (if p+1<pairCount then 12 else 4111))
def nextPair (p : Nat) (s : MachineState) (w : Draw40) :=
  if p%2048=2047 then latchState (randomStep s w) p else randomStep s w
def extra (p : Nat) := if p+1<pairCount then 3 else 2
def pairSteps (p : Nat) := if p%2048=2047 then 2+extra p else 2
def pairCycles (p : Nat) := if p%2048=2047 then 7+extra p else 7
theorem random_registers (s : MachineState) (w : Draw40) :
    (randomStep s w).pc = s.pc + 8 ∧
    (randomStep s w).getReg .x10 = s.getReg .x10 + 184 ∧
    ∀ r, r ≠ .x10 → (randomStep s w).getReg r = s.getReg r := by
  constructor
  · change (s.pc+4)+4 = s.pc+8
    rw [BitVec.add_assoc]
    rfl
  constructor
  · simp only [randomStep, execInstrBr, signExtend12, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), writeBits_register]
    rfl
  · intro r hr
    simp only [randomStep, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ hr.symm, writeBits_register]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem latch_decode :
    decoded 4108 = some (.base (.ADDI .x20 .x20 4095)) ∧
    decoded 4109 = some (.base (.BEQ .x20 .x0 8)) ∧
    decoded 4110 = some (.base (.JAL .x0 2080760)) := by
  decide +kernel

private theorem latch_run (s : MachineState) (p : Nat) (ip : s.pc=pcAt 4108)
    (zero : (decrement s).getReg .x20=0 ↔ ¬p+1<pairCount) (fuel : Nat) :
    execute commitImage (fuel+extra p) s true =
      (do let r←execute commitImage fuel (latchState s p) true;return r.charge (extra p) 0) := by
  let t:=decrement s
  have here : t.pc=pcAt 4109 := by change s.pc+4=_;rw [ip];rfl
  have f0 : fetch commitImage s=some (.base (.ADDI .x20 .x20 4095)) :=
    decoded_site (by decide) latch_decode.1 s ip
  have f1 : fetch commitImage t=some (.base (.BEQ .x20 .x0 8)) :=
    decoded_site (by decide) latch_decode.2.1 t here
  by_cases more : p+1<pairCount
  · have nz : t.getReg .x20≠0:=fun e=>(zero.mp e) more
    let u:=t.setPC (pcAt 4110)
    have turn : ordinaryStep t (.base (.BEQ .x20 .x0 8))=some u := by
      change some (if (t.getReg .x20==t.getReg .x0) then _ else t.setPC (t.pc+4))=_
      rw [show t.getReg .x0=0 from rfl,beq_eq_false_iff_ne.mpr nz,if_neg (by decide : ¬false=true),here];rfl
    have f2 : fetch commitImage u=some (.base (.JAL .x0 2080760)) :=
      decoded_site (by decide) latch_decode.2.2 u rfl
    have back : ordinaryStep u (.base (.JAL .x0 2080760))=some (latchState s p) := by
      change some (t.setPC (pcAt 4110+signExtend21 2080760))=some (latchState s p)
      rw [show pcAt 4110+signExtend21 2080760=pcAt 12 by decide,latchState,if_pos more]
    rw [extra,if_pos more,execute_ordinary_step _ _ _ t _ _ f0 rfl,
      execute_ordinary_step _ _ _ u _ _ f1 turn,execute_ordinary_step _ _ _ _ _ _ f2 back]
    simp [Execution.charge,instructionCycles,bind_assoc,←Nat.add_assoc]
  · have eq:=zero.mpr more
    have turn : ordinaryStep t (.base (.BEQ .x20 .x0 8))=some (latchState s p) := by
      change some (if (t.getReg .x20==t.getReg .x0) then t.setPC (t.pc+signExtend13 8) else _)=_
      rw [show t.getReg .x0=0 from rfl,eq,beq_self_eq_true,if_pos (rfl : true=true),here,latchState,if_neg more];rfl
    rw [extra,if_neg more,execute_ordinary_step _ _ _ t _ _ f0 rfl,execute_ordinary_step _ _ _ _ _ _ f1 turn]
    simp [Execution.charge,instructionCycles,bind_assoc,←Nat.add_assoc]

theorem latch_counter (p : Nat) (s : MachineState) (inside : p<pairCount) (atEnd : p%2048=2047)
    (ctr : s.getReg .x20=BitVec.ofNat 64 (4096-p/2048)) :
    (decrement s).getReg .x20=BitVec.ofNat 64 (4096-(p+1)/2048) := by
  change p<8388608 at inside
  change s.getReg .x20+(-1)=_
  rw [ctr,←BitVec.sub_eq_add_neg]
  exact (BitVec.ofNat_sub_ofNat_of_le (w:=64) (4096-p/2048) 1 (by decide) (by omega)).trans
    (congrArg (BitVec.ofNat 64) (by omega))

theorem execute_one_pair {s : MachineState} {p : Nat} (a : AtPair s p) (inside : p < pairCount)
    (fuel : Nat) :
    execute commitImage (fuel+pairSteps p) s true =
      (do let w ← draw40
          let r ← execute commitImage fuel (nextPair p s w) true
          return r.charge (pairCycles p) 0) := by
  have ip := a.pc
  rw [if_pos inside] at ip
  have valid : randomArgumentsValid s = true := by
    obtain ⟨align, ceiling⟩ := pair_address_valid p inside
    have h : pairAddress p < 2^64 := by change pairAddress p + 40 ≤ 2^36 at ceiling; omega
    simp only [randomArgumentsValid, rangeValid, a.bytes, a.dest, destination, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h, align, decide_true, Bool.true_and]
    exact decide_eq_true ceiling
  by_cases endOfTile : p%2048=2047
  · unfold pairSteps pairCycles nextPair
    simp only [if_pos endOfTile]
    rw [show fuel+(2+extra p)=fuel+extra p+2 by omega,execute_pair s _ (fuel+extra p) (Nat.mod_lt _ (by decide)) ip a.selector a.bytes valid]
    apply bind_congr;intro w
    have pc : (randomStep s w).pc=pcAt 4108 := by rw [(random_registers s w).1,ip,endOfTile];rfl
    have newc:=latch_counter p (randomStep s w) inside endOfTile (((random_registers s w).2.2 _ (by decide)).trans a.counter)
    have zero : (decrement (randomStep s w)).getReg .x20=0 ↔ ¬p+1<pairCount := by
      rw [newc];change p<8388608 at inside
      constructor
      · intro e;have val:=congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at val
        change _=0 at val;change ¬p+1<8388608;omega
      · intro e;change ¬p+1<8388608 at e;rw [show 4096-(p+1)/2048=0 by omega];rfl
    rw [latch_run _ p pc zero]
    simp [bind_assoc,Execution.charge,←Nat.add_assoc,Nat.add_comm (extra p) 7]
  · simpa only [pairSteps,pairCycles,nextPair,if_neg endOfTile] using execute_pair s _ fuel (Nat.mod_lt _ (by decide)) ip a.selector a.bytes valid

end CommitGolfCandidate.Chained.BinaryMachine
