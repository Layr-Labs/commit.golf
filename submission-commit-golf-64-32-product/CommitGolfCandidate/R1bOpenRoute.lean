import CommitGolfCandidate.R1bRoutes

namespace CommitGolfCandidate.R1b.Opening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open R1bPC (pcAt)
set_option maxRecDepth 16384

def packNow (n len : Nat) : Bool := decide (n=128 ∧ 67488<len)
def extra (n len : Nat) : Nat := if n≠128 then 5 else if len≤67488 then 8 else 11192
def returnPC := pcAt 12624

private theorem relative (i j : Nat) (d : BitVec 21) (s : MachineState)
    (bound : i<12697) (here : s.pc=pcAt i) (word : stands .opening i (.JAL .x0 d))
    (target : pcAt i+signExtend21 d=pcAt j) : Runs .opening s (s.setPC (pcAt j)) 1 1 := by
  apply one bound here _ (stood word)
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,MachineState.setReg,here,target]

private def step (s : MachineState) (i : Instr) := execInstrBr s i

structure Routed (n len : Nat) (s t : MachineState) : Prop where
  run : Runs .opening s t (if n≠128 then 4 else 7)
    (if n≠128 then 4 else 7)
  pc : t.pc=if packNow n len then pcAt 1443 else returnPC
  packet : packNow n len=true → t.getReg .x18=W proofBase
  length : t.getReg .x11=s.getReg .x11
  memory : t.mem=s.mem

theorem route (n len : Nat) (s : MachineState) (atPC : s.pc=pcAt 664)
    (nReg : s.getReg .x16=W n) (nBound : n<2^64) (lReg : s.getReg .x11=W len) (lBound : len<2^64)
    (base : s.getReg .x20=W proofBase) : ∃ t,Routed n len s t := by
  let a:=s.setPC (pcAt 1435)
  let b:=step a (.ADDI .x6 .x0 128)
  have oneA:=Codec.openEnter s atPC
  have oneB:=one (c:=.opening) (n:=1435) (by decide) (show a.pc=pcAt 1435 from rfl)
    (.ADDI .x6 .x0 128) (by apply stood; decide) (show ordinaryStep a _=some b from rfl)
  have test : b.getReg .x16=b.getReg .x6 ↔ n=128 := by
    change s.getReg .x16=128 ↔ _;rw [nReg]
    constructor
    · intro h;exact wordNumber nBound (by decide : 128<2^64) h
    · rintro rfl;rfl
  by_cases batch : n=128
  · let c:=b.setPC (pcAt 1438)
    have oneC:=one (c:=.opening) (n:=1436) (by decide) (show b.pc=pcAt 1436 from rfl)
      (.BEQ .x16 .x6 8) (by apply stood; decide) (show ordinaryStep b _=some c by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,c,test.mpr batch,show b.pc=pcAt 1436 from rfl,pcAt,signExtend13])
    let d:=step c (.LUI .x6 16)
    let e:=step d (.ADDI .x6 .x6 1952)
    have oneD:=one (c:=.opening) (n:=1438) (by decide) (show c.pc=pcAt 1438 from rfl)
      (.LUI .x6 16) (by apply stood; decide) (show ordinaryStep c _=some d from rfl)
    have oneE:=one (c:=.opening) (n:=1439) (by decide) (show d.pc=pcAt 1439 from rfl)
      (.ADDI .x6 .x6 1952) (by apply stood; decide) (show ordinaryStep d _=some e from rfl)
    have cmp : (e.getReg .x6).ult (e.getReg .x11)=decide (67488<len) := by
      have lim : e.getReg .x6=67488#64 := by change 65536#64+signExtend12 1952=_;decide
      have old : e.getReg .x11=s.getReg .x11 := rfl
      have natural : (W len).toNat=len := by rw [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lBound]
      change decide ((e.getReg .x6).toNat < (e.getReg .x11).toNat)=_
      rw [lim,old,lReg,natural,show (67488#64).toNat=67488 by decide]
    have ran:=(oneA.trans oneB |>.trans oneC |>.trans oneD |>.trans oneE)
    by_cases long : 67488<len
    · let f:=e.setPC (pcAt 1442)
      let t:=step f (.ADDI .x18 .x20 0)
      have oneF:=one (c:=.opening) (n:=1440) (by decide) (show e.pc=pcAt 1440 from rfl)
        (.BLTU .x6 .x11 8) (by apply stood; decide) (show ordinaryStep e _=some f by
          simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,cmp,long,show e.pc=pcAt 1440 from rfl,f,pcAt,signExtend13])
      have last:=one (c:=.opening) (n:=1442) (by decide) (show f.pc=pcAt 1442 from rfl)
        (.ADDI .x18 .x20 0) (by apply stood; decide) (show ordinaryStep f _=some t from rfl)
      refine ⟨t,⟨by simpa [batch,instructionCycles,Nat.not_le.mpr long] using (ran.trans oneF).trans last,?_,?_,rfl,rfl⟩⟩
      · simp [packNow,batch,long,t,f,pcAt,step,execInstrBr,MachineState.setPC]
      · intro _;exact (BitVec.add_zero (s.getReg .x20)).trans base
    · let f:=e.setPC (pcAt 1441)
      have oneF:=one (c:=.opening) (n:=1440) (by decide) (show e.pc=pcAt 1440 from rfl)
        (.BLTU .x6 .x11 8) (by apply stood; decide) (show ordinaryStep e _=some f by
          simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,cmp,long,show e.pc=pcAt 1440 from rfl,f,pcAt,signExtend13])
      have last:=relative 1441 12624 44732 f (by decide) rfl (by decide) (by decide)
      exact ⟨f.setPC (pcAt 12624),⟨by simpa [batch,instructionCycles,Nat.le_of_not_gt long] using (ran.trans oneF).trans last,
        by simp [packNow,long,returnPC,MachineState.setPC],by simp [packNow,long],rfl,rfl⟩⟩
  · let c:=b.setPC (pcAt 1437)
    have oneC:=one (c:=.opening) (n:=1436) (by decide) (show b.pc=pcAt 1436 from rfl)
      (.BEQ .x16 .x6 8) (by apply stood; decide) (show ordinaryStep b _=some c by
        simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,c,mt test.mp batch,show b.pc=pcAt 1436 from rfl,pcAt])
    have last:=relative 1437 12624 44748 c (by decide) rfl (by decide) (by decide)
    exact ⟨c.setPC (pcAt 12624),⟨by simpa [batch,instructionCycles] using ((oneA.trans oneB).trans oneC).trans last,
      by simp [packNow,batch,returnPC,MachineState.setPC],by simp [packNow,batch],rfl,rfl⟩⟩

end CommitGolfCandidate.R1b.Opening
