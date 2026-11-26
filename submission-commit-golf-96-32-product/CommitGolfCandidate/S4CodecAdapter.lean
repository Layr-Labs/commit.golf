import CommitGolfCandidate.S4CodecSites
import CommitGolfCandidate.S4CodecRun
import CommitGolfCandidate.S4OutputFrame
import CommitGolfCandidate.S4Frames
namespace CommitGolfCandidate.S4.Codec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Late (pcAt)
section
attribute [local irreducible] List.range List.finRange

theorem packedProof (s t : MachineState) (wide : Proof) (len : wide.length=70410)
    (before : Open.Contains s proofBase wide) (afterMem : Mem false s t 330 1309) :
    Open.Contains t proofBase (Carry.packed wide) := by
  intro j bj
  have small : j<70080:=by rwa [Carry.packed_length] at bj
  have valid (a : Nat) (ha : a<70410) : original s a=Carry.read wide a:=by
    have inside : a<wide.length:=by omega
    exact (before a inside).trans (by rw [Carry.read,List.getElem?_eq_getElem inside,Option.getD_some])
  have r:=afterMem.atByte j (by omega)
  rw [Carry.encoded,packed_agrees _ _ valid j small,←Carry.packed_byte _ _ small] at r
  simpa only [Carry.read,List.getElem?_eq_getElem bj,Option.getD_some] using r

private theorem initialAway (x : CheckInput) (ys : Proof) (q : Nat) (b : q<2^64)
    (outside : (q<proofBase ∨ proofBase+x.proof.length≤q) ∧ (q<proofBase ∨ proofBase+ys.length≤q)) :
    byte (initial x) q=byte (initial {x with proof:=ys}) q := by
  have old:=initial_input_byte Late.submission .check x q b
  have new:=initial_input_byte Late.submission .check {x with proof:=ys} q b
  apply old.trans;apply Eq.trans _ new.symm
  unfold inputByte
  let head:=[fixedBuffer rootBase x.commitment,positionsBuffer indexBase x.positions,valuesBuffer valueBase x.positions x.values]
  let pf (bs : Proof) : InputBuffer:=⟨proofBase,bs.length,fun j=>Carry.read bs j⟩
  let pred (buf : InputBuffer):=decide (buf.address≤q ∧ q<buf.address+buf.length)
  have no (bs : Proof) (h : q<proofBase ∨ proofBase+bs.length≤q) :
      (head++[pf bs]).find? pred=head.find? pred:=by
    have bad : pred (pf bs)=false:=decide_eq_false (by change ¬(proofBase≤q ∧ q<proofBase+bs.length);omega)
    rw [List.find?_append];cases hit : head.find? pred <;> simp [bad]
  change (match (head++[pf x.proof]).find? pred with | some b=>b.byteAt (q-b.address) | none=>_)=
    (match (head++[pf ys]).find? pred with | some b=>b.byteAt (q-b.address) | none=>_)
  rw [no x.proof outside.1,no ys outside.2]

theorem decodedInput (x : CheckInput) (s t : MachineState) (batch : x.positions.card=BATCH) (len : x.proof.length=70080)
    (initialMem : s.mem=(initial x).mem) (step : Mem true s t 330 1309) : InputsStill (wideInput x) t := by
  have honest : wideInput x={x with proof:=Carry.wide x.proof}:=by simp [wideInput,batch,len]
  rw [honest];intro q _ bq
  have orig (j : Nat) : byte s j=byte (initial x) j:=by simp only [byte,MachineState.getByte,MachineState.getMem,initialMem]
  by_cases range : proofBase≤q ∧ q<proofBase+70410
  · let j:=q-proofBase
    have low : j<70410:=by dsimp [j];omega
    have pos : q=proofBase+j:=by dsimp [j];omega
    have same (n : Nat) (hn : n<70080) : original s n=Carry.read x.proof n:=by
      have bound : n<x.proof.length:=by omega
      have rd:=proof_byte x n bound (by unfold proofBase;omega)
      rw [original,orig,rd,Carry.read,List.getElem?_eq_getElem bound,Option.getD_some]
    rw [pos,step.atByte _ low,Carry.decoded _ _ low,decoded_agrees _ _ same _ low,←Carry.wide_byte _ _ low]
    let y:CheckInput:={x with proof:=Carry.wide x.proof}
    have inside : j<y.proof.length:=by change j<(Carry.wide _).length;rwa [Carry.wide_length]
    exact (by rw [Carry.read,List.getElem?_eq_getElem inside,Option.getD_some] : Carry.read y.proof j=y.proof[j]).trans
      (proof_byte y j inside (by omega)).symm
  · rw [step q bq,if_neg range,orig]
    apply initialAway _ _ _ bq
    rw [Carry.wide_length,len];omega

end

def restoreOps : List Sym.Calc := [.addi .x8 .x0 1824,.slli .x8 .x8 11,.addi .x8 .x8 2,.slli .x8 .x8 11,.addi .x8 .x8 32]

theorem decodeMachine (s : MachineState) (pc : s.pc=pcAt 2667) (ptr : s.getReg .x18=W proofBase) :
    ∃ t, Runs .check s t 9505 9505 ∧ t.pc=pcAt 2668 ∧ t.getReg .x8=W indexBase ∧
      Mem true s t 330 1309 ∧ (∀ r,stable r → t.getReg r=s.getReg r) := by
  have go:=jump .check 2667 12988 s pc (by decide)
  let a:=s.setPC (pcAt 12988)
  obtain ⟨u,frame,ip,body⟩:=run byteSites true a rfl ptr
  have listedCode : listed .check (donePC true) (restoreOps.map Sym.Calc.instr):=by decide
  obtain ⟨rest,regs,mem,addr⟩:=calcRegs .check u restoreOps (donePC true) ip (by decide) (matchesListed listedCode) (by decide) rfl
  let v:=Sym.evaluated restoreOps u
  have back:=jump .check 22491 2668 v addr (by decide)
  let t:=v.setPC (pcAt 2668)
  have fm : t.mem=u.mem:=mem
  have after:=frame.memory.still fm
  refine ⟨t,((go.trans body).trans rest).trans back,rfl,(regs .x8).trans rfl,after,?_⟩
  intro r hr
  have ne : r≠.x8:=by intro e;subst r;exact hr.1 (by decide)
  exact (outsideCalc restoreOps u v regs [.x8] rfl r (by simpa using ne)).trans (frame.keep r hr)

end CommitGolfCandidate.S4.Codec
