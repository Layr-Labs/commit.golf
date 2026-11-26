import CommitGolfCandidate.StreamCopyControl

namespace TwoPermutationPrototype.PackedOpening.StreamCopy
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Pack
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

structure Pos (base : Nat) (f : Nat→Byte) (orig : MachineState) (d a : Nat) (s : MachineState) : Prop where
  frame : Frame orig s
  bytes : Bytes base f orig d s
  dst : s.getReg .x24=word (base+d)
  src : s.getReg .x30=word (base+a)

private theorem pairFrame {s t : MachineState} (keep : ∀ r,r≠.x23 → t.getReg r=s.getReg r) :
    Frame s t := by
  intro r hr; apply keep; intro e;subst r;simp at hr

private theorem movedBytes {base n : Nat} {f : Nat→Byte} {orig s : MachineState}
    (h : Bool) (c : Control) (m : Bytes base f orig n s) :
    Bytes base f orig n (after h c s) := by intro a;rw [ctrlBytes,m]

theorem records (h : Bool) (k L base : Nat) (Q : Proof) (f : Nat→Byte)
    (orig s : MachineState) (fits : (width h+1)*k≤L) (room : base+L<2^36)
    (source : ∀ j<L,orig.getByte (word (base+j))=Q.getD j 0)
    (values : ∀ r<k,∀ j<width h,Q.getD ((width h+1)*r+copyOff (width h) j) 0=f (width h*r+j))
    (s0 : Pos base f orig 0 0 s) (count:s.getReg .x25=word k)
    (pc:s.pc=pcOf (if k=0 then latch h+4 else start h .record)) :
    ∃ z, Pos base f orig (width h*k) ((width h+1)*k) z ∧ z.pc=pcOf (latch h+4) ∧
      Runs s z ((2*width h+4)*k) ((2*width h+4)*k) := by
  let w:=width h
  let I:=fun r (t : MachineState)=>Pos base f orig (w*r) ((w+1)*r) t ∧ t.getReg .x25=word (k-r) ∧
    t.pc=pcOf (if r=k then latch h+4 else start h .record)
  have init : I 0 s:=⟨by simpa using s0,by simpa using count,by simpa [eq_comm] using pc⟩
  have one (r : Nat) (hr : r<k) (t : MachineState) (inv : I r t) :
      ∃ z, I (r+1) z ∧ Runs t z (2*w+4) (2*w+4) := by
    obtain ⟨p,rem,atPc⟩:=inv
    have bound : (w+1)*r+(w+1)≤L := by
      simpa [Nat.mul_add] using (Nat.mul_le_mul_left (w+1) (show r+1≤k by omega)).trans fits
    have ar : (w+1)*r=w*r+r := Nat.succ_mul _ _
    have layout (j : Nat) (hj : j<size h .record) :
        w*r+j≤(w+1)*r+offset h .record j ∧ (w+1)*r+offset h .record j<L ∧
        Q.getD ((w+1)*r+offset h .record j) 0=f (w*r+j) := by
      change j<w at hj
      refine ⟨?_,?_,values r hr j hj⟩ <;>
        simp only [offset,copyOff] <;> split_ifs <;> omega
    obtain ⟨u,body,atLatch,kept,mu⟩:=copySpan h .record base (w*r) ((w+1)*r) L Q f orig t room
      (by simpa [Nat.ne_of_lt hr] using atPc) p.dst p.src p.bytes source layout
    have here : u.pc=pcOf (latch h) := by simpa [start,size,latch] using atLatch
    have rc : k-r=(k-(r+1))+1 := by omega
    have sm : k-(r+1)<2^64 := by rw [Nat.succ_mul] at fits;omega
    obtain ⟨a,d,n,newpc⟩:=recordRegs h u (base+(w+1)*r) (base+w*r) (k-(r+1))
      ((kept _ (by decide)).trans p.src) ((kept _ (by decide)).trans p.dst)
      (by rw [kept _ (by decide),rem,rc]) sm here
    have rcost:=ctrlRun h .record here (by intro impossible;cases impossible)
    have total:=body.trans rcost
    have ra : base+(w+1)*r+(w+1)=base+(w+1)*(r+1) := by ring
    have rd : w*r+w=w*(r+1) := by ring
    refine ⟨_,⟨⟨p.frame.thenDo ((pairFrame kept).thenDo (ctrlFrame h .record u)),?_,?_,?_⟩,n,?_⟩,total⟩
    · rw [←rd];exact movedBytes h .record mu
    · rw [←rd];simpa only [Nat.add_assoc] using d
    · rw [←ra];exact a
    · simpa [show k-(r+1)=0 ↔ r+1=k by omega] using newpc
  obtain ⟨z,⟨endPos,_,endPc⟩,all⟩:=fixedLoop I k (2*w+4) one init
  exact ⟨z,endPos,by simpa using endPc,all⟩

private def tailSpan (wide : Bool) : Span := if wide then .eight else .last
private def stepSize (wide : Bool) := if wide then 8 else 1
private def endReg (wide : Bool) : Reg := if wide then .x28 else .x26
private def nextCtl (wide : Bool) : Control := if wide then .wide else .byte
private def exitWord (h wide : Bool) := latch h+(if wide then 27 else 33)

/-- Eight-byte blocks and the one-byte remainder have the same two-pointer postcondition. -/
private theorem tailPost (h wide : Bool) (s : MachineState) (src dst endp : Nat)
    (a:s.getReg .x30=word src) (b:s.getReg .x24=word dst) (e:s.getReg (endReg wide)=word endp)
    (le:dst+stepSize wide≤endp) (room:endp<2^64) (pc:s.pc=pcOf (beginAt h (nextCtl wide))) :
    let t:=after h (nextCtl wide) s
    t.getReg .x30=word (src+stepSize wide) ∧ t.getReg .x24=word (dst+stepSize wide) ∧
      t.getReg (endReg wide)=word endp ∧
      t.pc=pcOf (if dst+stepSize wide=endp then exitWord h wide else start h (tailSpan wide)) := by
  cases wide with
  | true => exact wideRegs h s src dst endp a b e le room pc
  | false =>
    obtain ⟨ra,rb,p⟩:=byteRegs h s src dst endp a b e le room pc
    exact ⟨ra,rb,(ctrlFrame h .byte s .x26 (by decide)).trans e,p⟩

private theorem tailLoop (h wide : Bool) (n d a base L : Nat) (orig s : MachineState)
    (Q : Proof) (f : Nat→Byte) (room:base+L<2^36)
    (fits:d+stepSize wide*n≤L)
    (source:∀ j<L,orig.getByte (word (base+j))=Q.getD j 0)
    (values:∀ j<stepSize wide*n,d+j≤a+j ∧ a+j<L ∧ Q.getD (a+j) 0=f (d+j))
    (inv0:Pos base f orig d a s) (endp:s.getReg (endReg wide)=word (base+(d+stepSize wide*n)))
    (pc:s.pc=pcOf (if n=0 then exitWord h wide else start h (tailSpan wide))) :
    ∃ z, Pos base f orig (d+stepSize wide*n) (a+stepSize wide*n) z ∧ z.pc=pcOf (exitWord h wide) ∧
      Runs s z ((2*stepSize wide+3)*n) ((2*stepSize wide+3)*n) := by
  let u:=stepSize wide
  let I:=fun j (t:MachineState) => Pos base f orig (d+u*j) (a+u*j) t ∧
    t.getReg (endReg wide)=word (base+(d+u*n)) ∧ t.pc=pcOf (if j=n then exitWord h wide else start h (tailSpan wide))
  have init : I 0 s:=⟨by simpa using inv0,endp,by simpa [eq_comm] using pc⟩
  change d+u*n≤L at fits
  change ∀ j<u*n, _ at values
  have sz : size h (tailSpan wide)=u := by cases wide <;>rfl
  have pos : 0<u := by cases wide <;>decide
  have one (j : Nat) (hj:j<n) (t:MachineState) (inv:I j t) :
      ∃ z,I (j+1) z ∧ Runs t z (2*u+3) (2*u+3) := by
    obtain ⟨p,e,pt⟩:=inv
    have jm : u*j+u≤u*n := by simpa [Nat.mul_add] using Nat.mul_le_mul_left u (show j+1≤n by omega)
    have facts (i : Nat) (hi:i<size h (tailSpan wide)) :
        d+u*j+i≤a+u*j+offset h (tailSpan wide) i ∧ a+u*j+offset h (tailSpan wide) i<L ∧
        Q.getD (a+u*j+offset h (tailSpan wide) i) 0=f (d+u*j+i) := by
      obtain ⟨lo,up,z⟩:=values (u*j+i) (by rw [sz] at hi;omega)
      have idx : offset h (tailSpan wide) i=i := by cases wide <;>rfl
      simpa only [idx,Nat.add_assoc] using And.intro lo (And.intro up z)
    obtain ⟨v,body,atLatch,keep,mem⟩:=copySpan h (tailSpan wide) base (d+u*j) (a+u*j) L Q f orig t room
      (by simpa [Nat.ne_of_lt hj] using pt) p.dst p.src p.bytes source facts
    have here : v.pc=pcOf (beginAt h (nextCtl wide)) := by
      rw [←show start h (tailSpan wide)+2*size h (tailSpan wide)=beginAt h (nextCtl wide) by cases wide <;> simp [start,size,tailSpan,beginAt,nextCtl] <;> omega];exact atLatch
    have er : endReg wide≠.x23 := by cases wide <;> decide
    obtain ⟨src2,dst2,e2,pc2⟩:=tailPost h wide v (base+(a+u*j)) (base+(d+u*j)) (base+(d+u*n))
      ((keep _ (by decide)).trans p.src) ((keep _ (by decide)).trans p.dst) ((keep _ er).trans e)
      (by change base+(d+u*j)+u≤base+(d+u*n);omega) (by omega) here
    have control:=ctrlRun h (nextCtl wide) here (by cases wide <;> intro impossible <;> cases impossible)
    have bill3 : bill (nextCtl wide)=3 := by cases wide <;>rfl
    have endEq : base+(d+u*j)+u=base+(d+u*n) ↔ j+1=n := by
      constructor
      · intro eq
        have same : u*(j+1)=u*n := by rw [Nat.mul_succ];omega
        exact Nat.eq_of_mul_eq_mul_left pos same
      · rintro rfl;rw [Nat.mul_succ];omega
    refine ⟨_,⟨⟨p.frame.thenDo ((pairFrame keep).thenDo (ctrlFrame h _ v)),?_,?_,?_⟩,e2,?_⟩,?_⟩
    · simpa only [sz,Nat.mul_succ,Nat.add_assoc,u] using movedBytes h (nextCtl wide) mem
    · simpa only [Nat.mul_succ,Nat.add_assoc,u] using dst2
    · simpa only [Nat.mul_succ,Nat.add_assoc,u] using src2
    · change (after h (nextCtl wide) v).pc=pcOf (if base+(d+u*j)+u=base+(d+u*n) then _ else _) at pc2
      simpa only [endEq] using pc2
    · simpa only [sz,bill3] using body.trans control
  obtain ⟨z,⟨endPos,_,endPc⟩,all⟩:=fixedLoop I n (2*u+3) one init
  exact ⟨z,endPos,by simpa using endPc,all⟩

/-- Run both record and suffix loops, re-entering the original guard with the output cursor at its end. -/
theorem compact (h : Bool) (k L base : Nat) (Q : Proof) (f : Nat→Byte) (s : MachineState)
    (fits:(width h+1)*k≤L) (room:base+L<2^36) (pc:s.pc=pcOf (guardWord h))
    (x16:s.getReg .x16=word k) (x18:s.getReg .x18=word (L-k)) (x20:s.getReg .x20=word base)
    (x22:s.getReg .x22=0) (x26:s.getReg .x26=word (base+(L-k)))
    (source:∀ j<L,s.getByte (word (base+j))=Q.getD j 0)
    (recordBytes:∀ r<k,∀ j<width h,Q.getD ((width h+1)*r+copyOff (width h) j) 0=f (width h*r+j))
    (tailBytes:∀ j<L-(width h+1)*k,Q.getD ((width h+1)*k+j) 0=f (width h*k+j)) :
    ∃ z, Runs s z (price (width h) k L) (price (width h) k L) ∧ z.pc=pcOf (guardWord h) ∧
      Frame s z ∧ z.getReg .x22=word (L-k) ∧ Bytes base f s (L-k) z := by
  let w:=width h
  let E:=L-(w+1)*k
  have mul : (width h+1)*k=width h*k+k := Nat.succ_mul _ _
  by_cases emp : L=k
  · subst L
    exact ⟨s,by simpa [price] using Runs.refl s,pc,Frame.refl s,by simpa using x22,by simp [Bytes]⟩
  have gate : s.getReg .x22≠s.getReg .x18 := by
    rw [x22,x18]; intro eq
    have z := (w_inj 0 (L-k) (by decide) (by omega)).mp eq
    omega
  have ent:=ctrlRun h .enter pc (fun _=>gate)
  obtain ⟨as0,ds0,ct0,pc0⟩:=entryRegs h s base k x20 x16 gate (by omega) pc
  have p0 : Pos base f s 0 0 (after h .enter s) :=
    ⟨ctrlFrame h .enter s,by intro q;rw [ctrlBytes];simp,by simpa using ds0,by simpa using as0⟩
  obtain ⟨v,pv,pcv,recs⟩:=records h k L base Q f s _ fits room source recordBytes p0 ct0 pc0
  have endValue : base+(L-k)=base+w*k+E := by dsimp [E,w];omega
  have prep:=ctrlRun h .prepare pcv (by intro impossible;cases impossible)
  obtain ⟨sa,da,e,pp⟩:=prepareRegs h v (base+w*k) E (by omega) pv.dst
    (by rw [pv.frame _ (by decide),x26,endValue]) pcv
  let z:=after h .prepare v
  have pz : Pos base f s (w*k) ((w+1)*k) z :=
    ⟨pv.frame.thenDo (ctrlFrame h .prepare v),movedBytes h .prepare pv.bytes,da,sa.trans pv.src⟩
  have ea : w*k+8*(E/8)≤L := by omega
  have fa (i : Nat) (hi:i<8*(E/8)) : w*k+i≤(w+1)*k+i ∧ (w+1)*k+i<L ∧ Q.getD ((w+1)*k+i) 0=f (w*k+i) := by
    have lt : i<E := by omega
    exact ⟨by dsimp [w];omega,by dsimp [E] at lt;omega,tailBytes i lt⟩
  obtain ⟨u,pu,pcu,wide⟩:=tailLoop h true (E/8) (w*k) ((w+1)*k) base L s z Q f room ea source fa pz
    (by simpa [endReg,stepSize,Nat.add_assoc] using e) pp
  have test:=ctrlRun h .test pcu (by intro impossible;cases impossible)
  obtain ⟨ua,ud,up⟩:=testRegs h u (base+(w*k+8*(E/8))) (base+(L-k)) pu.dst
    ((pu.frame _ (by decide)).trans x26) (by omega) (by omega) pcu
  have pr : Pos base f s (w*k+8*(E/8)) ((w+1)*k+8*(E/8)) (after h .test u) :=
    ⟨pu.frame.thenDo (ctrlFrame h .test u),movedBytes h .test pu.bytes,ud,ua.trans pu.src⟩
  have endEq : base+(w*k+8*(E/8))=base+(L-k) ↔ E%8=0 := by omega
  have fb (j : Nat) (hj : j<1*(E%8)) :
      w*k+8*(E/8)+j≤(w+1)*k+8*(E/8)+j ∧ (w+1)*k+8*(E/8)+j<L ∧
      Q.getD ((w+1)*k+8*(E/8)+j) 0=f (w*k+8*(E/8)+j) := by
    have lt : 8*(E/8)+j<E := by omega
    exact ⟨by dsimp [w];omega,by dsimp [E] at lt;omega,by simpa only [Nat.add_assoc] using tailBytes _ lt⟩
  obtain ⟨y,py,pcy,bytes⟩:=tailLoop h false (E%8) _ _ base L s _ Q f room (by change w*k+8*(E/8)+1*(E%8)≤L;omega)
    source fb pr (by change (after h .test u).getReg .x26=word (base+(w*k+8*(E/8)+1*(E%8)));rw [pr.frame _ (by decide),x26];congr 1;omega)
    (by change (after h .test u).pc=pcOf (if E%8=0 then latch h+33 else start h .last);simpa only [endEq] using up)
  have finish:=ctrlRun h .finish pcy (by intro impossible;cases impossible)
  obtain ⟨done,pDone⟩:=finishRegs h y pcy
  have total:=(((((ent.trans recs).trans prep).trans wide).trans test).trans bytes).trans finish
  have cost : price (width h) k L=13+(2*w+4)*k+19*(E/8)+5*(E%8) := by simp [price,emp,w,E]
  refine ⟨_,total.cast ?_ ?_,pDone,py.frame.thenDo (ctrlFrame h .finish y),
    done.trans ((py.frame _ (by decide)).trans x18),?_⟩
  · rw [cost];change 6+(2*w+4)*k+4+19*(E/8)+1+5*(E%8)+2=_;omega
  · rw [cost];change 6+(2*w+4)*k+4+19*(E/8)+1+5*(E%8)+2=_;omega
  · have z:=movedBytes h .finish py.bytes
    convert z using 1
    change L-k=w*k+8*(E/8)+1*(E%8);omega

end TwoPermutationPrototype.PackedOpening.StreamCopy
