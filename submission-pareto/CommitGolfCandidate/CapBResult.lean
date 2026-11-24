import CommitGolfCandidate.CapBStart
import CommitGolfCandidate.CapBFlush
import CommitGolfCandidate.CapBCopy
import CommitGolfCandidate.CapBFormat
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp Layout2Helpers
open TwoPermutationPrototype.GroupedOpening (openingImage bytesAt capOffset)
open TwoPermutationPrototype.GroupedOpening.CapB (handlers flushPrice flushBytes)
open TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

def copyCost (k n : Nat) := if k%4=0 then 0 else 3+5*n

theorem afterCopy (s : MachineState) (k : Nat) (xs : List Byte) (ref : MachineState)
    (here : s.pc=pc 6662) (dest : s.getReg .x21=addr (work k+xs.length))
    (copy : s.getReg .x14=addr (copyDest k)) (bytes : WritesList ref s (work k) xs)
    (fit : k≤16777216) (len : xs.length≤8192) :
    ∃ t, Run openingImage s t (1+copyCost k xs.length) (1+copyCost k xs.length) ∧
    t.pc=pc 6671 ∧ t.getReg .x21=addr (capStart k+xs.length) ∧ t.getReg .x20=s.getReg .x20 ∧
    (∀ i,i<xs.length → gbyte t (capStart k+i)=xs[i]?.getD 0) ∧
    (∀ q,proofBase≤q → q<capStart k → gbyte t q=gbyte ref q) ∧
    t.getReg .x14=(if k%4=0 then 0#64 else addr (capStart k+xs.length)) := by
  have space : capStart k+8192≤MEMORY_BYTES := by unfold capStart proofBase MEMORY_BYTES;omega
  have geo : scratch+8192≤proofBase := by decide
  obtain ⟨a,ra,pa,ma,rA⟩:=nav_copyTest s here
  have ba:=bytes.move (s':=ref) rfl ma
  by_cases align : k%4=0
  · have b : WritesList ref a (capStart k) xs := by simpa only [WritesList,work,if_pos align] using ba
    refine ⟨a,by simpa [copyCost,align] using ra,by simpa [copy,copyDest,align,addr] using pa,by simpa [rA,work,align] using (rA .x21).trans dest,rA _,?_,?_,?_⟩
    · intro j h;exact b.atIndex _ h (by omega)
    · intro q h h';exact b.outside _ (by omega) (Or.inl h')
    · rw [if_pos align,rA,copy];simp [copyDest,align,addr]
  · have nonzero : addr (capStart k)≠0#64 := by
      change addr (capStart k)≠addr 0;rw [ne_eq,addr_inj (by unfold MEMORY_BYTES at space;omega) (by decide)];unfold capStart proofBase;omega
    have b : WritesList ref a scratch xs := by simpa only [WritesList,work,if_neg align] using ba
    obtain ⟨t,rt,pt,dt,ot,bt,xt⟩:=scratchCopy a (capStart k) xs.length (by change scratch+xs.length≤_ ∧ _;constructor <;> first | omega | (unfold capStart;omega))
      (by simpa [copy,copyDest,align,nonzero] using pa)
      (by simp [rA,copy,copyDest,align]) (by simpa [rA,work,align,scratch] using (rA .x21).trans dest)
    refine ⟨t,by simpa [copyCost,align] using ra.thenDo rt,pt,dt,ot.trans (rA _),?_,?_,?_⟩
    · intro i small;exact (bt.atIndex i small (by omega)).trans (b.atIndex i small (by unfold scratch MEMORY_BYTES;omega))
    · intro q above below;exact (bt.outside _ (by omega) (Or.inl below)).trans (b.outside _ (by omega) (Or.inr (by omega)))
    · rw [if_neg align];exact xt

def bill (gs : List Nat) (k : Nat) :=
  TwoPermutationPrototype.GroupedOpening.CapB.price gs k
theorem bill_fit (gs : List Nat) (k : Nat) : bill gs k≤65536 := by
  let f:=(capFrontierNodes gs 1 8).length
  have bound : f≤128 := limit_frontier gs
  have all := TwoPermutationPrototype.GroupedOpening.CapB.batch_frontier ⟨f,by omega⟩
  have c:=TwoPermutationPrototype.GroupedOpening.CapB.control_bound gs 1 5
  change TwoPermutationPrototype.GroupedOpening.CapB.control gs 1 5≤850+2*f at c
  change 297+(850+2*f)+handlers f+1+7+flushPrice f≤3375 at all
  have sz : Layout2.Cap.size f≤3840 := by unfold Layout2.Cap.size;omega
  unfold bill TwoPermutationPrototype.GroupedOpening.CapB.price;change 297+_+handlers f+1+7+flushPrice f+_≤_
  split <;> dsimp only [f] at * <;> omega

/-- The return (6671 → 709..712, V2b's HALT block): 5 cycles, the proof length `534 k + n`. -/
theorem return_ok (s : MachineState) (B n k : Nat) (here : s.pc=pc 6671) (dest : s.getReg .x21=addr (B+n))
    (out : s.getReg .x20=addr proofBase) (base : B=capStart k) (room : B+n≤MEMORY_BYTES) :
    ∃ t,(∀ surplus,execute openingImage (5+surplus) s true=pure ⟨.success,t,5,0⟩) ∧
      (t.getReg .x11).toNat=534*k+n ∧ t.mem=s.mem := by
  obtain ⟨a,ra,pa,ma,_rA⟩:=nav_haltJump s here
  obtain ⟨t,rt,pt,mt,rT⟩:=nav_exit a pa
  have fetch:=wide_image_fetch openingImage t 712 Instr.ECALL (by decide) pt (by rfl)
  have halt : ∀ surplus,execute openingImage (1+surplus) t true=pure ⟨.success,t,1,0⟩ := by
    intro fuel;rw [Nat.add_comm 1,execute,fetch];simp [rT]
  refine ⟨t,?_,?_,mt.trans ma⟩
  · intro fuel;have joint:=ra.thenDo rt
    rw [show 5+fuel=(1+3)+(1+fuel) by omega]
    rw [joint,halt];rfl
  · simp only [rT,_rA,reduceCtorEq,ite_false,ite_true,dest,out]
    rw [base];change (addr ((proofBase+534*k)+n)-addr proofBase).toNat=_
    rw [show proofBase+534*k+n=(534*k+n)+proofBase by omega,←add_addr,BitVec.add_sub_cancel,BitVec.toNat_ofNat]
    unfold capStart MEMORY_BYTES at *;omega

/-- Cap execution on every admitted nonempty record pass, including arbitrary trapdoor padding. -/
theorem cap_stage {gs H k s} (e : CapEntry gs H k s) :
    let ns:=capFrontierNodes gs 1 8
    let ds:=ns.map H
    ∃ t steps cycles, steps≤65536 ∧ (k=128 → cycles≤3375) ∧
      (∀ surplus,execute openingImage (steps+surplus) s true=pure ⟨.success,t,cycles,0⟩) ∧
      (t.getReg .x11).toNat=534*k+capOffset ns.length ∧
      (∀ q,proofBase≤q → q<capStart k → gbyte t q=gbyte s q) ∧
      bytesAt t (capStart k) (capOffset ns.length)=capRaw ds := by
  let ns:=capFrontierNodes gs 1 8;let f:=ns.length;let ds:=ns.map H
  have hf : f≤128 := limit_frontier gs
  have geometry:=work_geo k e.count
  obtain ⟨ref,w,z,runW,iw,pw,frame⟩:=walk_root e
  let st:=stream z ds
  let B:=work k+8*st.out.length
  have count : ds.length=f := by simp [ds,f]
  have sz := stream_size z ds
  change 8*st.out.length=Layout2.Cap.body ds.length at sz;rw [count] at sz
  have room : B+8≤MEMORY_BYTES := by dsimp [B];unfold Layout2.Cap.body at sz;omega
  obtain ⟨u,ru,pu,du,ou,cu,tail⟩:=flush f B w st.carry pw iw.phase iw.first iw.dest iw.acc (by dsimp [B];omega) room
  have bodyWrite:=iw.data.bytes geometry.1 (by change work k+8*st.out.length≤_;dsimp [B] at room;omega)
  have blen:=flatWordLength st.out
  have tail' : WritesList w u (work k+(st.out.flatMap wordBytes).length) ((wordBytes st.carry).take (flushBytes (ds.length%32))) := by simpa only [blen,count] using tail
  have bytes : WritesList ref u (work k) (capRaw ds) := by rw [←capRaw_seed z];exact joinWrites bodyWrite tail'
  have xslen : (capRaw ds).length=Layout2.Cap.size f := by rw [capRaw_length,count]
  have lens : 8*st.out.length+flushBytes (f%32)=(capRaw ds).length := by
    rw [←capRaw_seed z];unfold capBytes;simp only [List.length_append,flatWordLength,List.length_take,wordBytes,List.length_ofFn,count]
    rw [Nat.min_eq_left (flush_range ⟨f%32,by omega⟩).1]
  have rawSmall : (capRaw ds).length≤8192 := by rw [xslen];unfold Layout2.Cap.size;omega
  obtain ⟨a,ra,pa,da,oa,out,kept,_⟩:=afterCopy u k (capRaw ds) ref pu
    (by rw [du,←lens];change addr ((work k+8*st.out.length)+_)=_;rw [Nat.add_assoc]) (cu.trans iw.copy) bytes e.count rawSmall
  have endRoom : capStart k+(capRaw ds).length≤MEMORY_BYTES := by have:=e.count;unfold capStart proofBase MEMORY_BYTES;omega
  obtain ⟨t,halt,len,mem⟩:=return_ok a (capStart k) (capRaw ds).length k pa da ((oa.trans ou).trans iw.output) rfl endRoom
  have cn : capOffset f=(capRaw ds).length := by rw [xslen];unfold capOffset Layout2.Cap.size;omega
  let cost:=walkCost gs 1 5 0
  let pre:=((297+extraInit k+cost)+(2+flushPrice f))+(1+copyCost k (capRaw ds).length)
  let step:=((201+extraInit k+cost)+(2+flushPrice f))+(1+copyCost k (capRaw ds).length)
  have billEq : pre+5=bill gs k := by
    unfold pre bill TwoPermutationPrototype.GroupedOpening.CapB.price extraInit copyCost cost walkCost
    change ((297+(if k%4=0 then 0 else 2)+(TwoPermutationPrototype.GroupedOpening.CapB.control gs 1 5+(handlers (0+f)-handlers 0)))+(2+flushPrice f))+(1+(if k%4=0 then 0 else 3+5*(capRaw ds).length))+5=297+_+handlers f+1+7+flushPrice f+_
    rw [xslen];simp only [handlers,Nat.zero_add,Nat.sub_zero];dsimp only [f,ns];split_ifs <;> omega
  have joint : Run openingImage s a step pre := (runW.thenDo ru).thenDo ra
  refine ⟨t,step+5,pre+5,?_,?_,?_,?_,?_,?_⟩
  · have:=bill_fit gs k;dsimp only [step,pre] at *;omega
  · rintro rfl;have sc:=TwoPermutationPrototype.GroupedOpening.CapB.scored gs hf;unfold bill at billEq;omega
  · intro surplus;rw [Nat.add_assoc,joint,halt];rfl
  · rw [cn];exact len
  · intro q above below
    have qfit : q<2^64 := by unfold MEMORY_BYTES at endRoom;omega
    have key:=frame (alignToDword (addr q)) (by rw [align_nat _ qfit];unfold markBase proofBase at *;omega)
    exact (show gbyte t q=gbyte a q by simp only [gbyte,MachineState.getByte,MachineState.getMem,mem]).trans
      ((kept _ above below).trans (congrArg (fun x=>extractByte x (byteOffset (addr q))) key))
  · rw [cn];apply List.ext_getElem (by simp [bytesAt,ds,ns]);intro i hi hj
    simp only [bytesAt,List.getElem_map,List.getElem_range]
    have get:=out i hj;rw [List.getElem?_eq_getElem hj,Option.getD_some] at get
    simpa only [gbyte,MachineState.getByte,MachineState.getMem,mem] using get
end CommitGolfCandidate.CapB
