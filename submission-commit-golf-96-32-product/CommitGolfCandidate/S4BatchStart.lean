import CommitGolfCandidate.S4Dispatch
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

private def sizeOps : List Sym.Calc := [.addi .x6 .x0 34,.slli .x6 .x6 11,.addi .x6 .x6 778]
private def readyOps := sizeOps++[.add .x24 .x18 .x6,.addi .x25 .x0 0,.addi .x26 .x0 0]
private def batchOps (ready : Bool) := if ready then readyOps else sizeOps
private def startPC (ready : Bool) := if ready then 2662 else 2657
private def stopPC (ready : Bool) := if ready then 2668 else 2660
private theorem guards (r : Bool) : (Fragment.arithmetic (batchOps r)).valid .check (startPC r) (stopPC r) ∧
    (batchOps r).all (fun x=>x.dst != .x0)=true ∧ Sym.requirements Sym.original (batchOps r)=[] := by cases r <;> decide

private def boot (r : Bool) (s : MachineState) := Sym.evaluated (batchOps r) s
private theorem batchOpsRun (r : Bool) (s : MachineState) (o : Oracle) (pc : s.pc=pcAt (startPC r)) :
    CheckRuns o s (boot r s) (if r then 6 else 3) 0 ∧
    (boot r s).pc=pcAt (stopPC r) ∧ (boot r s).mem=s.mem ∧ (boot r s).getReg .x6=70410 ∧
    ∀ x, x∉[Reg.x6,.x24,.x25,.x26] → (boot r s).getReg x=s.getReg x := by
  obtain ⟨ok,nz,reads⟩:=guards r
  have h:=evalMath .check _ _ _ s pc ok (fun c mem=>bne_iff_ne.mp (List.all_eq_true.mp nz c mem))
    (fun _ mem=>by rw [reads] at mem;cases mem)
  have size : (batchOps r).length=(if r then 6 else 3):=by cases r <;> rfl
  refine ⟨size ▸ ofRuns o h.1,h.2.2.2,h.2.2.1,?_,?_⟩
  · exact (h.2.1 .x6).trans (by cases r <;> rfl)
  · intro x notMem
    apply (h.2.1 x).trans
    have static (r : Bool) (x : Reg) (allowed : x∉[Reg.x6,.x24,.x25,.x26]) :
        ((batchOps r).foldl Sym.bump Sym.original) x=Sym.original x:=by
      cases r <;> cases x <;> first | exfalso;apply allowed;decide | rfl
    rw [static r x notMem];cases x <;> rfl

theorem zeroScratch (i : CheckInput) (q : Nat) (small : q<32768) : byte (initial i) q=0 := by
  apply (initial_input_byte Late.submission .check i q (by omega)).trans
  unfold inputByte
  let root:=fixedBuffer rootBase i.commitment
  let ix:=positionsBuffer indexBase i.positions
  let val:=valuesBuffer valueBase i.positions i.values
  let pf : InputBuffer:=⟨proofBase,i.proof.length,fun j=>i.proof[j]?.getD 0⟩
  have empty (b : InputBuffer) (above : 32768≤b.address) : decide (b.address≤q ∧ q<b.address+b.length)=false := decide_eq_false (by omega)
  have h : [root,ix,val,pf].find? (fun b=>decide (b.address≤q ∧ q<b.address+b.length))=none:=by
    simp only [List.find?_cons,empty root (show 32768≤4294971392 by decide),empty ix (show 32768≤7650414624 by decide),empty val (show 32768≤7784632352 by decide),empty pf (show 32768≤12079599648 by decide),
      List.find?_nil]
  change (match [root,ix,val,pf].find? _ with | some b=>_ | none=>_)=_
  rw [h]
  have high : ¬dataBase (Late.submission.image .check)≤q:=by change ¬68719476736≤q;omega
  exact if_neg high

theorem batchStart (o : Oracle) (i : CheckInput) (hb : i.positions.card=BATCH)
    (fit : i.proof.length≤Late.submission.sizes.proof) :
    (i.proof.length≠70410 ∧ ∃ n≤30,Finishes o (initial i) n 0 .failure) ∨
    (i.proof.length=70410 ∧ ∃ s,Env i s ∧ Cursor i s 0 ∧ Seen o.compression (readView i) 0 s ∧
       s.pc=pcAt 2668 ∧ CheckRuns o (initial i) s 25 0) := by
  obtain ⟨base,hdr,imem⟩:=dispatch i o
  rw [if_pos hb] at base
  let s:=modeState i
  have pc : s.pc=pcAt (startPC false):=by simp only [s,modeState,if_pos hb];rfl
  obtain ⟨pre,at2660,mem,sz,keep⟩:=batchOpsRun false s o pc
  let t:=boot false s
  have bytes : t.getReg .x17=W i.proof.length:=(keep _ (by decide)).trans hdr.proofLen
  have test:=alternate .check 2660 2662 4855 .x6 .x17 true (by decide) (by decide) rfl t at2660
  change i.proof.length≤17179869184 at fit
  have cond : ((t.getReg .x6==t.getReg .x17)==true)=decide (70410=i.proof.length):=by
    rw [sz,bytes];change ((W 70410==W i.proof.length)==true)=_;rw [eqNatural _ _ (by decide) (by omega)];simp
  rw [cond] at test
  by_cases len : i.proof.length=70410
  · rw [decide_eq_true len.symm] at test
    let u:=t.setPC (pcAt 2662)
    obtain ⟨ready,endPC,lastMem,_,saved⟩:=batchOpsRun true u o rfl
    let z:=boot true u
    have allMem : z.mem=(initial i).mem:=lastMem.trans (mem.trans imem)
    have kr (r : Reg) (nr : r∉[Reg.x6,.x24,.x25,.x26]) : z.getReg r=s.getReg r:=
      (saved r nr).trans (MachineState.getReg_setPC.trans (keep r nr))
    refine Or.inr ⟨len,z,⟨?_,?_,?_,?_,?_,(show InputsStill i (initial i) from fun _ _ _=>rfl).regs allMem⟩,
      ⟨?_,?_,?_,?_⟩,?_,endPC,((base.trans pre).trans (ofRuns o test)).trans ready⟩
    all_goals first | (rw [kr _ (by decide)];first | exact hdr.mode | exact hdr.kind | exact hdr.width | exact hdr.three | exact hdr.root | exact hdr.index | exact hdr.value | exact hdr.proof | exact hdr.count) | refine ⟨?_,?_,?_⟩
    · intro x bx
      have zero:=zeroScratch i (768+x) (by omega)
      simpa only [byte,MachineState.getByte,MachineState.getMem,allMem,served,firstBefore,List.range_zero,List.find?_nil,
        Option.map_none,Option.isSome_none,Bool.false_eq_true,ite_false] using zero
    · intro x _ d e;cases e
    · intro x hx;omega
  · rw [decide_eq_false (Ne.symm len)] at test
    exact Or.inl ⟨len,23,by decide,((base.trans pre).trans (ofRuns o test)).finish (verdict false _ o rfl)⟩
end CommitGolfCandidate.S4.Machine
