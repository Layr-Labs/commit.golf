import CommitGolfCandidate.PairHashEval
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 200000
attribute [local irreducible] Late.Check.Normal.checkEvaluation execute readBuffer parentAt

structure Prepared (o : Oracle) (input : CheckInput) (p : Fin 128) (s t : MachineState) : Prop where
  pc : t.pc=5408
  regs : Carries s t
  quiet : Quiet s t (sourceRow p.val) 64
  value : o.compression (readBuffer t (sourceRow p.val) 96) = parentAt o.compression input p.val

theorem parentValue (o : Oracle) (s : MachineState) (p : Fin 128) (l r : Digest)
    (low : digestAt s (sourceRow p.val)=l) (high : digestAt s (sourceRow p.val+32)=r)
    (gap : digestAt s (sourceRow p.val+64)=0) :
    o.compression (readBuffer s (sourceRow p.val) 96)=combine o.compression l r := by
  rw [rowInput s _ (by unfold sourceRow;omega) gap]
  exact congrArg o.compression (congrArg padInput (congrArg₂ BitVec.append high low))

theorem hashEffect {o : Oracle} {input : CheckInput} {p : Fin 128} {s t m : MachineState} {d : Digest}
    (prep : Prepared o input p s t) (keep : Carries t m) (w : Written t m (outSlot p.val) d)
    (eqn : d=parentAt o.compression input p.val) : PairEffect o.compression input p.val s (m.setPC 5468) :=
  ⟨rfl,carriesTrans (carriesTrans prep.regs keep) (carriesPC m 5468),
   (memDigest (s:=m) (t:=m.setPC 5468) rfl (outSlot p.val)).trans (w.atDst.trans eqn),
   fun x bx ch out=>(byteMem (s:=m) (t:=m.setPC 5468) rfl x).trans ((w.outside x bx out).trans (prep.quiet x bx ch))⟩

theorem executeParent (o : Oracle) (input : CheckInput) (p : Fin 128) (s t : MachineState)
    (a : Args p s) (prep : Prepared o input p s t) :
    ∃ z,Runs o t z 7 1 ∧ PairEffect o.compression input p.val s z := by
  have atT := a.transfer prep.regs
  have bp := p.isLt
  have addr : (t.getReg .x23).toNat=sourceRow p.val := by rw [atT.source,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold sourceRow;omega)]
  have dst : (t.getReg .x24).toNat=outSlot p.val := by rw [atT.dest,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold outSlot;omega)]
  have sb : rangeValid (t.getReg .x23) 96 := by simp [rangeValid,addr,sourceRow,MEMORY_BYTES];omega
  have db : rangeValid (t.getReg .x24) 32 := by simp [rangeValid,dst,outSlot,MEMORY_BYTES];omega
  have sa : (t.getReg .x23).toNat%8=0 := by rw [addr];unfold sourceRow;omega
  have da : (t.getReg .x24).toNat%8=0 := by rw [dst];unfold outSlot;omega
  let d:=o.compression (readBuffer t (t.getReg .x23).toNat 96)
  have eqn : d=parentAt o.compression input p.val := by dsimp [d];rw [addr];exact prep.value
  let m:=hashed t d
  have pc : m.pc=5432 := by change (hashSetupState t).pc+4=5432;rw [(hashRegisters t prep.pc).1] <;> rfl
  have run : Runs o t m 6 1 := hashRuns o t prep.pc sb sa db da
  have wr := hashWritten t (outSlot p.val) atT.dest (by unfold outSlot;omega) d
  exact ⟨m.setPC 5468,runs_trans run (jump334 o m pc),hashEffect (s:=s) (t:=t) (m:=m) prep (hashKeeps t d) wr eqn⟩
end CommitGolfCandidate.PairCap.Batch
