import CommitGolfCandidate.ChainedFastOps

namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 2200000
attribute [local irreducible] execute writeBits readBuffer

def Charge (s : MachineState) (prog : OracleComp World MachineState) (steps cycles calls : Nat) :=
  ∀ fuel coins, execute chainedCommitImage (steps+fuel) s coins =
    (do let t←prog; let r←execute chainedCommitImage fuel t coins; return r.charge cycles calls)

theorem Charge.thenDo {s : MachineState} {p : OracleComp World MachineState} {f : MachineState→OracleComp World MachineState}
    {u v c x y z : Nat} (one : Charge s p u v c) (next : ∀ t∈support p, Charge t (f t) x y z) :
    Charge s (p >>= f) (u+x) (v+y) (c+z) := by
  intro fuel coins;rw [Nat.add_assoc,one (x+fuel) coins,bind_assoc]
  apply bind_congr_of_forall_mem_support;intro t mem
  rw [next t mem fuel coins];simp [bind_assoc,Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

private theorem ordinary {s t : MachineState} {op : Instr}
    (atPC : fetch chainedCommitImage s=some (.base op))
    (step : ordinaryStep s (.base op)=some t) (cost: instructionCycles (.base op)=1) :
    Charge s (pure t) 1 1 0 := by
  intro fuel coins;rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ atPC step,cost,pure_bind]

private theorem ptrAligned {n : Nat} (b : Bounds n) (p : Port) : (ptr n p).toNat%8=0 := by
  rw [ptr,word_addr b,aligned]
private theorem ptrValid {n : Nat} (b : Bounds n) (p : Port) (bytes : Nat) (small:bytes≤64) :
    rangeValid (ptr n p) bytes=true := by
  simp only [rangeValid,decide_eq_true_eq,ptr,word_addr b,MEMORY_BYTES];have:=address_room b p.slot;omega

theorem cmd_charge (n : Nat) (k : Lane) (b : Bounds n) (a : Cmd) (m : Known) (s : MachineState)
    (regs : Tracked n k m s) (allowed : permits m a=true)
    (fetched : fetch chainedCommitImage s=some (.base (a.op k))) :
    Charge s (command n s a) 1 (1+7*a.calls) a.calls := by
  cases a with
  | get r i =>
    have base : m .x6=some .childBase := by simp [permits] at allowed;exact allowed.2
    have addr:= (congrArg (· +signExtend12 (childOff k i.val)) (regs _ _ base)).trans (child_effective n k i)
    apply ordinary fetched _ rfl
    simp [ordinaryStep,Cmd.op,memoryArgumentsValid,memAccess,addr,access b,execInstrBr,putR,cslot]
  | put i r =>
    have base : m .x6=some .childBase := by simpa [permits] using allowed
    have addr:= (congrArg (· +signExtend12 (childOff k i.val)) (regs _ _ base)).trans (child_effective n k i)
    apply ordinary fetched _ rfl
    simp [ordinaryStep,Cmd.op,memoryArgumentsValid,memAccess,addr,access b,execInstrBr,putM,cslot]
  | «calc» r ar =>
    cases ar <;> apply ordinary fetched _ rfl <;> rfl
  | srcChild =>
    have base : m .x6=some .childBase := by simpa [permits] using allowed
    have addr:= (congrArg (· +signExtend12 (childOff k 0)) (regs _ _ base)).trans (child_effective n k 0)
    apply ordinary fetched _ rfl
    change some (putR s .x10 _) = _;rw [addr];rfl
  | dstParent =>
    have base : m .x7=some .parentBase := by simpa [permits] using allowed
    have addr:=(congrArg (· +signExtend12 (parentOff k)) (regs _ _ base)).trans (parent_effective n k)
    apply ordinary fetched _ rfl
    change some (putR s .x12 _) = _;rw [addr];rfl
  | srcChain => exact ordinary fetched rfl rfl
  | dstChain => exact ordinary fetched rfl rfl
  | tag r =>
    apply ordinary fetched _ rfl
    change (if accessValid 256 8=true then some _ else none)=some _
    rw [if_pos (by decide)];rfl
  | getTop =>
    have base : m .x12=some (.port .parent) := by simpa [permits] using allowed
    have ea : s.getReg .x12+signExtend12 24#12=W (address n 11) := (congrArg (·+24#64) (regs _ _ base)).trans (parent_top_addr n)
    apply ordinary fetched _ rfl
    simp [ordinaryStep,Cmd.op,memoryArgumentsValid,memAccess,ea,access b,execInstrBr,putR]
  | putTop =>
    have base : m .x12=some (.port .parent) := by simpa [permits] using allowed
    have ea : s.getReg .x12+signExtend12 24#12=W (address n 11) := (congrArg (·+24#64) (regs _ _ base)).trans (parent_top_addr n)
    apply ordinary fetched _ rfl
    simp [ordinaryStep,Cmd.op,memoryArgumentsValid,memAccess,ea,access b,execInstrBr,putM]
  | hash f l =>
    simp only [permits,Bool.and_eq_true,beq_iff_eq] at allowed
    obtain ⟨⟨⟨⟨sx,dx⟩,sel⟩,sz⟩,kd⟩:=allowed
    have src : s.getReg .x10=ptr n (srcPort f):=regs _ _ sx
    have dst : s.getReg .x12=ptr n (dstPort l):=regs _ _ dx
    have zero : s.getReg .x5=0 := regs _ _ sel
    have len : s.getReg .x11=64 := regs _ _ sz
    have kind : s.getReg .x13=0 := regs _ _ kd
    have input : oracleInput s=some (.inl (readBuffer s (address n (srcPort f).slot) 64)) := by
      have hz : (s.getReg .x13).toNat=0 := by rw [kind];rfl
      unfold oracleInput;dsimp only;rw [hz]
      have inOk := ptrValid b (srcPort f) 64 (by decide)
      have outOk := ptrValid b (dstPort l) 32 (by decide)
      simp [src,dst,len,ptrAligned b,inOk,outOk,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
        show (ptr n (srcPort f)).toNat=address n (srcPort f).slot from word_addr b _,aligned]
    intro fuel coins
    rw [Nat.add_comm 1 fuel]
    simp [execute,fetched,Cmd.op,zero,input,command,writeOracleAnswer,dst,oracleCycles,
      COMPRESSION_CYCLES,Cmd.calls,bind_assoc] <;> rfl

private theorem assocReg (s : MachineState) (r : Reg) (v : Word) (nonzero:r≠.x0) (q : Reg) :
    (putR s r v).getReg q=if q=r then v else s.getReg q := by
  by_cases h:q=r
  · subst q;simp [putR,MachineState.getReg_setReg_eq nonzero]
  · simp [putR,h,MachineState.getReg_setReg_ne,Ne.symm h]

private theorem track_forget {n k m s} (tr:Tracked n k m s) (rd v) (nz:rd≠.x0) :
    Tracked n k (assign m rd none) (putR s rd v) := by
  intro r p val;rw [assocReg _ _ _ nz];by_cases eq:r=rd
  · simp [assign,eq] at val
  · rw [if_neg eq];apply tr;simp_all [assign]

private theorem track_set {n k m s} (tr:Tracked n k m s) (rd p) (nz:rd≠.x0) :
    Tracked n k (assign m rd (some p)) (putR s rd (roleValue n k p)) := by
  intro r kind val;rw [assocReg _ _ _ nz];by_cases eq:r=rd
  · simp [assign,eq] at val;subst kind;simp [eq]
  · rw [if_neg eq];apply tr;simp_all [assign]

theorem cmd_post {n k m s} (tr:Tracked n k m s) (a : Cmd) (ok:permits m a=true)
    (t : MachineState) (run:t∈support (command n s a)) :
    Tracked n k (nextRegs m a) t ∧ t.pc=s.pc+4 := by
  cases a with
  | hash f l =>
    simp only [command,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at run
    obtain ⟨y,_,rfl⟩:=run
    refine ⟨fun r k i => (writeBits_register ..).trans (tr r k i),by simp only [writeBits,MachineState.setPC]⟩
  | get r i | «calc» r i =>
    simp only [command,support_pure,Set.mem_singleton_iff] at run;subst t
    constructor
    · apply track_forget tr
      simp [permits] at ok; tauto
    · rfl
  | srcChild | srcChain | dstChain | dstParent =>
    simp only [command,support_pure,Set.mem_singleton_iff] at run;subst t
    exact ⟨track_set tr _ _ (by decide),rfl⟩
  | getTop =>
    simp only [command,support_pure,Set.mem_singleton_iff] at run;subst t
    exact ⟨track_forget tr _ _ (by decide),rfl⟩
  | put i r | tag r | putTop =>
    simp only [command,support_pure,Set.mem_singleton_iff] at run;subst t
    exact ⟨fun r role hit => by cases r <;> exact tr _ _ hit,rfl⟩

def FetchList (k : Lane) (base : Nat) (xs : List Cmd) :=
  ∀ i : Fin xs.length, ∀ s : MachineState, s.pc=pc (base+i.val) →
    fetch chainedCommitImage s=some (.base (xs[i].op k))

theorem execList (n : Nat) (k : Lane) (bound : Bounds n) (base : Nat) (xs : List Cmd)
    (m : Known) (s : MachineState) (tr:Tracked n k m s) (pc0:s.pc=pc base)
    (check:checked m xs=true) (cells:FetchList k base xs) :
    Charge s (trace n xs s) xs.length (xs.length+7*nCalls xs) (nCalls xs) := by
  induction xs generalizing base m s with
  | nil =>
    intro fuel coins;simp [trace,nCalls,Execution.charge]
  | cons a xs ih =>
    simp only [checked,Bool.and_eq_true] at check
    have fetched:=cells ⟨0,by simp⟩ s (by simpa using pc0)
    have first:=cmd_charge n k bound a m s tr check.1 fetched
    have tail (t) (hit:t∈support (command n s a)) :=
      ih (base+1) (nextRegs m a) t (cmd_post tr a check.1 t hit).1
        (by rw [(cmd_post tr a check.1 t hit).2,pc0];exact word_pc _) check.2 (by
          intro i st atPc
          simpa using cells ⟨i.val+1,by simp <;> omega⟩ st (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using atPc))
    have both:=first.thenDo tail
    simpa [trace,nCalls,Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using both

theorem countedList (oracle : Oracle) (n : Nat) (xs : List Cmd) (s : MachineState) :
    RunPublic oracle (trace n xs s) (nCalls xs) := by
  induction xs generalizing s with
  | nil => exact run_pure_public ..
  | cons a xs ih =>
    have one : RunPublic oracle (command n s a) a.calls := by
      cases a <;> try exact run_pure_public ..
      exact run_bind_public _ _ _ 1 0 (run_query_public ..) (fun _=>run_pure_public ..)
    exact run_bind_public _ _ _ _ _ one (fun t=>ih t)

end CommitGolfCandidate.Chained.Native.Fast
