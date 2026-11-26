import CommitGolfCandidate.S4PairHash
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)
private theorem noChild {l r : Option Digest} (none : (l.isSome || r.isSome)=false) : (l.isNone && r.isNone)=true:=by
  cases l <;> cases r <;> simp_all

private theorem skipWhenAbsent (H : Compression) (l r : Option Digest) (slot : Digest)
    (empty : (l.isSome || r.isSome)=false) : slot=mergePair .byte H l r slot:=by
  rw [mergePair,noChild empty];rfl
attribute [local irreducible] batchCap mergePair readBuffer lower List.range
theorem unusedPair (o : Oracle) (x : CheckInput) (j : Nat) (bj : j<171) (s : MachineState)
    (empty : touched o.compression (readView x) j=false) (pc : s.pc=pcAt 4495)
    (addr : s.getReg .x30=W (upperAddr j)) (slot : readBuffer s 352 32=(readView x).slot j) :
    ∃ t,PairFinished o x s t j 9 0 := by
  let u:=execInstrBr s (ptrCode .x14 352)
  have prepare:=stepAdd .check s 4495 .x14 .x0 352 (by decide) pc (stood pairSites.unusedPtr)
  have copy:=dwordBlock .check u .x14 .x30 4496 352 (upperAddr j) 0 0 4 (by decide) (by decide)
    (addPC _ _ _ pc) (by decide) pairSites.unused rfl ((keepAdd s .x14 .x0 .x30 352 (by decide)).trans addr)
    (by decide) (by unfold upperAddr;omega) (by decide) (by decide) (by decide) (by unfold upperAddr MEMORY_BYTES;omega)
    (Or.inl (by unfold upperAddr;omega))
  let t:=copyBlock .x14 .x30 0 0 (dwords 4) u
  have move : Moved s t 352 (upperAddr j) 32:=copy.bytes.congr rfl rfl
  have safe : ∀ r : Reg,whilePair r → r≠.x6 ∧ r≠.x14:=by intro r;cases r <;> decide
  refine ⟨t,⟨ofRuns o (prepare.trans copy.run),copy.endPC,fun r h=>(copy.regs r (Ne.symm (safe r h).1)).trans
    (keepAdd s .x14 .x0 r 352 (Ne.symm (safe r h).2)),highWrite move.frame,?_⟩⟩
  have got:=(move.read (by unfold upperAddr;omega)).trans slot
  apply got.trans
  let a:=leftChild o.compression (readView x) j;let b:=rightChild o.compression (readView x) j
  rw [capDecomposition]
  exact skipWhenAbsent o.compression a b _ empty

theorem Seen.pairWrite {H : Compression} {v : View} {s t : MachineState} {j : Nat} (seen : Seen H v 128 s)
    (frame : HighExcept s t (upperAddr j) 32) : Seen H v 128 t:=by
  refine ⟨?_,?_,seen.agree⟩
  · intro u bu;exact (frame _ (by omega) (by omega) (Or.inl (by unfold upperAddr;omega))).trans (seen.flags u bu)
  · intro u bu d e
    exact (frame.read (by omega) (by omega) (Or.inl (by unfold upperAddr;omega))).trans (seen.leaves u bu d e)

structure AfterPair (o : Oracle) (x : CheckInput) (s t : MachineState) (j steps q : Nat) : Prop where
  run : CheckRuns o s t steps q
  pc : t.pc=pcAt 4504
  env : Env x t
  seen : Seen o.compression (readView x) 128 t
  closed : ∀ i<j+1,readBuffer t (upperAddr i) 32=batchCap .byte o.compression (readView x) i
  flags : t.getReg .x1=W (flagAddr (2*j))
  children : t.getReg .x29=W (capAddr (2*j))
  dest : t.getReg .x30=W (upperAddr j)
  remaining : t.getReg .x19=W (171-j)
  proof : t.getReg .x18=W (wireSlot (j+1))

theorem pairBody (o : Oracle) (x : CheckInput) (j : Nat) (bj : j<171) (s : MachineState) (f : PairCursor o.compression x s j) :
    ∃ t steps q,steps≤100 ∧ q≤1 ∧ AfterPair o x s t j steps q:=by
  obtain ⟨u,n,num,load⟩:=pairLoad o x s j bj f
  have hframe:=protectedBytes load.frame (by decide) (by decide)
  have envSafe : ∀ r : Reg,envReg r → pairKeep r:=by intro r;cases r <;> decide
  have env : Env x u:=f.toEnv.move (fun r h=>load.keep r (envSafe r h)) (f.data.scratch hframe)
  have seen:=f.seen.scratch hframe
  have out: u.getReg .x30=W (upperAddr j):=(load.keep _ (by decide)).trans f.dest
  have go : ∃ t m q,m≤32 ∧ q≤1 ∧ PairFinished o x u t j m q:=by
    by_cases hit:touched o.compression (readView x) j=true
    · have pc:=load.pc;rw [hit] at pc
      obtain ⟨t,done⟩:=touchedPair o x j bj u hit pc load.left load.right ((load.keep _ (by decide)).trans f.children) out seen load.slot env
      exact ⟨t,32,1,le_rfl,le_rfl,done⟩
    · have miss:=Bool.eq_false_iff.mpr hit;have pc:=load.pc;rw [miss] at pc
      obtain ⟨t,done⟩:=unusedPair o x j bj u miss pc out load.slot
      exact ⟨t,9,0,by decide,by decide,done⟩
  obtain ⟨t,m,q,mb,qb,done⟩:=go
  have keep (r : Reg) (h : pairKeep r) : t.getReg r=s.getReg r:=(done.keep r (Or.inl h)).trans (load.keep r h)
  have frame : HighExcept s t (upperAddr j) 32:=(highOnly load.frame (by decide)).trans done.frame
  have data:=frame.env (by unfold upperAddr;omega) f.data
  refine ⟨t,n+m,q,by omega,qb,⟨?_,done.pc,f.toEnv.move (fun r h=>keep r (envSafe r h)) data,f.seen.pairWrite frame,?_,
    (keep _ (by decide)).trans f.flagsPtr,(keep _ (by decide)).trans f.children,(keep _ (by decide)).trans f.dest,
    (keep _ (by decide)).trans f.remaining,(done.keep _ (Or.inr rfl)).trans load.cursor⟩⟩
  · simpa only [Nat.zero_add] using load.run.trans done.run
  · intro i bi;by_cases same:i=j
    · subst i;exact done.value
    · exact (frame.read (by unfold upperAddr;omega) (by unfold upperAddr;omega) (Or.inl (by unfold upperAddr;omega))).trans (f.closed i (by omega))
end CommitGolfCandidate.S4.Machine
