import CommitGolfCandidate.S4Fresh
import CommitGolfCandidate.S4CompareLoop
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)
attribute [local irreducible] pathPrice nodePC recordAt readBuffer

structure BatchRowEnd (o : Oracle) (x : CheckInput) (s t : MachineState) (r n : Nat) : Prop where
  run : CheckRuns o s t n 19
  pc : t.pc=pcAt (if r+1<x.positions.card then rowStart true else endOfRows true)
  env : Env x t
  cursor : Cursor x t (r+1)
  seen : Seen o.compression (readView x) (r+1) t

theorem batchRecordStep (o : Oracle) (x : CheckInput) (r : Nat) (s : MachineState) (b : x.positions.card=128)
    (br : r<128) (pc : s.pc=pcAt (rowStart true)) (env : Env x s) (cur : Cursor x s r) (seen : Seen o.compression (readView x) r s) :
    (¬BatchValid .packed o.compression (readView x) x.commitment ∧ ∃ n≤2000,Finishes o s n 19 .failure) ∨
    (∃ t n,n≤2000 ∧ BatchRowEnd o x s t r n) := by
  obtain ⟨u,run,at4343,frame,delta,idx,dig⟩:=checkedRow o x true r s (by omega) (decide_eq_true (show x.positions.card=BATCH from b)).symm pc env cur
  let v:=readView x;let j:=bucket v r;let d:=lower .packed o.compression v r
  let prior:=served o.compression v r j
  have seen' : Seen o.compression v r u:=seen.scratch delta
  have inside : j<342:=indexInside (v.idx r) 15
  have flag : byte u (flagAddr j)=if prior.isSome then 1 else 0:=seen'.flags j inside
  have amount : recordFuel true≤1711:=by change 111+pathPrice true 15≤111+1600;exact Nat.add_le_add_left pathEnd.2.2.2 111
  obtain ⟨t,check⟩:=probeFlag o u j inside prior.isSome at4343 idx flag
  have initialWork:=run.trans check.run
  have pending : PendingRow x t r:=frame.transfer check.keep (frame.data.regs check.mem)
  have seent : Seen o.compression v r t := seen'.sameMem check.mem
  have child : readBuffer t 256 32=d:=(read_buffer_memory_congr t u check.mem _ _).trans dig
  cases stated : prior with
  | none=>
    have start : t.pc=pcAt 4353:=by have e:=check.pc;rw [stated] at e;exact e
    obtain ⟨z,add,fpc,live,full⟩:=freshRecord o x t r v start pending seent stated inside child check.faddr check.addr check.root
    obtain ⟨f,n,limit,next⟩:=advanceRow o x true z r (by omega) fpc live
    have done : CheckRuns o s f (recordFuel true+9+11+n) 19:=by
      have h:=(initialWork.trans add).trans next.run;rw [stated] at h;exact h
    exact Or.inr ⟨f,_,by omega,⟨done,next.pc,next.env,next.cursor,full.sameMem next.mem⟩⟩
  | some old=>
    have start : t.pc=pcAt 4364:=by have e:=check.pc;rw [stated] at e;exact e
    have val:=seent.leaves j inside old stated
    have ok : AddrOK (capAddr j) 32:=by constructor <;> simp only [capAddr,MEMORY_BYTES] <;> omega
    rcases compareDigest .seen o t 256 (capAddr j) start check.root check.addr ⟨by decide,by decide⟩ ok with
      ⟨same,z,accepted⟩|⟨ne,n,hn,fail⟩
    · have agree : d=old:=child.symm.trans (same.trans val)
      have keep (q : Reg) (hq : caller q) : z.getReg q=t.getReg q:=by
        have safe : ∀ q : Reg,caller q → q≠.x6 ∧ q≠.x7:=by intro q;cases q <;> decide
        exact accepted.regs q (safe q hq).1 (safe q hq).2
      have pz : PendingRow x z r :=pending.transfer keep (pending.data.regs accepted.mem)
      have full : Seen o.compression v (r+1) z:= (seent.duplicate (stated.trans (congrArg some agree.symm))).sameMem accepted.mem
      obtain ⟨f,m,lim,next⟩:=advanceRow o x true z r (by omega) accepted.pc pz
      have done : CheckRuns o s f (recordFuel true+10+12+m) 19:=by
        have h:=(initialWork.trans accepted.run).trans next.run;rw [stated] at h;exact h
      exact Or.inr ⟨f,_,by omega,⟨done,next.pc,next.env,next.cursor,full.sameMem next.mem⟩⟩
    · have different : old≠d:=fun eqv=>ne (child.trans (eqv.symm.trans val.symm))
      have done : Finishes o s (recordFuel true+10+n) 19 .failure:=by
        have h:=initialWork.finish fail;rw [stated] at h;exact h
      exact Or.inl ⟨disagreement br stated different _,_,by omega,done⟩

structure RecordsEnd (o : Oracle) (x : CheckInput) (s t : MachineState) (n steps : Nat) : Prop where
  run : CheckRuns o s t steps (19*n)
  pc : t.pc=pcAt (if n<128 then rowStart true else endOfRows true)
  env : Env x t
  cursor : Cursor x t n
  seen : Seen o.compression (readView x) n t

theorem manyRecords (o : Oracle) (x : CheckInput) (s : MachineState) (batch : x.positions.card=128)
    (pc : s.pc=pcAt (rowStart true)) (env : Env x s) (cur : Cursor x s 0) (empty : Seen o.compression (readView x) 0 s)
    (n : Nat) (cap : n≤128) :
    (¬BatchValid .packed o.compression (readView x) x.commitment ∧ ∃ a q,a≤2000*n ∧ q≤19*n ∧ Finishes o s a q .failure) ∨
    (∃ t a,a≤2000*n ∧ RecordsEnd o x s t n a) := by
  induction n with
  | zero=>exact Or.inr ⟨s,0,le_rfl,⟨CheckRuns.refl o s,pc,env,cur,empty⟩⟩
  | succ n ih=>
    rcases ih (by omega) with ⟨bad,a,q,ha,hq,fail⟩|⟨u,a,ha,f⟩
    · exact Or.inl ⟨bad,a,q,by omega,by omega,fail⟩
    · have go : u.pc=pcAt (rowStart true):=by have e:=f.pc;rw [if_pos (by omega : n<128)] at e;exact e
      rcases batchRecordStep o x n u batch (by omega) go f.env f.cursor f.seen with
        ⟨bad,m,hm,fail⟩|⟨t,m,hm,next⟩
      · exact Or.inl ⟨bad,a+m,19*n+19,by omega,by omega,f.run.finish fail⟩
      · refine Or.inr ⟨t,a+m,by omega,⟨?_,?_,next.env,next.cursor,next.seen⟩⟩
        · rw [Nat.mul_succ];exact f.run.trans next.run
        · simpa only [batch] using next.pc
end CommitGolfCandidate.S4.Machine
