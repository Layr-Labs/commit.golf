import CommitGolfCandidate.S5BucketCheck
import CommitGolfCandidate.S5CheckRecord
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
theorem RecordRegs.bucket_saved {b x r} {s u : MachineState} (g : RecordRegs b x (r+1) (s.setReg .x23 (W (x.positions.card-(r+1)))))
    (m : Outside s u marksBuf bucketSpan) (keep : ∀ q∈persistentRegs,u.getReg q=s.getReg q) :
    RecordRegs b x (r+1) (u.setReg .x23 (W (x.positions.card-(r+1)))) := by
  let before:=s.setReg .x23 (W (x.positions.card-(r+1)))
  let after_:=u.setReg .x23 (W (x.positions.card-(r+1)))
  have out : Outside before after_ marksBuf bucketSpan:=m
  have stable (q : Reg) (mem : q∈persistentRegs) : after_.getReg q=before.getReg q:=by
    by_cases eq:q=.x23
    · subst q;rfl
    · exact (MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm eq)).trans ((keep q mem).trans (MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm eq)).symm)
  refine ⟨(stable _ (by decide)).trans g.root,(stable _ (by decide)).trans g.indices,(stable _ (by decide)).trans g.values,
    (stable _ (by decide)).trans g.count,(stable _ (by decide)).trans g.leaf,⟨(stable _ (by decide)).trans g.fixed.radix,
    (stable _ (by decide)).trans g.fixed.row,(stable _ (by decide)).trans g.fixed.chain,(stable _ (by decide)).trans g.fixed.digest⟩,
    g.stream.frame out (by decide) (by decide) (by decide) (stable _ (by decide)) (stable _ (by decide))
      (stable _ (by decide)) (stable _ (by decide)),g.high.after out (by decide)⟩

def batchRowsPC (r : Nat) := if r<128 then 233 else 810
structure RowsPassed (o : Oracle) (x : CheckInput) (s : MachineState) (n : Nat) : Prop where
  valid : Consistent o.compression x 128
  reached : ∃ t steps,steps≤11030*n ∧ Flow o s t steps (76*n) ∧ t.pc=pcAt 810 ∧ RecordRegs true x 128 t ∧ BucketTable o.compression x 128 t
structure RowsFailed (o : Oracle) (x : CheckInput) (s : MachineState) (n : Nat) : Prop where
  invalid : ¬Consistent o.compression x 128
  reached : ∃ steps q,steps≤11030*n+3 ∧ q≤76*n ∧ Finished o s steps q .failure

attribute [local irreducible] readBuffer view lookup lower
set_option maxRecDepth 12000 in
theorem batch_rows (o : Oracle) (x : CheckInput) (r n : Nat) (s : MachineState) (len : x.positions.card=128) (range : r+n=128)
    (pc : s.pc=pcAt (batchRowsPC r)) (reg : RecordRegs true x r s) (table : BucketTable o.compression x r s)
    (consistent : Consistent o.compression x r) : RowsPassed o x s n ∨ RowsFailed o x s n := by
  induction n generalizing r s with
  | zero=>
    have end_ : r=128:=by omega
    subst r;exact Or.inl ⟨consistent,⟨s,0,by decide,Flow.refl o s,pc,reg,table⟩⟩
  | succ n ih=>
    have earlier : r<128:=by omega
    have start : s.pc=pcAt 233:=pc.trans (congrArg pcAt (if_pos earlier))
    obtain ⟨u,a,alim,out⟩:=check_record o x true r s (by omega) (decide_eq_true len).symm start reg
    have there:=table.after_record out.frame
    have dig : readBuffer u digestBuf 32=lower o.compression x r:=by simpa only [lower,S5.Auth.lower,pathValue,pathDepth,ite_true] using out.value
    have pos : u.getReg .x14=W (bucket x r):=by simpa only [bucket,S5.Auth.bucket,positionAt,(view_indices x true).1,pathDepth,ite_true] using out.parent
    have dp : u.getReg .x27=W digestBuf:=out.next.fixed.digest
    obtain ⟨v,b,blim,check⟩:=check_bucket o x r u there out.pc pos dp dig
    have partial_ : Flow o s v (a+b) 76:=out.run.trans check.run
    change a≤11000 at alim
    by_cases same : agreesBucket o.compression x r
    · have ip : v.pc=pcAt 807:=check.pc.trans (congrArg pcAt (if_pos same))
      have cnt : v.getReg .x23=W (x.positions.card-r):=(check.keep _ (by decide)).trans out.count
      obtain ⟨z,zlim,next⟩:=record_advance o v true x.positions.card r (by rw [len];decide) (by omega) ip cnt
      let w:=advanced v true x.positions.card r
      have regs:=out.next.bucket_saved check.mem check.keep
      have newReg : RecordRegs true x (r+1) w:=regs.advanced rfl (fun _ _=>rfl)
      have tab : BucketTable o.compression x (r+1) w:=(check.table same).same rfl
      have nw : w.pc=pcAt (batchRowsPC (r+1)):=by unfold w advanced batchRowsPC;rw [len];rfl
      have front : Flow o s w (a+b+z) 76:=partial_.trans next
      rcases ih (r+1) w (by omega) nw newReg tab (consistent_next consistent same) with passed|failed
      · obtain ⟨valid,⟨t,m,limit,last,end_,final,memory⟩⟩:=passed
        refine Or.inl ⟨valid,⟨t,a+b+z+m,by omega,?_,end_,final,memory⟩⟩
        simpa only [Nat.mul_succ,Nat.add_comm 76 (76*n)] using front.trans last
      · obtain ⟨bad,⟨m,q,limit,bound,last⟩⟩:=failed
        exact Or.inr ⟨bad,⟨a+b+z+m,76+q,by omega,by omega,front.finish last⟩⟩
    · have ip : v.pc=pcAt 2333:=check.pc.trans (congrArg pcAt (if_neg same))
      exact Or.inr ⟨inconsistent same earlier,⟨a+b+3,76,by omega,by omega,partial_.finish (verdict o v false ip)⟩⟩
end CommitGolfCandidate.S5Machine.Check
