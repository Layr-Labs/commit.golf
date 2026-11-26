import CommitGolfCandidate.S4BatchStart
import CommitGolfCandidate.S4UpperLoop
import CommitGolfCandidate.S4NormalEvaluation
import CommitGolfCandidate.S4PairLoop
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)
private theorem rootAddr : (Fragment.arithmetic (li2 .x14 16384)).valid .check 4833 4836 := by decide

theorem finalRoot (o : Oracle) (x : CheckInput) (s : MachineState) (pc : s.pc=pcAt (upperHeader 8))
    (env : Env x s) (level : Level o.compression (readView x) 8 s) :
    ∃ n,n≤19 ∧ Conclusion o s n 0 (batchRoot .byte o.compression (readView x)=x.commitment) := by
  let ops:=li2 .x14 16384;let u:=Sym.evaluated ops s
  obtain ⟨run,regs,mem,after⟩:=evalMath .check ops 4833 4836 s pc rootAddr
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : (li2 .x14 16384).all (fun c=>c.dst != .x0)=true) c h))
    (fun _ h=>by cases h)
  have root : readBuffer u 16384 32=batchRoot .byte o.compression (readView x):=
    (read_buffer_memory_congr u s mem _ _).trans (level 0 (by decide : 0<width (16+8)))
  have old : readBuffer u rootBase 32=x.commitment:=((env.data.regs mem).read rootBase 32 (by decide) (by decide)).trans (loaded_root x)
  have ptr : u.getReg .x14=W 16384:=(regs .x14).trans rfl
  have rptr : u.getReg .x27=W rootBase:=(regs .x27).trans env.root
  rcases compareDigest .root o u 16384 rootBase after ptr rptr ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ with
    ⟨equal,t,ok⟩|⟨ne,n,hn,fail⟩
  · exact ⟨18,by decide,⟨⟨.success,by decide,⟨fun _=>root.symm.trans (equal.trans old),fun _=>rfl⟩,
      ((ofRuns o run).trans ok.run).finish (verdict true t o ok.pc)⟩⟩⟩
  · exact ⟨3+n,by omega,⟨⟨.failure,by decide,⟨(fun e=>by cases e),fun eqv=>False.elim (ne (root.trans (eqv.trans old.symm)))⟩,
      (ofRuns o run).finish fail⟩⟩⟩

theorem batchEvaluation (o : Oracle) (x : CheckInput) (b : x.positions.card=BATCH)
    (fits : x.proof.length≤Late.submission.sizes.proof) : Evaluation o x := by
  rcases batchStart o x b fits with ⟨bad,n,nb,fail⟩|⟨size,s,env,cur,seen,pc,go⟩
  · refine ⟨n,0,by omega,Nat.zero_le _,⟨⟨.failure,by decide,⟨(fun eq=>by cases eq),?_⟩,fail⟩⟩⟩
    intro good;rw [wireValid,if_pos b] at good;exact False.elim (bad good.1)
  · have eqv : wireValid o.compression x ↔ BatchValid .byte o.compression (readView x) x.commitment:=by
      rw [wireValid,if_pos b];simp only [size,true_and]
    rcases manyRecords o x s b pc env cur seen 128 le_rfl with ⟨bad,a,q,aa,qb,fail⟩|⟨u,a,aa,rows⟩
    · exact ⟨25+a,q,by omega,by change q≤100*x.positions.card;rw [b];change q≤12800;omega,
        ⟨⟨.failure,by decide,⟨(fun eq=>by cases eq),fun good=>False.elim (bad (eqv.mp good))⟩,
          by simpa only [Nat.zero_add] using go.finish fail⟩⟩⟩
    · have pcR : u.pc=pcAt 4385:=rows.pc
      obtain ⟨v,enter,pstart⟩:=pairEnter o x u b pcR rows.env rows.cursor rows.seen
      obtain ⟨t,m,q,mm,qb,pairs,pend⟩:=pairLoop o x v pstart 171 le_rfl
      obtain ⟨inUpper,start⟩:=completedCap o x t pend
      obtain ⟨z,h,hh,uppers,ip,envZ,root⟩:=upperLayers o x t pend.toEnv inUpper start 8 le_rfl
      obtain ⟨w,ww,⟨e,ex,correct,done⟩⟩:=finalRoot o x z ip envZ root
      have agree:=rows.seen.agree
      have valid : BatchValid .byte o.compression (readView x) x.commitment ↔ batchRoot .byte o.compression (readView x)=x.commitment:=
        ⟨And.right,fun root=>⟨agree,root⟩⟩
      have reach:=(((go.trans rows.run).trans enter).trans pairs).trans uppers
      have fin:=reach.finish done
      have counted : upperQueries 8=174:=by decide
      rw [counted] at fin
      refine ⟨25+a+8+m+h+w,19*128+q+174,by omega,?_,⟨⟨e,ex,correct.trans (eqv.trans valid).symm,?_⟩⟩⟩
      · change 19*128+q+174≤100*x.positions.card;rw [b];change 19*128+q+174≤12800;omega
      · simpa only [Nat.zero_add,Nat.add_zero] using fin
end CommitGolfCandidate.S4.Machine
