import CommitGolfCandidate.S5BucketUpdate
import CommitGolfCandidate.S5BucketHeader
import CommitGolfCandidate.S5CheckAdvance
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W Outside)
def agreesBucket (H : Compression) (x : CheckInput) (n : Nat) :=
  (lookup H x n (bucket x n)).getD (lower H x n)=lower H x n
instance (H : Compression) (x : CheckInput) (n : Nat) : Decidable (agreesBucket H x n):=inferInstanceAs (Decidable (_=_))
structure BucketResult (o : Oracle) (x : CheckInput) (n : Nat) (s t : MachineState) (steps : Nat) : Prop where
  run : Flow o s t steps 0
  pc : t.pc=pcAt (if agreesBucket o.compression x n then 807 else 2333)
  table : agreesBucket o.compression x n → BucketTable o.compression x (n+1) t
  mem : Outside s t marksBuf bucketSpan
  keep : ∀ q∈persistentRegs,t.getReg q=s.getReg q

private theorem safe (q : Reg) (mem : q∈persistentRegs) : q∉bucketTemps ∧ q≠.x28 ∧ q≠.x30 ∧ q≠.x31:=by
  cases q <;> simp_all [persistentRegs,bucketTemps]
attribute [local irreducible] readBuffer lower lookup
set_option maxRecDepth 10000 in
theorem check_bucket (o : Oracle) (x : CheckInput) (n : Nat) (s : MachineState)
    (old : BucketTable o.compression x n s) (pc : s.pc=pcAt 771) (idx : s.getReg .x14=W (bucket x n))
    (cur : s.getReg .x27=W digestBuf) (data : readBuffer s digestBuf 32=lower o.compression x n) :
    ∃ t steps,steps≤26 ∧ BucketResult o x n s t steps := by
  let j:=bucket x n
  let H:=o.compression
  have inside : j<342:=bucket_bound x n
  obtain ⟨u,hd⟩:=bucket_header o s j (lookup H x n j) inside pc idx (old.mark j inside)
  have up:=hd.pc
  have digest : readBuffer u digestBuf 32=lower H x n:=(read_buffer_memory_congr u s hd.mem _ _).trans data
  have node : u.getReg .x27=W digestBuf:=(hd.keep _ (by simp [bucketTemps])).trans cur
  cases e : lookup H x n j with
  | none=>
    rw [e] at up
    have pass : agreesBucket H x n:=by unfold agreesBucket;change (lookup H x n j).getD _= _;rw [e];rfl
    obtain ⟨t,w⟩:=save_bucket o u j inside up hd.marks hd.slot node
    refine ⟨t,19,by decide,⟨hd.run.trans w.run,by rw [if_pos pass];exact w.pc,
      fun _=>write_bucket_table H x n o u t (old.same hd.mem) w e digest,
      fun q b al sep=>(w.frame inside q b al sep).trans (congrFun hd.mem _),?_⟩⟩
    intro q h;obtain ⟨a,b,c,_⟩:=safe q h;exact (w.keep q b c).trans (hd.keep q a)
  | some prev=>
    rw [e] at up
    obtain ⟨v,k,bill,cmp,ip,vm,preserved⟩:=compare_digest o u duplicateCmp (by decide +kernel) (bucketAddress j) digestBuf up hd.slot node
      ⟨by dsimp [bucketAddress,compBase];omega,by dsimp [bucketAddress,compBase,MEMORY_BYTES];omega⟩ ⟨by decide,by decide⟩
    have prior : readBuffer u (bucketAddress j) 32=prev:=(read_buffer_memory_congr u s hd.mem _ _).trans (old.data j inside prev e)
    have good : agreesBucket H x n ↔ prev=lower H x n:=by unfold agreesBucket;change (lookup H x n j).getD _=_ ↔ _;rw [e];rfl
    have live (q : Reg) (hq : q∈persistentRegs) : v.getReg q=s.getReg q:=by
      obtain ⟨a,_,c,d⟩:=safe q hq;exact (preserved q c d).trans (hd.keep q a)
    have same : v.mem=s.mem:=vm.trans hd.mem
    rw [prior,digest] at ip
    by_cases match_ : prev=lower H x n
    · rw [if_pos match_] at ip
      let t:=v.setPC (pcAt 807)
      have leap:=jump o v 796 807 .x0 (by decide +kernel) ip
      refine ⟨t,9+k+1,by omega,⟨(hd.run.trans cmp).trans leap,by rw [if_pos (good.mpr match_)];rfl,
        fun _=>(old.repeat e).same (t:=t) same,fun q _ _ _=>congrFun same _,fun q h=>MachineState.getReg_setPC.trans (live q h)⟩⟩
    · rw [if_neg match_] at ip
      refine ⟨v,9+k,by omega,⟨hd.run.trans cmp,by rw [if_neg (fun h=>match_ (good.mp h))];exact ip,
        fun h=>False.elim (match_ (good.mp h)),fun q _ _ _=>congrFun same _,live⟩⟩
end CommitGolfCandidate.S5Machine.Check
