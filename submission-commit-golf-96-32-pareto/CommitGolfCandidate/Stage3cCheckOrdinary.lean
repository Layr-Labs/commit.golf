import CommitGolfCandidate.Stage3cCheckRecord
import CommitGolfCandidate.Stage3cCheckAdvance
import CommitGolfCandidate.Stage3cCheckCompare
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
structure Outcome (o : Oracle) (s : MachineState) (P : Prop) (maxSteps maxCalls : Nat) : Prop where
  reaches : ∃ n q ex,n≤maxSteps ∧ q≤maxCalls ∧ ex≠Exit.unfinished ∧ (ex=.success ↔ P) ∧ Finished o s n q ex

theorem Outcome.prefix {o s t P a m b k} (head : Flow o s t a m) (tail : Outcome o t P b k) :
    Outcome o s P (a+b) (m+k) := by
  obtain ⟨⟨n,q,ex,nmax,qmax,done_,iff,run⟩⟩:=tail
  exact ⟨⟨a+n,m+q,ex,by omega,by omega,done_,iff,head.finish run⟩⟩
theorem Outcome.weaken {o s P Q m n a b} (src : Outcome o s P m a) (eq : P↔Q) (lim : m≤n) (calls : a≤b) : Outcome o s Q n b := by
  obtain ⟨⟨k,q,ex,km,qm,done_,iff,r⟩⟩:=src
  exact ⟨⟨k,q,ex,by omega,by omega,done_,iff.trans eq,r⟩⟩

def rowsValid (H : Compression) (x : CheckInput) (r n : Nat) := ∀ j,r≤j → j<r+n → pathValue H false x j 24=x.commitment
private theorem rows_cons (H : Compression) (x : CheckInput) (r n : Nat) :
    rowsValid H x r (n+1) ↔ pathValue H false x r 24=x.commitment ∧ rowsValid H x (r+1) n := by
  constructor
  · intro all;exact ⟨all r le_rfl (by omega),fun j a b=>all j (by omega) (by omega)⟩
  · rintro ⟨one,tail⟩ j a b;by_cases h:j=r
    · subst j;exact one
    · exact tail j (by omega) (by omega)

theorem reject_iff {P : Prop} (no : ¬P) : Exit.failure=Exit.success ↔ P := ⟨fun h=>False.elim ((by decide : Exit.failure≠Exit.success) h),fun h=>(no h).elim⟩
private def ordinaryCmp : CompareSite:=⟨2126,2144,false,.x27,.x8,.x6,.x7⟩
private theorem cmp_live (q : Reg) (h : q∈persistentRegs) : q≠ordinaryCmp.temp ∧ q≠ordinaryCmp.other := by
  cases q <;> simp_all [persistentRegs,ordinaryCmp]

set_option maxRecDepth 12000 in
theorem ordinary_rows (o : Oracle) (x : CheckInput) (r n : Nat) (s : MachineState) (count : r+n=x.positions.card)
    (mode : x.positions.card≠BATCH) (old : RecordRegs false x r s)
    (pc : s.pc=pcAt (if r<x.positions.card then recordBegin false else afterRows false)) :
    Outcome o s (rowsValid o.compression x r n) (3720*n+3) (100*n) := by
  induction n generalizing s r with
  | zero=>
    have done_ : r=x.positions.card:=by omega
    have pass : rowsValid o.compression x r 0:=fun j a b=>by omega
    rw [if_neg (by omega)] at pc
    exact ⟨⟨3,0,.success,by decide,by decide,by decide,⟨fun _=>pass,fun _=>rfl⟩,verdict o s true pc⟩⟩
  | succ n ih=>
    have lt : r<x.positions.card:=by omega
    rw [if_pos lt] at pc
    obtain ⟨t,nr,rs,record⟩:=check_record o x false r s lt (decide_eq_false mode).symm pc old
    let updated:=t.setReg .x23 (W (x.positions.card-(r+1)))
    have root : readBuffer t rootBase 32=x.commitment:=(record.next.high.read rootBase 32 le_rfl (by decide)).trans (loaded_root x)
    have rr : t.getReg .x8=W rootBase:=record.next.root
    have dg : t.getReg .x27=W digestBuf:=record.next.fixed.digest
    obtain ⟨u,nc,cs,cmp,up,mem,keep⟩:=compare_digest o t ordinaryCmp (by decide +kernel)
      digestBuf rootBase record.pc dg rr ⟨by decide,by decide⟩ ⟨by decide,by decide⟩
    have test : readBuffer t digestBuf 32=readBuffer t rootBase 32 ↔ pathValue o.compression false x r 24=x.commitment := by rw [root];exact iff_of_eq (congrArg (·=x.commitment) record.value)
    have head:=record.run.trans cmp
    change nr≤3700 at rs
    change Flow o s u (nr+nc) 100 at head
    by_cases agrees : pathValue o.compression false x r 24=x.commitment
    · rw [if_pos (test.mpr agrees)] at up
      have bound : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
      have countReg : u.getReg .x23=W (x.positions.card-r):=(keep _ (by decide) (by decide)).trans record.count
      obtain ⟨na,as_,advance⟩:=record_advance o u false x.positions.card r bound lt up countReg
      let z:=advanced u false x.positions.card r
      have kz (q : Reg) (h : q∈persistentRegs) : u.getReg q=t.getReg q:=keep q (cmp_live q h).1 (cmp_live q h).2
      have state : RecordRegs false x (r+1) z:=record.next.advanced mem kz
      have after:=ih (s:=z) (r:=r+1) (by omega) state rfl
      have whole:=Outcome.prefix (head.trans advance) after
      apply whole.weaken
      · rw [rows_cons];exact ⟨fun h=>⟨agrees,h⟩,And.right⟩
      · omega
      · omega
    · rw [if_neg (fun h=>agrees (test.mp h))] at up
      have no : ¬rowsValid o.compression x r (n+1):=fun all=>agrees ((rows_cons ..).mp all).1
      exact ⟨⟨nr+nc+3,100,.failure,by omega,by omega,(by decide : Exit.failure≠.unfinished),reject_iff no,
        head.finish (verdict o u false up)⟩⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
