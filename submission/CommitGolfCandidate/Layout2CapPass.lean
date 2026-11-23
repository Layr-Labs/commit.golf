import CommitGolfCandidate.Layout2CapTail
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.Layout2.Quartet (checkImage)
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

theorem pass (s : MachineState) (k len : Nat) (args : Input s k len) (here : s.pc=pc 1002)
    (data : AtData s) (clean : ∀ j,j<952 → byte s (scratchBase+j)=0) :
    let base:=proofBase+534*k
    let n:=len-534*k
    ∃ t h cost, h≤200+108*n ∧ Runs checkImage s t h cost ∧
      (if Good k len then t.pc=pc 1001 ∧ Writes s t base n (result s base n) ∧ Kept temps s t
       else t.pc=pc 364) := by
  dsimp only
  let base:=proofBase+534*k
  let n:=len-534*k
  have card:=args.count;have capacity:=args.capacity
  obtain ⟨g,rg,pg,mg,regG,kg⟩:=ctl_guard s here
  have required : (s.getReg .x16)*534#64=addr (534*k) := by
    rw [args.card,show 534#64=addr 534 from rfl,←BitVec.ofNat_mul,Nat.mul_comm]
  rw [args.length,required,ult _ _ (by omega) (by omega)] at pg
  by_cases short : len<534*k
  · have bad : ¬Good k len := fun g=>by have:=g.1;omega
    exact ⟨g,3,6,by omega,rg,by simpa [bad,short] using pg⟩
  · have long : 534*k≤len := by omega
    have endG : g.pc=pc 1005 := by simpa [short] using pg
    obtain ⟨a,ra,pa,ma,regA,ka⟩:=ctl_empty g endG
    have keep:=kg.trans ka
    have ag:=rg.thenDo ra
    have sep : scratchBase+2136≤base := by dsimp [base,scratchBase,proofBase];omega
    have room : base+n≤tableBase := by dsimp [base,n,proofBase,tableBase];omega
    rw [kg _ (by decide),args.card] at pa
    by_cases emp : k=0
    · subst k
      have pcA : a.pc=pc 1154 := by simpa [addr] using pa
      obtain ⟨b,rb,pb,mb,regB,kb⟩:=ctl_emptyLen a pcA
      rw [keep _ (by decide),args.length] at pb
      by_cases zeroLen : len=0
      · subst len
        have pcB : b.pc=pc 1155 := by simpa [addr] using pb
        obtain ⟨t,rt,pt,mt,_,kt⟩:=ctl_emptyExit b pcB
        exact ⟨t,6,9,by decide,(ag.thenDo rb).thenDo rt,by rw [if_pos (by decide : Good 0 0)];exact ⟨pt,(writes_zero s _ _).move rfl (mt.trans (mb.trans (ma.trans mg))),keep.trans (kb.trans kt)⟩⟩
      · have ne : addr len≠0#64 := (addr_ne (by omega) (by decide : 0<2^64)).2 zeroLen
        have bad : ¬Good 0 len := fun h=>zeroLen (h.2.2 rfl)
        exact ⟨b,5,8,by omega,ag.thenDo rb,by simpa [bad,ne] using pb⟩
    · have ne : addr k≠0#64 := (addr_ne (by omega) (by decide : 0<2^64)).2 emp
      have pcA : a.pc=pc 1006 := by simpa [ne] using pa
      obtain ⟨b,rb,pb,mb,regB,kb⟩:=ctl_init a pcA
      have measure : a.getReg .x6=addr (534*k) := by simp [regA,regG,required]
      have left : addr len-addr (534*k)=addr n := by
        rw [show len=n+534*k by dsimp [n];omega,←addr_add,BitVec.add_sub_cancel]
      have cur : Cursor s b base n 0 := by
        refine ⟨pb,?_,?_,?_,?_,(Output.zero s base _).mem (mb.trans (ma.trans mg)),keep.trans kb⟩
        · simp [regB,keep _ (by decide : Reg.x15∉temps),args.output,measure,addr_add,base]
        · simp [regB,keep _ (by decide : Reg.x17∉temps),args.length,measure,left]
        · simp [regB]
        · simp [regB]
      obtain ⟨u,ru,cu⟩:=full_loop cur data args.scratch args.stack sep room
      obtain ⟨v,ht,ct,limit,rv,vt⟩:=tail cu data args.scratch args.stack sep room
      have ran:=(((ag.thenDo rb).thenDo ru).thenDo rv)
      by_cases shape : size (tag (n%952))=n%952
      · have good : Good k len := ⟨long,shape,fun h=>False.elim (emp h)⟩
        rw [if_pos shape] at vt
        obtain ⟨pcV,wrote,kv⟩:=vt
        obtain ⟨t,rt,pt,finished,kt⟩:=clear v pcV ((kv _ (by decide)).trans args.scratch)
        refine ⟨t,_,_,?_,ran.thenDo rt,?_⟩
        · change 8+100926*(n/952)+ht+120≤200+108*n
          omega
        · rw [if_pos good];exact ⟨pt,finish_scratch wrote finished (by omega) clean,kv.trans kt⟩
      · have bad : ¬Good k len := fun g=>shape g.2.1
        rw [if_neg shape] at vt
        refine ⟨v,_,_,?_,ran,by rwa [if_neg bad]⟩
        change 8+100926*(n/952)+ht≤200+108*n
        omega
end CommitGolfCandidate.Layout2.Cap
