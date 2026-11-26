import CommitGolfCandidate.ReconstructedCheckLaunchGate

namespace CommitGolfCandidate.Reconstruction.CheckLaunchBody
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CommitBlocks CheckValues CheckParentRun CheckLaunchCode
open CheckLaunchGate CheckCapArith
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

def env (s : MachineState) (count : Nat) : Env := {CheckRegion.env s CheckLayout.sp with answer:=fun _ _=>W (minimum count)}
def geometry (s : MachineState) (count : Nat) : Layout (env s count) tab := by
  have h:=CheckRegion.layout s CheckLayout.sp 2432 (by decide) (by decide) (by decide)
  exact ⟨h.safe,h.unique,h.table⟩

theorem frame (s : MachineState) (count : Nat) (xs : Writes) (safe : Safe tab xs) (p : Word)
    (away : p.toNat<CheckLayout.sp ∨ CheckLayout.fp≤p.toNat) :
    CheckValues.memory (env s count) p xs=s.getMem p := by
  induction xs with
  | nil=>rfl
  | cons row xs ih=>
    obtain ⟨q,v⟩:=row
    have ok:=safe (q,v) List.mem_cons_self
    change decide (q.region=1 ∧ q.offset.toNat%8=0 ∧ q.offset.toNat<2432)=true at ok
    rw [decide_eq_true_eq] at ok
    have z : physical (env s count) q=W (CheckLayout.sp+q.offset.toNat):=CheckRegion.addr s _ _ ok.1
    have fresh : p ≠ physical (env s count) q := by
      intro eq;have v:=congrArg BitVec.toNat (eq.trans z)
      change p.toNat=(68719473296+q.offset.toNat)%2^64 at v
      change p.toNat<68719473296 ∨ 68719475728≤p.toNat at away;omega
    rw [CheckValues.memory,ite_eq_right fresh]
    exact ih (fun r h=>safe r (List.mem_cons_of_mem _ h))

structure Slots (s : MachineState) (count len : Nat) : Prop where
  length : s.getMem (W (CheckLayout.fp-2424))=W len
  countWord : s.getMem (W (CheckLayout.fp-2416))=W count
  widths : s.getMem (W (CheckLayout.fp-2408))=W 2097352
  values : s.getMem (W (CheckLayout.fp-2400))=TwoPermutationPrototype.RV64.wordAddress CheckEntry.valuesBase
  indices : s.getMem (W (CheckLayout.fp-2392))=TwoPermutationPrototype.RV64.wordAddress CheckEntry.indexBase
  marker : s.getMem (W (CheckLayout.fp-2384))=3633
  mask : s.getMem (W CheckLayout.maskCell)=0xffffffff
  ret : s.getMem (W (CheckLayout.fp-8))=addr 20

structure Positive (s t : MachineState) (count len : Nat) : Prop where
  registers : CheckRecordABI.Registers t 0 0
  x5 : t.getReg .x5=W count
  slots : Slots t count len
  frame : ∀ p,p.toNat<CheckLayout.sp ∨ CheckLayout.fp≤p.toNat → t.getMem p=s.getMem p

private theorem endState (s t : MachineState) (count len : Nat) (fit : Matches (env s count) done t)
    (safe : Safe tab done.writes) (num : s.getReg .x5=W count) (size : s.getReg .x11=W len) : Positive s t count len := by
  let e:=env s count
  have data (i : Nat) (x : Term) (which : (i,x)∈slots) :
      t.getMem (W (CheckLayout.sp+i))=x.val e := by
    obtain ⟨same,allowed⟩:=doneFacts.2.2 (i,x) which
    have ref:=look_sound e tab (geometry s count) done.writes (loc 1 i) allowed safe
    change look tab (loc 1 i) done.writes=x at same
    rw [same] at ref
    rw [←show physical e (loc 1 i)=W (CheckLayout.sp+i) from CheckRegion.point s _ i]
    rw [fit.mem];exact ref.symm
  have reg (r : Reg) (x : Term) (ok : (r,x)∈registers) : t.getReg r=x.val e := by rw [fit.regs,doneFacts.2.1 (r,x) ok]
  refine ⟨⟨fit.pc.trans doneFacts.1,reg _ (ptr 1 0) (by simp [registers]),reg _ (ptr 1 2432) (by simp [registers]),reg _ (.lit 0) (by simp [registers]),
    reg _ (.lit 0) (by simp [registers]),reg _ (.lit 10334769248) (by simp [registers]),reg _ (ptr 1 104) (by simp [registers]),reg _ (ptr 1 360) (by simp [registers])⟩,
    (reg _ (.reg .x5) (by simp [registers])).trans num,?_,?_⟩
  · exact ⟨(data 8 (.reg .x11) (by simp [slots])).trans size,(data 16 (.reg .x5) (by simp [slots])).trans num,
      data 24 (.lit 2097352) (by simp [slots]),data 32 (.lit 6039801952) (by simp [slots]),data 40 (.lit 5905584160) (by simp [slots]),
      data 48 (.lit 3633) (by simp [slots]),data 64 (.lit 0xffffffff) (by simp [slots]),data 2424 (.lit (addr 20)) (by simp [slots])⟩
  · intro p away;rw [fit.mem];exact frame s count _ safe _ away

theorem run (o : Oracle) (s : MachineState) (count len : Nat) (small : count≤2^24) (lenFit : len≤8355061248)
    (pc : s.pc=addr 29) (ra : s.getReg .x1=addr 20) (stack : s.getReg .x2=W CheckLayout.fp)
    (num : s.getReg .x5=W count) (negative : s.getReg .x10=(-1)) (size : s.getReg .x11=W len) :
    if minimum count≤len then ∃ t,Segment o 64 s t [] ∧ Positive s t count len else Reject o 48 s := by
  let e:=env s count
  have inp : Matches e start s := by
    refine ⟨pc,?_,fun _=>rfl⟩;intro r;cases r <;> first | rfl | exact ra | exact stack | exact negative
  obtain ⟨u,a,hu,safe⟩:=CheckLink.run_sound o e tab (geometry s count) firstCode _ start first s inp
    (fun _ h=>by cases h) decodedFirst first_ok
  let v:=effect u sizeCode
  have upc:=hu.pc.trans entryFacts.1
  have compute : Segment o 3 u v [] := CheckCapArith.positive o u 50 sizeCode upc (by decide)
  have uv : u.getReg .x5=W count:=by rw [hu.regs,entryFacts.2.1];exact num
  have marker : u.getReg .x12=3633:=by rw [hu.regs,entryFacts.2.2];rfl
  have value : v.getReg .x12=W (minimum count) := by
    rw [register];change ((u.getReg .x5*u.getReg .x12+7#64) >>> (3 : Nat))=_
    rw [uv,marker];exact sizeWord count small
  have hv : Matches e sized v := by
    refine ⟨location u 50 sizeCode upc,?_,fun p=>(congrFun (CheckCapArith.memory u sizeCode) p).trans (hu.mem p)⟩
    intro r
    by_cases eq : r=.x12
    · subst r;exact value
    · have nr : r∉sizeCode.map Prod.fst:=by simpa [sizeCode] using eq
      rw [outside u sizeCode r nr,hu.regs]
      simp [sized,State.set,State.get,eq]
  obtain ⟨w,b,hw,sw⟩:=CheckLink.run_sound o e tab (geometry s count) middleCode _ sized mid v hv safe decodedMiddle mid_ok
  obtain ⟨pos,sizedReg,lenReg,stackReg,failed,ret⟩:=middleFacts
  have gate:=CheckBranch.event o w 56 73 .ge .x11 .x12 68 (by decide) (hw.pc.trans pos) rfl (by decide)
  change Segment o 1 w (w.setPC (if !(w.getReg .x11).ult (w.getReg .x12) then addr 73 else addr 57)) [] at gate
  have wl : w.getReg .x11=W len := by rw [hw.regs,lenReg];exact size
  have wz : w.getReg .x12=W (minimum count) := by rw [hw.regs,sizedReg];rfl
  have inside : minimum count<2^64:=by unfold minimum;omega
  rw [wl,wz,BitVec.ult_eq_decide] at gate
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : len<2^64),Nat.mod_eq_of_lt inside] at gate
  split
  · rename_i pass
    simp only [Nat.not_lt_of_ge pass,decide_false,Bool.not_false,ite_true] at gate
    let y:=w.setPC (addr 73)
    have fy : Matches e ready y:=set_pc e mid w hw _
    obtain ⟨t,body,full,st⟩:=CheckLink.run_sound o e tab (geometry s count) lastCode _ ready done y fy sw decodedLast end_ok
    exact ⟨t,compose (compose (compose (compose a compute) b) gate) body,endState s t count len full st num size⟩
  · rename_i fail
    have low : len<minimum count:=by omega
    simp only [low,decide_true,Bool.not_true,Bool.false_eq_true,ite_false] at gate
    let y:=w.setPC (addr 57)
    have sp : y.getReg .x2=W CheckLayout.sp := by change w.getReg .x2=_;rw [hw.regs,stackReg];rfl
    have back : y.getMem (W (CheckLayout.sp+2424))=addr 20 := by
      change w.getMem (physical e (loc 1 2424))=_
      rw [hw.mem,←look_sound e tab (geometry s count) mid.writes (loc 1 2424) (by decide) sw,ret];rfl
    have minus : y.getReg .x10=(-1) := by change w.getReg .x10=_;rw [hw.regs,failed];rfl
    obtain ⟨t,epi,tpc,rv,_⟩:=CheckEpilogue.positive o y CheckLayout.sp (by decide) (by decide) rfl sp back
    exact extend (compose (compose (compose (compose a compute) b) gate) epi) (reject o t tpc (rv.trans minus))

end CommitGolfCandidate.Reconstruction.CheckLaunchBody

