import CommitGolfCandidate.RungAWrite
import CommitGolfCandidate.RungAGroupMath
import CommitGolfCandidate.RungACompactPlan
import CommitGolfCandidate.RungAGround
import CommitGolfCandidate.S4HonestTree
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1700000
attribute [local irreducible] execute DetRun readBuffer

def Blank (s : MachineState) := ∀ j,j<32 → j∉writes → readBuffer s (32*j) 32=0
def Stored (o : Oracle) (m : Message) (r : Tape) (g : Nat) (s : MachineState) := ∀ i,i<g →
  readBuffer s (nodeAddress 4 i) 32=model o m r 4 i

structure State (o : Oracle) (m : Message) (r : Tape) (g : Nat) (s : MachineState) : Prop where
  env : Env s
  src : s.getReg .x21=Z (rowBase+2208*g+1920)
  stride : s.getReg .x25=2208
  stop : s.getReg .x20=Z (nodeAddress 4 699048)
  ground : Ground o m r s
  blank : Blank s
  roots : Stored o m r g s

def stateData (o : Oracle) (m : Message) (r : Tape) (g : Nat) (s : MachineState) : Data o :=
  ⟨rowValue o m r g,fun j=>readBuffer s (32*j) 32⟩

theorem prepare {o m r s} (c : Layout) (start : State o m r c.group s) (ptr : s.getReg .x22=Z c.base)
    (limit : c.limit=min 24 (16777216-24*c.group)) :
    Live o (stateData o m r c.group s) c (initial writes) s := by
  refine ⟨start.env,start.src,ptr,?_,?_,fun _ bad=>by contradiction,fun _ bad=>by contradiction⟩
  · intro j fit
    have ok : 24*c.group+j<LENGTH:=by change 24*c.group+j<16777216;have:=c.gfit;omega
    have addr : address c (.leaf j)=finalRowAddress (24*c.group+j) := by
      dsimp [address,rowPtr,displacement,finalRowAddress];omega
    rw [addr];change readBuffer s _ 96=rowValue o m r c.group j
    rw [rowValue,dif_pos ok];exact start.ground.rows ⟨_,ok⟩
  · intro j bound
    by_cases h : j∈writes
    · simp only [initial,if_pos h,Data.eval,value,stateData]
    · exact (start.blank j bound h).trans (by simp only [initial,if_neg h,Data.eval,value])

theorem endBlanks (many : Bool) : ∀ j : Fin 32,j.val∉writes →
    ((if many then full else tailGroup).foldl update (initial writes)).cells j.val=.zero := by
  cases many <;> decide +kernel

theorem endGroup {o m r s t} (c : Layout) (beg : State o m r c.group s)
    (valid : c.limit=min 24 (16777216-24*c.group)) (many : Bool)
    (fullOrTail : c.limit=if many then 24 else 16)
    (out : Live o (stateData o m r c.group s) c ((if many then full else tailGroup).foldl update (initial writes)) t)
    (fr : Frame c s t) :
    Ground o m r t ∧ Stored o m r (c.group+1) t ∧ Blank t := by
  have dest:=destBounds c
  have loc : location c .output=nodeAddress 4 c.group:=c.address
  have gfit : c.group<levelCount 4:=c.gfit
  have gaps : Gaps t := by
    intro h p k pg
    have st : tdAddress≤unusedSlotAddr h p k:=by unfold unusedSlotAddr rowAddress tdAddress;omega
    change 4294971424≤_ at st
    have en:=padValid _ _ _ pg
    exact (fr _ _ (by omega) (by change _≤5905584160 at en;omega) (by rw [loc];exact (node_pad 4 c.group h p k (by decide) gfit pg).symm)).trans (beg.ground.gaps h p k pg)
  refine ⟨beg.ground.kept (fun a n lo hi sep=>fr a n (by omega) hi (by unfold Apart;omega)) gaps,?_,?_⟩
  · intro i small
    by_cases eq : i=c.group
    · subst i
      have op : ((if many then full else tailGroup).foldl update (initial writes)).out=some (wanted c.limit 4 0) := by
        rw [fullOrTail];cases many
        · exact verifiedTail.2.1
        · exact verifiedFull.2.1
      have output:=out.out _ op
      rw [loc] at output
      apply output.trans
      simpa only [Data.eval,stateData,show scale 4=1 by decide,Nat.one_mul,Nat.add_zero] using
        evalWanted o m r c.group c.limit c.gfit valid (fun j=>readBuffer s (32*j) 32) 4 0 (by decide) (by decide)
    · have earlier : i<c.group:=by omega
      have b:=Upper.bounds 4 i le_rfl (by decide) (by omega)
      apply (fr _ _ (by omega) (by omega) (Or.inl ?_)).trans (beg.roots i earlier)
      rw [loc];change 5301604576+Late.gapOffset i+32≤5301604576+Late.gapOffset c.group;have:=gap_mono i c.group earlier;omega
  · intro j small skip
    have v:=out.scratch j small
    rw [endBlanks many ⟨j,small⟩ skip] at v
    exact v

theorem group (o : Oracle) (m : Message) (r : Tape) (c : Layout) (s : MachineState)
    (n : Nat) (many : Bool) (valid : c.limit=min 24 (16777216-24*c.group))
    (fullOrTail : c.limit=if many then 24 else 16) (start : State o m r c.group s)
    (pc : s.pc=pcAt n) (ptr : s.getReg .x22=Z c.base)
    (sites : listed n (code (if many then full else tailGroup) c.off)=true)
    (advance : Site (n+(if many then 113 else 95)) (.ADD .x21 .x21 .x25)) :
    let k:=if many then 114 else 96
    let q:=if many then 39 else 28
    ∃ t,MRun o s k t (k+7*q) q ∧ t.pc=pcAt (n+k) ∧ State o m r (c.group+1) t ∧ t.getReg .x22=Z c.base := by
  let plan:=if many then full else tailGroup
  have count : queries plan=if many then 39 else 28:=by cases many <;> first | exact verifiedTail.2.2 | exact verifiedFull.2.2
  have size : (code plan c.off).length=if many then 113 else 95 := by cases many <;> first | exact (lengths _).1 | exact (lengths _).2
  have ok : legal c.limit writes (initial writes) plan=true:=by rw [fullOrTail];cases many <;> first |exact verifiedFull.1|exact verifiedTail.1
  obtain ⟨u,st⟩:=executePlan writes plan n _ s (prepare c start ptr valid) pc ok sites
  obtain ⟨data,roots,blanks⟩:=endGroup c start valid many fullOrTail st.live st.frame
  let t:=execInstrBr u (.ADD .x21 .x21 .x25)
  have ip:=st.pc;rw [size] at ip
  have last : MRun o u 1 t 1 0:=DetRun.step1 (advance _ ip) rfl
  have mem : t.mem=u.mem:=mem_exec_ADD ..
  have stay (q : Reg) (neq : q≠.x21) : t.getReg q=u.getReg q:=MachineState.getReg_setReg_ne u .x21 q _ neq.symm
  have stride:=(st.stable .x25 (by decide)).trans start.stride
  have reg : t.getReg .x21=Z (rowBase+2208*(c.group+1)+1920):=by
    change (u.setReg .x21 _).getReg .x21=_
    rw [MachineState.getReg_setReg_eq (by decide),st.live.source,stride]
    change Z (rowBase+2208*c.group+1920)+Z 2208=_;rw [←BitVec.ofNat_add];congr 1 <;> omega
  have endEq : (if many then 113 else 95)+1=(if many then 114 else 96):=by cases many <;> decide
  refine ⟨t,?_,?_,⟨?_,reg,(stay _ (by decide)).trans stride,(stay _ (by decide)).trans ((st.stable _ (by decide)).trans start.stop),?_,?_,?_⟩,(stay _ (by decide)).trans st.live.dest⟩
  · have tr:=st.run.trans last
    rw [size,count] at tr
    convert tr using 1 <;> omega
  · apply (pc_step_idx u _ ip).trans
    rw [Nat.add_assoc,endEq];rfl
  · exact ⟨(stay _ (by decide)).trans st.live.env.mode,(stay _ (by decide)).trans st.live.env.kind,
      (stay _ (by decide)).trans st.live.env.width,(stay _ (by decide)).trans st.live.env.root⟩
  · exact data.kept (fun _ _ _ _ _=>readBuffer_of_mem_eq mem _ _) (fun h p k g=>(readBuffer_of_mem_eq mem _ _).trans (data.gaps h p k g))
  · exact fun j h x=>(readBuffer_of_mem_eq mem _ _).trans (blanks j h x)
  · exact fun i h=>(readBuffer_of_mem_eq mem _ _).trans (roots i h)
end CommitGolfCandidate.RungA.Kernel
