import CommitGolfCandidate.Layout2TailRun
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 2000000
def prologueSteps (k : Nat) :=
  if k=0 then 19 else 9+226429*(k/4)+tailSteps (k%4)+804+14

theorem fuel_reserve (k : Nat) (fit : k≤16777216) : prologueSteps k+34359803904≤2^41 := by
  unfold prologueSteps tailSteps dispatchCost
  split_ifs <;> omega

structure Normalized (τ : Tables) (s t : MachineState) (k : Nat) : Prop where
  start : t.pc=pc 1
  register : ∀ r, t.getReg r=if r=.x6 then 534 else if r∈temps then 0 else s.getReg r
  memory : Writes s t proofBase (534*k) (resultByte τ s k)

private theorem guard_hop {I} (program : Program I) (s : MachineState) (k len : Nat)
    (here : s.pc=pc 786) (args : Input s k len) :
    ∃ t, Runs I s t 4 7 ∧ t.mem=s.mem ∧ Kept temps s t ∧ t.pc=if len<534*k then pc 364 else pc 708 := by
  have e:=move program .entry s here trivial
  let a:=after .entry s
  have g:=move program .guard a e.pos trivial
  have count : a.getReg .x16=addr k := (e.kept _ (by decide)).trans args.card
  have length : a.getReg .x17=addr len := (e.kept _ (by decide)).trans args.length
  have sizes:=args.capacity;have cardinal:=args.count
  refine ⟨after .guard a,e.run.thenDo g.run,g.mem.trans e.mem,
    (e.kept.weaken (move_temps _)).trans (g.kept.weaken (move_temps _)),?_⟩
  rw [g.pos];change (if BitVec.ult (a.getReg .x17) (a.getReg .x16 * 534) then _ else _)=_
  rw [count,length]
  change (if BitVec.ult (addr len) (addr k*addr 534)=true then pc 364 else pc 708)=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm k 534]
  have small : 534*k<2^64 := by omega
  have argsSmall : len<2^64 := by omega
  simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt argsSmall,decide_eq_true_eq]


theorem short_run {I} (program : Program I) (s : MachineState) (k len : Nat)
    (here : s.pc=pc 786) (args : Input s k len) (short : len<534*k) :
    ∃ t, Runs I s t 4 7 ∧ t.pc=pc 364 := by
  obtain ⟨t,run,_,_,dest⟩:=guard_hop program s k len here args
  exact ⟨t,run,by simpa [short] using dest⟩

/-- All admitted, sufficiently long inputs reach the original word 1 with the converted
record prefix. Only the preexisting proof bytes were read, including for partial blocks. -/
theorem prologue {I τ} (program : Program I) (wf : WellFormed τ) (s : MachineState) (k len : Nat)
    (here : s.pc=pc 786) (args : Input s k len) (long : 534*k≤len) (tables : TablesAt τ s)
    (clean : ∀ j, j<2136 → byte s (scratchBase+j)=0) :
    ∃ t, Runs I s t (prologueSteps k) (prologueSteps k+3) ∧ Normalized τ s t k := by
  obtain ⟨g,guard,memG,keepG,pcG⟩:=guard_hop program s k len here args
  have pc0 : g.pc=pc 708 := by simpa [show ¬len<534*k by omega] using pcG
  have branch:=move program .empty g pc0 trivial
  let a:=after .empty g
  have countG := (keepG .x16 (by decide)).trans args.card
  have stable := keepG.trans (branch.kept.weaken (move_temps _))
  have memA : a.mem=s.mem := branch.mem.trans memG
  by_cases empty : k=0
  · have endA : a.pc=pc 745 := by simpa [pcOut,countG,empty,addr] using branch.pos
    obtain ⟨t,tail,pcT,memT,regs⟩:=restore program a endA
    have rr : Runs I s t 19 22 := (guard.thenDo branch.run).thenDo tail
    refine ⟨t,by simpa [prologueSteps,empty] using rr,pcT,?_,?_⟩
    · intro r;rw [regs];split <;> first | rfl | (split <;> first | rfl | apply stable _ ‹_›)
    · subst k;exact (writes_zero s proofBase _).move rfl (memT.trans memA)
  · have bound:=args.count
    have nz := (addr_ne (a:=k) (b:=0) (by omega) (by decide)).2 empty
    have pcA : a.pc=pc 709 := by simpa [pcOut,countG,nz] using branch.pos
    have init:=move program .init a pcA trivial
    let m:=after .init a
    have initial : FullCursor τ k s m 0 := by
      refine ⟨init.pos,?_,?_,?_,?_,?_,stable.trans (init.kept.weaken (move_temps _))⟩
      · rw [init.regs];simpa [regOut] using (stable .x15 (by decide)).trans args.output
      · rw [init.regs];simpa [regOut] using (stable .x16 (by decide)).trans args.card
      · rw [init.regs];rfl
      · rw [init.regs];rfl
      · exact (Records.zero s proofBase _).move rfl (init.mem.trans memA)
    obtain ⟨u,runF,done⟩:=full_loop program wf s m k len args tables initial
    obtain ⟨v,runT,pcV,wrote,kept⟩:=finish_tail program wf s u k len args tables done
    obtain ⟨c,runC,clear⟩:=clear_loop program v pcV ((kept _ (by decide)).trans args.scratch)
    obtain ⟨t,runR,pcT,memT,regs⟩:=restore program c (by simpa using clear.next)
    have saved:=kept.trans (clear.kept.weaken (b:=temps) (by intro q h;cases q <;> simp_all [clearScratch,temps]))
    refine ⟨t,?_,pcT,?_,(merge_scratch wrote clear.wrote (by decide) clean).move rfl memT⟩
    · have steps:=(((((guard.thenDo branch.run).thenDo init.run).thenDo runF).thenDo runT).thenDo runC).thenDo runR
      change Runs I s t (9+226429*(k/4)+tailSteps (k%4)+804+14) (12+226429*(k/4)+tailSteps (k%4)+804+14) at steps
      rw [prologueSteps,if_neg empty]
      convert steps using 1 <;> omega
    · intro r;rw [regs];split <;> first | rfl | (split <;> first | rfl | apply saved _ ‹_›)

end CommitGolfCandidate.Layout2
