import CommitGolfCandidate.PairCounts
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def Finishes (o : Oracle) (s : MachineState) (k q : Nat) (ex : Exit) :=
  ∀ fuel, obs o (k+fuel) s = (ex,q)

theorem runs_finish {o : Oracle} {s t : MachineState} {a b q r : Nat} {ex : Exit}
    (run : Runs o s t a q) (fin : Finishes o t b r ex) : Finishes o s (a+b) (q+r) ex := by
  intro fuel;rw [Nat.add_assoc,run,fin]

theorem compRuns {o : Oracle} {s : MachineState} {k cyc calls : Nat} {op : OracleComp World MachineState}
    (run : ∀ fuel, execute Late.Check.Normal.checkerImage (k+fuel) s false =
      (do let t ← op; let next ← execute Late.Check.Normal.checkerImage fuel t false
          return next.charge cyc calls)) :
    Runs o s (Late.Check.Normal.checkEvaluation o op).1 k (Late.Check.Normal.checkEvaluation o op).2 := by
  intro fuel;unfold obs;rw [run,Late.Check.Normal.check_evaluation_bind]
  simp only [bind_pure_comp,Late.Check.Normal.check_evaluation_map];rfl

structure CompleteCap (H : Compression) (input : CheckInput) (s : MachineState) : Prop where
  pc : s.pc=5492
  rootPtr : s.getReg .x26=4294971392
  root : readBuffer s 4294971392 32=input.commitment
  parents : ∀ p<128,readBuffer s (4608+32*p) 32=capTable H input p

theorem compareFinal (o : Oracle) (s : MachineState) (pc : s.pc=5572)
    (left : s.getReg .x21=544) (right : s.getReg .x23=4294971392) :
    Finishes o s 15 0 (if readBuffer s 544 32=readBuffer s 4294971392 32 then .success else .failure) := by
  let same := ∀ j<4,s.getMem (s.getReg .x21+BitVec.ofNat 64 (8*j))=s.getMem (s.getReg .x23+BitVec.ofNat 64 (8*j))
  have eqn : same ↔ readBuffer s 544 32=readBuffer s 4294971392 32 := by
    rw [read_digest_eq_iff _ _ _ _ (by decide) (by decide)];dsimp [same];rw [left,right]
    simp only [BitVec.ofNat_add];rfl
  have sv : ∀ j<4,accessValid (s.getReg .x21+BitVec.ofNat 64 (8*j)) 8 := by
    intro j hj;rw [left];exact (show ∀ i : Fin 4, accessValid (544+BitVec.ofNat 64 (8*i.val)) 8 by decide) ⟨j,hj⟩
  have dv : ∀ j<4,accessValid (s.getReg .x23+BitVec.ofNat 64 (8*j)) 8 := by
    intro j hj;rw [right];exact (show ∀ i : Fin 4, accessValid (4294971392+BitVec.ofNat 64 (8*i.val)) 8 by decide) ⟨j,hj⟩
  intro fuel
  by_cases ok : same
  · have done := top_check_root_words_pc s 369 (Or.inr rfl) pc 4 (by decide) ok
    unfold obs
    rw [if_pos (eqn.mp ok),show 15+fuel=12+(3+fuel) by omega,top_check_root_matches s 369 (Or.inr rfl) pc sv dv ok,
      top_check_exit _ true done,pure_bind,Late.Check.Normal.check_evaluation_pure]
    rfl
  · obtain ⟨e,run,bad,_,_⟩ := top_check_root_rejects s 369 (Or.inr rfl) pc sv dv ok fuel false
    unfold obs;rw [if_neg (fun v=>ok (eqn.mpr v)),run,Late.Check.Normal.check_evaluation_pure];exact Prod.ext bad rfl

attribute [local irreducible] Late.Check.Normal.checkEvaluation execute top_checkCapParentLoop

structure UpperEntry (o : Oracle) (input : CheckInput) (s : MachineState) : Prop where
  pc : s.pc=5548
  r5 : s.getReg .x5=0
  r13 : s.getReg .x13=0
  r22 : s.getReg .x22=512
  r10 : s.getReg .x10=8640
  r12 : s.getReg .x12=4576
  r26 : s.getReg .x26=4294971392
  root : readBuffer s 4294971392 32=input.commitment
  slots : ∀ p<128,readBuffer s (4608+32*p) 32=capTable o.compression input p

theorem upperEntry (o : Oracle) (input : CheckInput) (s : MachineState) (inv : CompleteCap o.compression input s) :
    ∃ t, Runs o s t 14 0 ∧ UpperEntry o input t := by
  let first:=initRootState s
  let t:=checkCapParentSetupState first
  have fp : first.pc=5496 := by simp [first,initRootState,initRootOps,execInstrBr,MachineState.setPC,inv.pc]
  obtain ⟨sp,r5,_,r13,r10,r12,mem⟩ := top_check_cap_parent_setup_registers first fp
  have r22 : t.getReg .x22=512 := (check_cap_parent_setup_preserves first _ (by decide)).trans (by rfl)
  have r26 : t.getReg .x26=4294971392 := (check_cap_parent_setup_preserves first _ (by decide)).trans inv.rootPtr
  have sameMem : t.mem=s.mem := mem.trans (by rfl)
  have run1 : Runs o s first 1 0 := pureBlockRuns (fun fuel => initRootRun s inv.pc fuel false)
  have run2 : Runs o first t 13 0 := pureBlockRuns (fun fuel => top_check_cap_parent_setup first fp fuel false)
  exact ⟨t,runs_trans run1 run2,sp,r5,r13,r22,r10,r12,r26,
    (read_buffer_memory_congr t s sameMem _ _).trans inv.root,
    fun p hp => (read_buffer_memory_congr t s sameMem _ _).trans (inv.parents p hp)⟩

structure UpperDone (o : Oracle) (input : CheckInput) (s : MachineState) : Prop where
  pc : s.pc=5564
  r22 : s.getReg .x22=512
  r26 : s.getReg .x26=4294971392
  root : readBuffer s 4294971392 32=input.commitment
  computed : readBuffer s 544 32=referenceHeap o.compression 128 (capTable o.compression input) 1

theorem runUpper (o : Oracle) (input : CheckInput) (s : MachineState) (inv : UpperEntry o input s) :
    ∃ t,Runs o s t 2540 127 ∧ UpperDone o input t := by
  let op:=top_checkCapParentLoop s 127
  let t:=(Late.Check.Normal.checkEvaluation o op).1
  have reached : t ∈ support op := Late.Check.Normal.check_evaluation_support o op
  have done := top_cap_parent_loop_finished 127 (by decide) s inv.r22 inv.r12 t reached
  have run := compRuns (o:=o) (fun fuel => top_check_cap_parent_loop 127 (by decide) s (fun _=>inv.pc)
    inv.r5 inv.r13 inv.r22 inv.r10 inv.r12 fuel false)
  rw [upperCalls] at run
  refine ⟨t,run,done.1 (by decide),(done.2 .x22 (by decide)).trans inv.r22,(done.2 .x26 (by decide)).trans inv.r26,?_,
    upperRoot o s _ inv.r10 inv.r12 inv.slots⟩
  apply Eq.trans _ inv.root
  apply read_digest_congr t s 4294971392 (by decide)
  intro j hj;apply top_cap_parent_loop_support_outside 127 (by decide) s inv.r12 t reached
  right;rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)];omega

theorem finishCap (o : Oracle) (input : CheckInput) (s : MachineState) (inv : CompleteCap o.compression input s) :
    ∃ ex,Finishes o s 2571 127 ex ∧ ex≠.unfinished ∧
      (ex=.success ↔ referenceHeap o.compression 128 (capTable o.compression input) 1=input.commitment) := by
  obtain ⟨a,first,entry⟩ := upperEntry o input s inv
  obtain ⟨t,parents,done⟩ := runUpper o input a entry
  let final:=top_checkCapRootSetupState t
  have l : final.getReg .x21=544 := by change t.getReg .x22+32=544;rw [done.r22];rfl
  have d : final.getReg .x23=4294971392 := done.r26
  have x : readBuffer final 544 32=referenceHeap o.compression 128 (capTable o.compression input) 1 :=
    (read_buffer_memory_congr final t rfl _ _).trans done.computed
  have y : readBuffer final 4294971392 32=input.commitment := (read_buffer_memory_congr final t rfl _ _).trans done.root
  have setup : Runs o t final 2 0 := pureBlockRuns (fun fuel => top_check_cap_root_setup t done.pc fuel false)
  have last := compareFinal o final rfl l d
  have all := runs_finish (runs_trans (runs_trans first parents) setup) last
  by_cases good : readBuffer final 544 32=readBuffer final 4294971392 32
  · rw [if_pos good] at all
    exact ⟨.success,all,by decide,fun _=>x.symm.trans (good.trans y),fun _=>rfl⟩
  · rw [if_neg good] at all
    refine ⟨.failure,all,by decide,?_⟩
    constructor
    · intro bad;cases bad
    · intro e;exact False.elim (good (x.trans (e.trans y.symm)))
end CommitGolfCandidate.PairCap.Batch
