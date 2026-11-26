import CommitGolfCandidate.ReconstructedCheckParentWords

namespace CommitGolfCandidate.Reconstruction.CheckParentExecution
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine TwoPermutationPrototype.Sampling
open CheckValues CheckOrdinary CheckParentImage CheckParentRun CheckParentPlan CheckParentCall CheckParentWords CheckRecorded
set_option maxHeartbeats 1500000
set_option maxRecDepth 18000

attribute [local irreducible] CheckParentRun.next CheckParentRun.table CheckParentImage.program

def rows (o : Oracle) (seed : Key) (q n : Nat) := (List.range' q n).map (row o seed)


private theorem replayWith (nf : State→Option Hit)
    (o : Oracle) (env : Env) (layout : Layout env table) (d : Nat) (seed : Key)
    (params : Params o env d seed)
    (soundNext : ∀ m s, Matches env m s → Safe table m.writes → ∀ h, nf m=some h →
      ∃ t, Segment o h.steps s t [] ∧ Matches env h.state t ∧ Safe table h.state.writes ∧
        t.pc=CommitBlocks.addr (674+h.site.val))
    (n q : Nat) (endAt : q+n=work d) (m : State) (s : MachineState)
    (merges : Matches env m s) (safe : Safe table m.writes) (ok : checkWith nf d q n m=true) :
    ∃ t hit, Segment o (stepsWith nf d q n m) s t (rows o seed q n) ∧ Matches env hit.state t ∧
      Safe table hit.state.writes ∧ t.pc=CommitBlocks.addr (674+hit.site.val) ∧ stopFields d hit=true := by
  induction n generalizing q m s with
  | zero =>
    change (nf m).elim false (stopFields d)=true at ok
    change ∃ t hit, Segment o ((nf m).elim 0 Hit.steps) s t _ ∧ _
    cases nxt : nf m with
    | none=>simp [nxt] at ok
    | some hit=>
      simp only [nxt,Option.elim] at ok
      obtain ⟨t,seg,h,good,pc⟩ := soundNext m s merges safe hit nxt
      exact ⟨t,hit,by simpa [rows] using seg,h,good,pc,ok⟩
  | succ n ih =>
    change (nf m).elim false (fun h=>callFields d q h && checkWith nf d (q+1) n (modelWrite d q h.state))=true at ok
    cases nxt : nf m with
    | none=>simp [nxt] at ok
    | some hit=>
      simp only [nxt,Option.elim,Bool.and_eq_true] at ok
      obtain ⟨u,beginSegment,matchU,good,pc⟩ := soundNext m s merges safe hit nxt
      obtain ⟨v,callSegment,matchV,safeV⟩ := call_step o env layout d q seed params (by omega) hit u matchU good pc ok.1
      obtain ⟨t,last,rem,matchT,safeT,lastPc,done⟩ := ih (q+1) (by omega) _ v matchV safeV ok.2
      have once := compose (compose beginSegment callSegment) rem
      refine ⟨t,last,?_,matchT,safeT,lastPc,done⟩
      change Segment o ((nf m).elim 0 (fun h=>h.steps+1+stepsWith nf d (q+1) n (modelWrite d q h.state))) _ _ _
      simpa only [nxt,Option.elim,rows,List.range'_succ,List.map_cons,List.nil_append,List.cons_append] using once

theorem replay (o : Oracle) (env : Env) (layout : Layout env table) (d : Nat) (seed : Key)
    (params : Params o env d seed) (n q : Nat) (endAt : q+n=work d) (m : State) (s : MachineState)
    (merges : Matches env m s) (safe : Safe table m.writes) (ok : check d q n m=true) :
    ∃ t hit, Segment o (steps d q n m) s t (rows o seed q n) ∧ Matches env hit.state t ∧
      Safe table hit.state.writes ∧ t.pc=CommitBlocks.addr (674+hit.site.val) ∧ stopFields d hit=true :=
  replayWith (next table 90) o env layout d seed params (CheckParentRun.sound o env table layout 90)
    n q endAt m s merges safe ok

theorem recorded (o : Oracle) (seed : Key) (d : Nat) :
    Binding.recorded (history (rows o seed 0 (work d))) (oracleCompression o) seed (work d-1) := by
  intro j hj
  apply (mem_history _ _ _).2
  have pos : 0<work d := by have h : 1≤work d:=Nat.le_max_left ..;omega
  have jr : j∈List.range' 0 (work d) := by simp [List.mem_range'_1];omega
  have mem := List.mem_map_of_mem (f:=row o seed) jr
  change PublicRow.compression (encodeKey (key o seed j)) (pack (unpack (result o seed j))) ∈ rows o seed 0 (work d)
  rw [Binding.pack_unpack (result o seed j)]
  exact mem

theorem no_large_parent (d : Fin 24) : steps d 0 (work d) (start d)+1≤170 := (checked d).2

private theorem memory_except (env : Env) (p : Word) (xs : Writes)
    (h : ∀ y∈xs, p≠physical env y.1) : memory env p xs=env.initial.getMem p := by
  induction xs with
  | nil=>rfl
  | cons hd rest ih=>
    obtain ⟨a,x⟩ := hd
    rw [memory,ite_eq_right (h (a,x) (by simp))]
    exact ih (fun a mem=>h a (List.mem_cons_of_mem _ mem))

/-- The actual routine restores its caller's frame and return address. Its
writes are confined to the parent frame and the destination digest. -/
structure Return (env : Env) (d : Nat) (s t : MachineState) : Prop where
  pc : t.pc=((s.getReg .x1 + signExtend12 0) &&& ~~~1#64)
  sp : t.getReg .x2=s.getReg .x2
  fp : t.getReg .x8=s.getReg .x8
  ra : t.getReg .x1=s.getReg .x1
  preserved : ∀ r ∈ CheckParentPlan.preserved, t.getReg r=s.getReg r
  frame : ∀ p, (∀ (a : Loc), table.allowed a=true → (a.region=1 ∨ a.region=3) → p≠physical env a) →
    t.getMem p=s.getMem p
  output : ∀ i : Fin 4, t.getMem (physical env (loc 3 (8*i.val)))=(finalWord d i).val env

theorem execute_parent (o : Oracle) (env : Env) (layout : Layout env table) (d : Fin 24) (seed : Key)
    (params : Params o env d seed) (s : MachineState) (args : initialArgs s env d) :
    ∃ t, Segment o (steps d 0 (work d) (start d)+1) s t (rows o seed 0 (work d)) ∧ Return env d s t := by
  have run := replay o env layout d seed params (work d) 0 (by simp) (start d) s
    (initial_matches s env d args) (fun _ h=>by cases h) (verified d)
  obtain ⟨u,h,seg,m,valid,pos,stop⟩ := run
  simp only [stopFields,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at stop
  obtain ⟨⟨⟨last,ra,fp,sp,out⟩,writes⟩,saved⟩ := stop
  have last' : entry h.site=.ret := by
    cases c : entry h.site <;> simp [c] at last ⊢
  have f := fetch_action h.site u pos
  rw [last'] at f
  let t := execInstrBr u (.JALR .x0 .x1 0)
  have ret : Segment o 1 u t [] := plain o u t _ f rfl
  have original := args.1
  have carry (r : Reg) : t.getReg r = u.getReg r := rfl
  have org (r : Reg) (eq : h.state.get r=.reg r) : t.getReg r=s.getReg r := by
    rw [carry,m.regs,eq];exact congrArg (fun v : MachineState=>v.getReg r) original
  refine ⟨t,by simpa using compose seg ret,⟨?_,?_,org _ fp,org _ ra,?_,?_,?_⟩⟩
  · change (u.getReg .x1 + signExtend12 0) &&& ~~~1#64=_
    rw [←carry,org _ ra]
  · rw [carry,m.regs,sp,args.2.2.1];rfl
  · intro r hr;exact org r (saved _ hr)
  · intro p outside
    change u.getMem p=_
    rw [m.mem,memory_except env p h.state.writes (fun a inA =>outside a.1 (valid _ inA) (writes _ inA)),original]
  · intro i
    have allowed : ∀ j : Fin 4, table.allowed (loc 3 (8*j.val))=true := by unfold CheckParentRun.table; decide
    have one := look_sound env table layout _ (loc 3 (8*i.val)) (allowed i) valid
    rw [out i,←m.mem] at one
    exact one.symm

end CommitGolfCandidate.Reconstruction.CheckParentExecution
