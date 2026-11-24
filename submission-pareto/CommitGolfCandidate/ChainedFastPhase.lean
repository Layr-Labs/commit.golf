import CommitGolfCandidate.ChainedFastLoop
import CommitGolfCandidate.ChainedParentPost

/-! Heights 0 to 7 in the specialized code, the hand-over to the delivered level code at
height 8, and the exact execution of the whole parent phase. -/
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
attribute [local irreducible] execute nodeSteps

/-! One height. -/

def stage (h : Low) (s : MachineState) : OracleComp World MachineState := do
  let t ← groups h (groupsN h) (ctl s (header h))
  return ctl t shift

def stageSteps (h : Low) := (header h).length+groupsN h*groupSteps h+1
def stageCycles (h : Low) := (header h).length+groupsN h*groupCycles h+1

theorem groupsN_pos (h : Low) : 1≤groupsN h := by have:=count_size h;omega

theorem header_cursor (h : Low) (s : MachineState) (lv : Level h s) :
    Cursor h (groupBase h (groupsN h)) (ctl s (header h)) := by
  have sz:=count_size h
  have keep (r : Reg) (hr : r∈([.x4,.x5,.x6,.x7,.x8,.x9,.x11,.x13] : List Reg)) := header_reg h s r hr
  have m:=getMem_of_mem (header_mem h s)
  have v:=header_values h s
  have mk:=header_masks h s
  refine ⟨⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,v.1,v.2.1,v.2.2.1,v.2.2.2.1,mk.1,mk.2⟩,?_,?_⟩
  · rw [keep .x8 (by decide)];exact lv.output
  · rw [keep .x9 (by decide)];exact lv.heap
  · rw [keep .x5 (by decide)];exact lv.selector
  · rw [keep .x11 (by decide)];exact lv.length
  · rw [keep .x13 (by decide)];exact lv.kind
  · rw [m];exact lv.z0
  · rw [m];exact lv.z1
  · rw [m];exact lv.flag
  · rw [keep .x4 (by decide)];exact lv.span
  · rw [v.2.2.2.2,ext4064,←BitVec.sub_eq_add_neg,lv.heap,lv.span]
    exact heap_boundary _ (count_positive h)
  · rw [keep .x6 (by decide),lv.source];congr 2;unfold groupBase;omega
  · rw [keep .x7 (by decide),lv.target];congr 1;unfold groupBase;omega

theorem stage_charge (h : Low) (s : MachineState) (lv : Level h s) :
    Charge s (stage h s) (stageSteps h) (stageCycles h) (64*groupsN h) := by
  have hc:=header_charge h s lv.pcAt
  have both:=hc.thenDo (f:=fun u=>groups h (groupsN h) u >>= fun t=>pure (ctl t shift))
      (x:=groupsN h*groupSteps h+1) (y:=groupsN h*groupCycles h+1) (z:=64*groupsN h+0) (by
    intro u hu
    rw [support_pure,Set.mem_singleton_iff] at hu;rw [hu]
    have gc:=groups_charge h (groupsN h) (groupsN_pos h) (le_refl _) _ (header_cursor h s lv)
      (header_pc h s lv.pcAt)
    exact gc.thenDo (fun t ht=>shift_charge h t (groups_post h _ (groupsN_pos h) (le_refl _) _ t
      (header_cursor h s lv) (header_pc h s lv.pcAt) ht).2))
  exact (both.ofEq (by rw [pure_bind];rfl)).cast (by unfold stageSteps;omega) (by unfold stageCycles;omega) (by omega)

structure After (h : Low) (t : MachineState) : Prop extends Common t where
  source : t.getReg .x6=heapAddress (2*(count h-1))
  target : t.getReg .x7=heapAddress (count h-1)
  span : t.getReg .x4=W (32*count h) >>> 1
  pcAt : t.pc=pc (tailStart h+4)

theorem stage_post (h : Low) (s t : MachineState) (lv : Level h s) (ht : t∈support (stage h s)) : After h t := by
  simp only [stage,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at ht
  obtain ⟨u,hu,rfl⟩:=ht
  have gp:=groups_post h _ (groupsN_pos h) (le_refl _) _ u (header_cursor h s lv) (header_pc h s lv.pcAt) hu
  have c:=gp.1
  have keep (r : Reg) (hr : r≠.x4) := shift_reg u r hr
  have m:=getMem_of_mem (shift_mem u)
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [keep .x8 (by decide)];exact c.output
  · rw [keep .x9 (by decide)];exact c.heap
  · rw [keep .x5 (by decide)];exact c.selector
  · rw [keep .x11 (by decide)];exact c.length
  · rw [keep .x13 (by decide)];exact c.kind
  · rw [m];exact c.z0
  · rw [m];exact c.z1
  · rw [m];exact c.flag
  · rw [keep .x6 (by decide),c.source];congr 2 <;> unfold groupBase <;> omega
  · rw [keep .x7 (by decide),c.target];congr 1 <;> unfold groupBase <;> omega
  · rw [shift_value,c.span]
  · rw [shift_pc,gp.2];exact word_pc _

theorem span_next : ∀ h : Low, (h7:h.val<7) → W (32*count h) >>> 1=W (32*count ⟨h.val+1,by omega⟩) := by
  decide +kernel

theorem After.next {h : Low} {t : MachineState} (a : After h t) (h7 : h.val<7) :
    Level ⟨h.val+1,by omega⟩ t := by
  have cn:=count_next h h7
  refine ⟨a.toCommon,?_,?_,?_,?_⟩
  · rw [a.source];congr 1;omega
  · rw [a.target];congr 1;omega
  · rw [a.span,span_next h h7]
  · rw [a.pcAt,next_level h h7]

structure Final (s : MachineState) : Prop extends Common s where
  source : s.getReg .x6=heapAddress (2*(2^16-1))
  target : s.getReg .x7=heapAddress (2^16-1)
  span : s.getReg .x4=W (32*2^15)
  pcAt : s.pc=pc 51098

theorem After.final {t : MachineState} (a : After 7 t) : Final t := by
  have c7 : count 7=2^16 := by decide +kernel
  refine ⟨a.toCommon,?_,?_,?_,?_⟩
  · rw [a.source,c7]
  · rw [a.target,c7]
  · rw [a.span,c7];decide
  · rw [a.pcAt,last_level]

/-! The eight specialized heights. -/

def lowAt (r : Nat) : Low := ⟨(8-r)%8,Nat.mod_lt _ (by decide)⟩

def fast : Nat → MachineState → OracleComp World MachineState
  | 0,s=>pure s
  | r+1,s=>do let t ← stage (lowAt (r+1)) s; fast r t
def fastSteps : Nat → Nat | 0=>0 | r+1=>stageSteps (lowAt (r+1))+fastSteps r
def fastCycles : Nat → Nat | 0=>0 | r+1=>stageCycles (lowAt (r+1))+fastCycles r
def fastCalls : Nat → Nat | 0=>0 | r+1=>64*groupsN (lowAt (r+1))+fastCalls r

theorem fast_zero (s : MachineState) : fast 0 s=pure s := rfl
theorem fast_succ (r : Nat) (s : MachineState) : fast (r+1) s=(stage (lowAt (r+1)) s >>= fast r) := rfl

theorem lowAt_next (r : Nat) (one : 1≤r) (le : r≤7) :
    (⟨(lowAt (r+1)).val+1,by simp [lowAt];omega⟩ : Low)=lowAt r := by
  apply Fin.ext;simp [lowAt];omega
theorem lowAt_one : lowAt 1=7 := rfl

theorem fast_charge : ∀ r, 1≤r → r≤8 → ∀ s, Level (lowAt r) s →
    Charge s (fast r s) (fastSteps r) (fastCycles r) (fastCalls r) := by
  intro r
  induction r with
  | zero => intro one;omega
  | succ r ih =>
    intro _ le s lv
    have first:=stage_charge _ s lv
    have both:=first.thenDo (f:=fast r) (x:=fastSteps r) (y:=fastCycles r) (z:=fastCalls r) (by
      intro t ht
      have a:=stage_post _ s t lv ht
      by_cases r0 : r=0
      · subst r0;rw [fast_zero];exact pure_charge t
      · have lt : (lowAt (r+1)).val<7 := by simp [lowAt];omega
        have nx:=a.next lt
        rw [lowAt_next r (by omega) (by omega)] at nx
        exact ih (by omega) (by omega) t nx)
    exact (both.ofEq (fast_succ r s).symm).cast rfl rfl rfl

theorem fast_post : ∀ r, 1≤r → r≤8 → ∀ s t, Level (lowAt r) s → t∈support (fast r s) → Final t := by
  intro r
  induction r with
  | zero => intro one;omega
  | succ r ih =>
    intro _ le s t lv ht
    rw [fast_succ] at ht;simp only [mem_support_bind_iff] at ht
    obtain ⟨mid,one,rest⟩:=ht
    have a:=stage_post _ s mid lv one
    by_cases r0 : r=0
    · subst r0;rw [fast_zero,support_pure,Set.mem_singleton_iff] at rest;rw [rest]
      exact (show After 7 mid from a).final
    · have lt : (lowAt (r+1)).val<7 := by simp [lowAt];omega
      have nx:=a.next lt
      rw [lowAt_next r (by omega) (by omega)] at nx
      exact ih (by omega) (by omega) mid t nx rest

theorem fast_counted (oracle : Oracle) : ∀ r s, RunPublic oracle (fast r s) (fastCalls r) := by
  have lanesC (h : Low) (G : Nat) : ∀ r s, RunPublic oracle (lanes h G r s) (4*r) := by
    intro r;induction r with
    | zero => intro s;exact run_pure_public ..
    | succ r ih =>
      intro s
      have one : RunPublic oracle (trace (G-(15-r)) (plan h) s) 4 := by
        have:=countedList oracle (G-(15-r)) (plan h) s;rwa [fourCalls] at this
      show RunPublic oracle (trace (G-(15-r)) (plan h) s >>= lanes h G r) (4*(r+1))
      rw [show 4*(r+1)=4+4*r by ring];exact run_bind_public _ _ _ _ _ one (fun t=>ih t)
  have groupsC (h : Low) : ∀ g s, RunPublic oracle (groups h g s) (64*g) := by
    intro g;induction g with
    | zero => intro s;exact run_pure_public ..
    | succ g ih =>
      intro s
      have b:=run_bind_public _ _ _ _ _ (lanesC h (groupBase h (g+1)) 16 s) (fun t=>ih (ctl t (latch h)))
      rw [groups_succ];rwa [show 64*(g+1)=4*16+64*g by ring]
  have stageC (h : Low) (s : MachineState) : RunPublic oracle (stage h s) (64*groupsN h) := by
    have b:=run_bind_public _ _ _ _ _ (groupsC h (groupsN h) (ctl s (header h))) (fun t=>run_pure_public oracle (ctl t shift))
    simpa [stage] using b
  intro r;induction r with
  | zero => intro s;exact run_pure_public ..
  | succ r ih =>
    intro s;rw [fast_succ];exact run_bind_public _ _ _ _ _ (stageC _ s) (fun t=>ih t)

/-! Setup, hand-over and the complete parent phase. -/

theorem tree_heap (n : Nat) : wordAddress (treeWord n)=heapAddress n := by
  unfold wordAddress treeWord heapAddress heapBase;congr 1;omega

theorem setup_level (s : MachineState) (here : s.pc=pc 45688) (entry : FastEntry s)
    (output : s.getReg .x8=4294971392) : Level 0 (ctl s setup) := by
  obtain ⟨⟨src,dst,sel,len,kind,heap⟩,stride⟩:=entry
  have e6 : (ctl s setup).getReg .x6=s.getReg .x10+signExtend12 0 := rfl
  have e7 : (ctl s setup).getReg .x7=s.getReg .x12+signExtend12 0 := rfl
  have e4 : (ctl s setup).getReg .x4=s.getReg .x19 >>> (1:BitVec 6).toNat := rfl
  have z : signExtend12 (0:BitVec 12)=0 := by decide
  have z' : ∀ x : Word, x+(0:Word)=x := fun x=>by simp
  have c0 : count 0=2^23 := by decide +kernel
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · exact output
  · change s.getReg .x9=_;rw [heap,tree_heap];rfl
  · exact sel
  · exact len
  · exact kind
  · rfl
  · rfl
  · have m : (ctl s setup).getMem 280=(0#64+signExtend12 1) <<< (63:BitVec 6).toNat := rfl
    rw [m];decide +kernel
  · rw [e6,z,z',src,tree_heap,c0];congr 1
  · rw [e7,z,z',dst,tree_heap,c0];congr 1
  · rw [e4,stride,c0];decide
  · rw [ctl_linear_pc _ (by decide),here,pc,wordplus];decide +kernel

theorem setup_post_pc (s : MachineState) (here : s.pc=pc 45688) : (ctl s setup).pc=pc (levelStart 0) := by
  rw [ctl_linear_pc _ (by decide),here,pc,wordplus];decide +kernel

theorem handoff_ready (a : MachineState) (f : Final a) :
    HeapLevelReady (ctl a handoff) (heightAt 16) (heightCount (heightAt 16)) := by
  have hc : heightCount (heightAt 16)=2^15 := by decide +kernel
  have keep (r : Reg) (r10 : r≠.x10) (r12 : r≠.x12) := handoff_reg a r r10 r12
  have v:=handoff_values a
  refine ⟨⟨v.1,v.2,?_,?_,?_,by decide,by decide,by decide,by decide⟩,?_,?_,?_,?_,?_,by rw [hc];decide,by rw [hc];decide⟩
  · rw [keep .x5 (by decide) (by decide)];exact f.selector
  · rw [keep .x11 (by decide) (by decide)];exact f.length
  · rw [keep .x13 (by decide) (by decide)];exact f.kind
  · rw [handoff_pc a f.pcAt];decide +kernel
  · rw [keep .x6 (by decide) (by decide),f.source,hc];congr 1
  · rw [keep .x7 (by decide) (by decide),f.target,hc];congr 1
  · rw [keep .x9 (by decide) (by decide),f.heap]
  · rw [keep .x4 (by decide) (by decide),f.span,hc]

def fastParentTrace (s : MachineState) : OracleComp World MachineState := do
  let a ← fast 8 (ctl s setup)
  let b ← parentLevels 16 (ctl a handoff)
  return chainedRootPrefix b 10

def fastParentSteps := 8+fastSteps 8+3+levelsSteps 16+11
def fastParentCycles := 8+fastCycles 8+3+levelsCycles 16+11
def fastParentCalls := fastCalls 8+levelsQueries 16

theorem fast_parent_charge (s : MachineState) (here : s.pc=pc 45688) (entry : FastEntry s)
    (output : s.getReg .x8=4294971392) :
    Charge s (fast 8 (ctl s setup) >>= fun a=>parentLevels 16 (ctl a handoff))
      (8+fastSteps 8+(3+levelsSteps 16)) (8+fastCycles 8+(3+levelsCycles 16)) (fastCalls 8+(0+levelsQueries 16)) := by
  have lv:=setup_level s here entry output
  have sc:=setup_charge s here
  have fc : Charge s (pure (ctl s setup) >>= fast 8) (8+fastSteps 8) (8+fastCycles 8) (0+fastCalls 8) :=
    sc.thenDo (fun u hu=>by
      rw [support_pure,Set.mem_singleton_iff] at hu;rw [hu];exact fast_charge 8 (by decide) le_rfl _ lv)
  have fc' : Charge s (fast 8 (ctl s setup)) (8+fastSteps 8) (8+fastCycles 8) (fastCalls 8) :=
    (fc.ofEq (pure_bind _ _)).cast rfl rfl (by omega)
  exact fc'.thenDo (f:=fun a=>parentLevels 16 (ctl a handoff))
    (x:=3+levelsSteps 16) (y:=3+levelsCycles 16) (z:=0+levelsQueries 16) (by
    intro a ha
    have fin:=fast_post 8 (by decide) le_rfl _ a lv ha
    have hc:=handoff_charge a fin.pcAt
    have lc : Charge (ctl a handoff) (parentLevels 16 (ctl a handoff)) (levelsSteps 16) (levelsCycles 16)
        (levelsQueries 16) :=
      fun fuel coins=>parent_levels_execution 16 (by decide) _ (fun _=>handoff_ready a fin) fuel coins
    have two : Charge a (pure (ctl a handoff) >>= parentLevels 16) (3+levelsSteps 16) (3+levelsCycles 16)
        (0+levelsQueries 16) :=
      hc.thenDo (fun b hb=>by rw [support_pure,Set.mem_singleton_iff] at hb;rw [hb];exact lc)
    exact two.ofEq (pure_bind _ _))

theorem fast_parent_execution (s : MachineState) (here : s.pc=pc 45688) (entry : FastEntry s)
    (output : s.getReg .x8=4294971392) (fuel : Nat) :
    execute chainedCommitImage (fastParentSteps+fuel) s true =
      (do let out ← fastParentTrace s
          return ⟨.success,out,fastParentCycles,fastParentCalls⟩) := by
  have lv:=setup_level s here entry output
  rw [show fastParentSteps+fuel=(8+fastSteps 8+(3+levelsSteps 16))+(11+fuel) by unfold fastParentSteps;omega,
    fast_parent_charge s here entry output (11+fuel) true]
  simp only [fastParentTrace,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro a ha
  have fin:=fast_post 8 (by decide) le_rfl _ a lv ha
  apply bind_congr_of_forall_mem_support
  intro b hb
  have ready:=handoff_ready a fin
  have endpc:=parent_levels_pc 16 (by decide) (by decide) _ b ready hb
  have x9 : b.getReg .x9=4294971424 :=
    (parent_levels_register 16 _ b hb .x9 (by simp [ParentSaved])).trans
      ((handoff_reg a .x9 (by decide) (by decide)).trans fin.heap)
  have x8 : b.getReg .x8=4294971392 :=
    (parent_levels_register 16 _ b hb .x8 (by simp [ParentSaved])).trans
      ((handoff_reg a .x8 (by decide) (by decide)).trans fin.output)
  rw [chained_root_execution b endpc x9 x8 fuel,pure_bind,pure_bind]
  refine congrArg pure ?_
  show (⟨.success,chainedRootPrefix b 10,8+fastCycles 8+(3+levelsCycles 16)+11,
      fastCalls 8+(0+levelsQueries 16)+0⟩ : Execution)=_
  rw [show 8+fastCycles 8+(3+levelsCycles 16)+11=fastParentCycles by unfold fastParentCycles;omega,
    show fastCalls 8+(0+levelsQueries 16)+0=fastParentCalls by unfold fastParentCalls;omega]

end CommitGolfCandidate.Chained.Native.Fast
