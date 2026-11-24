import CommitGolfCandidate.ChainedFastControl

/-! Lanes, groups and heights of the specialized parent phase: exact steps, cycles and
public calls, and the register, pc and memory facts each stage leaves behind. -/
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
attribute [local irreducible] execute nodeSteps

/-! Heap address arithmetic. -/

theorem heap_numeric (n : Nat) (small : n<2^25) : (heapAddress n).toNat=heapBase+32*n := by
  unfold heapAddress;rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold heapBase;omega)]

theorem heap_inj {a b : Nat} (ha : a<2^25) (hb : b<2^25) (e : heapAddress a=heapAddress b) : a=b := by
  have n:=congrArg BitVec.toNat e;rw [heap_numeric a ha,heap_numeric b hb] at n;omega

theorem heap_back (m d : Nat) : heapAddress (m+d)+-(W (32*d))=heapAddress m := by
  unfold heapAddress;rw [show heapBase+32*(m+d)=(heapBase+32*m)+32*d by ring,BitVec.ofNat_add,
    BitVec.add_assoc,BitVec.add_right_neg,BitVec.add_zero]

theorem ext3072 : signExtend12 (3072:BitVec 12)=-(W (32*32)) := by decide
theorem ext3584 : signExtend12 (3584:BitVec 12)=-(W (32*16)) := by decide
theorem ext4064 : signExtend12 (4064:BitVec 12)=-(32:Word) := by decide

/-! One lane. -/

structure Cursor (h : Low) (G : Nat) (s : MachineState) : Prop extends Band h s where
  source : s.getReg .x6=heapAddress (2*G)
  target : s.getReg .x7=heapAddress G

theorem lane_tracked {h : Low} {G : Nat} {s : MachineState} (c : Cursor h G s) (k : Lane) (kG : k.val≤G) :
    Tracked (G-k.val) k startRegs s := by
  have sum : G-k.val+k.val=G := Nat.sub_add_cancel kG
  intro r p hit
  cases r <;> simp only [startRegs,reduceCtorEq,Option.some.injEq] at hit <;> subst hit <;>
    simp only [roleValue,sum]
  · exact c.selector
  · exact c.source
  · exact c.target
  · exact c.length
  · exact c.kind

theorem lane_bounds {G : Nat} (k : Lane) (lo : 65536+15≤G) (hi : G<2^24) : Bounds (G-k.val) :=
  ⟨by have:=k.isLt;omega,by omega⟩

theorem safe_word (n : Nat) (q : Nat) (low : 256<q) (high : q<4096) (al : q%8=0) : SafeWord n q := by
  refine ⟨al,by omega,?_⟩
  intro i hi;unfold address heapBase;split_ifs <;> omega

theorem lane_charge (h : Low) (G : Nat) (k : Lane) (lo : 65536+15≤G) (hi : G<2^24) (s : MachineState)
    (c : Cursor h G s) (here : s.pc=pc (lanePC h k.val)) :
    Charge s (trace (G-k.val) (plan h) s) (nodeSteps h) (nodeSteps h+28) 4 := by
  have run:=execList (G-k.val) k (lane_bounds k lo hi) (nodeStart h k) (plan h) startRegs s
    (lane_tracked c k (by have:=k.isLt;omega)) here (checks h) (nodeFetch h k)
  exact run.cast (plan_steps h) (by rw [plan_steps,fourCalls]) (fourCalls h)

theorem lane_post (h : Low) (G : Nat) (k : Lane) (lo : 65536+15≤G) (hi : G<2^24) (s t : MachineState)
    (c : Cursor h G s) (here : s.pc=pc (lanePC h k.val)) (ht : t∈support (trace (G-k.val) (plan h) s)) :
    Cursor h G t ∧ t.pc=pc (lanePC h (k.val+1)) := by
  have b:=lane_bounds k lo hi
  have regs : ∀ r∈saved,t.getReg r=s.getReg r := fun r hr=>nodeReg ht r hr
  have mem (q : Nat) (l : 256<q) (u : q<4096) (al : q%8=0) : t.getMem (W q)=s.getMem (W q) :=
    traceMem _ b q (safe_word _ q l u al) _ s t ht
  refine ⟨⟨c.toBand.transfer (fun r hr=>regs r (band_saved r hr)) (mem 264 (by decide) (by decide) (by decide))
      (mem 272 (by decide) (by decide) (by decide)) (mem 280 (by decide) (by decide) (by decide)),?_,?_⟩,?_⟩
  · rw [regs .x6 (by decide)];exact c.source
  · rw [regs .x7 (by decide)];exact c.target
  · have p:=endPC (G-k.val) k (plan h) startRegs s t (lane_tracked c k (by have:=k.isLt;omega)) (checks h)
      (nodeStart h k) here ht
    rw [p,plan_steps,node_lane,lane_step]

/-- Lanes `16-r` to `15` of the group whose first parent is `G`. -/
def lanes (h : Low) (G : Nat) : Nat → MachineState → OracleComp World MachineState
  | 0,s=>pure s
  | r+1,s=>do let t ← trace (G-(15-r)) (plan h) s; lanes h G r t

theorem pure_charge (s : MachineState) : Charge s (pure s) 0 0 0 := by
  intro fuel coins;simp [Execution.charge]

theorem lanes_charge (h : Low) (G : Nat) (lo : 65536+15≤G) (hi : G<2^24) :
    ∀ r, r≤16 → ∀ s, Cursor h G s → s.pc=pc (lanePC h (16-r)) →
      Charge s (lanes h G r s) (r*nodeSteps h) (r*(nodeSteps h+28)) (4*r) := by
  intro r
  induction r with
  | zero => intro _ s _ _;simpa [lanes] using pure_charge s
  | succ r ih =>
    intro small s c here
    let k : Lane := ⟨15-r,by omega⟩
    have hk : lanePC h k.val=lanePC h (16-(r+1)) := by congr 1 <;> simp [k] <;> omega
    have first:=lane_charge h G k lo hi s c (here.trans (by rw [hk]))
    have both:=first.thenDo (f:=lanes h G r) (by
      intro t ht
      have post:=lane_post h G k lo hi s t c (here.trans (by rw [hk])) ht
      exact ih (by omega) t post.1 (post.2.trans (by congr 2 <;> simp [k] <;> omega)))
    exact (both.ofEq rfl).cast (by rw [Nat.succ_mul];omega) (by rw [Nat.succ_mul];omega) (by omega)

theorem lanes_post (h : Low) (G : Nat) (lo : 65536+15≤G) (hi : G<2^24) :
    ∀ r, r≤16 → ∀ s t, Cursor h G s → s.pc=pc (lanePC h (16-r)) → t∈support (lanes h G r s) →
      Cursor h G t ∧ t.pc=pc (lanePC h 16) := by
  intro r
  induction r with
  | zero =>
    intro _ s t c here ht
    simp only [lanes,support_pure,Set.mem_singleton_iff] at ht;subst ht;exact ⟨c,by simpa using here⟩
  | succ r ih =>
    intro small s t c here ht
    simp only [lanes,mem_support_bind_iff] at ht
    obtain ⟨mid,one,rest⟩:=ht
    let k : Lane := ⟨15-r,by omega⟩
    have post:=lane_post h G k lo hi s mid c (here.trans (by congr 2 <;> simp [k] <;> omega)) one
    exact ih (by omega) mid t post.1 (post.2.trans (by congr 2 <;> simp [k] <;> omega)) rest

/-! Groups of sixteen lanes and the latch. -/

theorem latch_target : ∀ h : Low, pc (tailStart h)+4+4+signExtend13 (latchOff h)=pc (lanePC h 0) := by
  decide +kernel
theorem latch_exit (h : Low) : pc (tailStart h)+4+4+4=pc (tailStart h+3) := by
  show W (4096+4*tailStart h)+W 4+W 4+W 4=W (4096+4*(tailStart h+3))
  rw [wordplus,wordplus,wordplus];exact congrArg W (by omega)

theorem group_bounds (h : Low) (g : Nat) (one : 1≤g) (le : g≤groupsN h) :
    65536+15≤groupBase h g ∧ groupBase h g<2^24 := by
  have := count_size h;unfold groupBase;omega

theorem latch_post (h : Low) (g : Nat) (le : g+1≤groupsN h) (t : MachineState)
    (c : Cursor h (groupBase h (g+1)) t) (here : t.pc=pc (tailStart h)) :
    Cursor h (groupBase h g) (ctl t (latch h)) ∧
      (ctl t (latch h)).pc=(if g=0 then pc (tailStart h+3) else pc (lanePC h 0)) := by
  have sz:=count_size h
  have keep : ∀ r∈bandRegs,(ctl t (latch h)).getReg r=t.getReg r := by
    intro r hr;apply latch_reg <;> (intro e;subst e;simp [bandRegs] at hr)
  have m := getMem_of_mem (latch_mem h t)
  have vals:=latch_values h t
  have x6 : (ctl t (latch h)).getReg .x6=heapAddress (2*groupBase h g) := by
    rw [vals.1,c.source,ext3072,show 2*groupBase h (g+1)=2*groupBase h g+32 by unfold groupBase;omega,heap_back]
  have x7 : (ctl t (latch h)).getReg .x7=heapAddress (groupBase h g) := by
    rw [vals.2,c.target,ext3584,show groupBase h (g+1)=groupBase h g+16 by unfold groupBase;omega,heap_back]
  refine ⟨⟨c.toBand.transfer keep (m _) (m _) (m _),x6,x7⟩,?_⟩
  rw [latch_pc,c.target,c.stop,ext3584,show groupBase h (g+1)=groupBase h g+16 by unfold groupBase;omega,
    heap_back,here]
  by_cases g0 : g=0
  · subst g0;rw [if_pos (by unfold groupBase;simp),if_pos rfl,latch_exit]
  · have ne : heapAddress (groupBase h g)≠heapAddress (count h-1) := by
      intro e;have:=heap_inj (by unfold groupBase;omega) (by omega) e;unfold groupBase at this;omega
    rw [if_neg ne,if_neg g0,latch_target]

def groups (h : Low) : Nat → MachineState → OracleComp World MachineState
  | 0,s=>pure s
  | g+1,s=>do let t ← lanes h (groupBase h (g+1)) 16 s; groups h g (ctl t (latch h))

theorem groups_zero (h : Low) (s : MachineState) : groups h 0 s=pure s := rfl
theorem groups_succ (h : Low) (g : Nat) (s : MachineState) :
    groups h (g+1) s=(lanes h (groupBase h (g+1)) 16 s >>= fun t=>groups h g (ctl t (latch h))) := rfl

def groupSteps (h : Low) := 16*nodeSteps h+3
def groupCycles (h : Low) := 16*(nodeSteps h+28)+3

theorem groups_charge (h : Low) : ∀ g, 1≤g → g≤groupsN h → ∀ s, Cursor h (groupBase h g) s →
    s.pc=pc (lanePC h 0) → Charge s (groups h g s) (g*groupSteps h) (g*groupCycles h) (64*g) := by
  intro g
  induction g with
  | zero => intro one;omega
  | succ g ih =>
    intro _ le s c here
    have bd:=group_bounds h (g+1) (by omega) le
    have first:=lanes_charge h _ bd.1 bd.2 16 (by decide) s c (by simpa using here)
    have both:=first.thenDo (f:=fun t=>groups h g (ctl t (latch h)))
        (x:=3+g*groupSteps h) (y:=3+g*groupCycles h) (z:=0+64*g) (by
      intro t ht
      have post:=lanes_post h _ bd.1 bd.2 16 (by decide) s t c (by simpa using here) ht
      have tl:=post.2.trans (congrArg pc (tail_lane h).symm)
      have lt:=latch_post h g le t post.1 tl
      have lc:=latch_charge h t tl
      have next : Charge (ctl t (latch h)) (groups h g (ctl t (latch h))) (g*groupSteps h) (g*groupCycles h) (64*g) := by
        by_cases g0 : g=0
        · subst g0;rw [groups_zero];exact (pure_charge _).cast (Nat.zero_mul _).symm (Nat.zero_mul _).symm rfl
        · exact ih (by omega) (by omega) _ lt.1 (by rw [lt.2,if_neg g0])
      have two : Charge t (pure (ctl t (latch h)) >>= groups h g) (3+g*groupSteps h) (3+g*groupCycles h)
          (0+64*g) := lc.thenDo (fun u hu=>by
        rw [support_pure,Set.mem_singleton_iff] at hu;rw [hu];exact next)
      exact two.ofEq (pure_bind _ _))
    exact (both.ofEq (groups_succ h g s).symm).cast (by unfold groupSteps;ring)
      (by unfold groupCycles;ring) (by omega)

theorem groups_post (h : Low) : ∀ g, 1≤g → g≤groupsN h → ∀ s t, Cursor h (groupBase h g) s →
    s.pc=pc (lanePC h 0) → t∈support (groups h g s) →
      Cursor h (groupBase h 0) t ∧ t.pc=pc (tailStart h+3) := by
  intro g
  induction g with
  | zero => intro one;omega
  | succ g ih =>
    intro _ le s t c here ht
    have bd:=group_bounds h (g+1) (by omega) le
    rw [groups_succ] at ht;simp only [mem_support_bind_iff] at ht
    obtain ⟨mid,one,rest⟩:=ht
    have post:=lanes_post h _ bd.1 bd.2 16 (by decide) s mid c (by simpa using here) one
    have lt:=latch_post h g le mid post.1 (post.2.trans (congrArg pc (tail_lane h).symm))
    by_cases g0 : g=0
    · subst g0;rw [groups_zero,support_pure] at rest
      rw [Set.mem_singleton_iff.mp rest];exact ⟨lt.1,by rw [lt.2,if_pos rfl]⟩
    · exact ih (by omega) (by omega) _ t lt.1 (by rw [lt.2,if_neg g0]) rest

end CommitGolfCandidate.Chained.Native.Fast
