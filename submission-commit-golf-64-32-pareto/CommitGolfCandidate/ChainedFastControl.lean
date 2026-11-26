import CommitGolfCandidate.ChainedFastFrame
import CommitGolfCandidate.ChainedParentLevels

/-! Straight-line control of the specialized parent phase: setup, height headers, the
group latch, the stride shift and the hand-over jump, with their register effects. -/
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
attribute [local irreducible] execute

def ctl (s : MachineState) (xs : List Instr) := xs.foldl execInstrBr s

theorem ctl_cons (s : MachineState) (a : Instr) (xs : List Instr) :
    ctl s (a::xs) = ctl (execInstrBr s a) xs := rfl

def simple : Instr→Bool
  | .ADDI ..|.SLLI ..|.SRLI ..|.ADD ..|.BNE ..|.JAL ..=>true
  | .SD .x0 _ i=>i==264 || i==272 || i==280
  | _=>false
def linear : Instr→Bool
  | .BNE ..|.JAL ..=>false | op=>simple op
def validCtl : List Instr→Bool
  | []=>true
  | [a]=>simple a
  | a::b::xs=>linear a && validCtl (b::xs)

private theorem linear_simple (a : Instr) (ok:linear a=true) : simple a=true := by
  cases a <;> simp_all [linear]

private theorem simple_step (s : MachineState) (a : Instr) (ok:simple a=true) :
    ordinaryStep s (.base a)=some (execInstrBr s a) ∧ instructionCycles (.base a)=1 := by
  cases a <;> simp [simple] at ok <;> try exact ⟨rfl,rfl⟩
  rename_i src r imm
  cases src <;> simp [simple] at ok
  rcases ok with (h|h)|h <;> subst h <;> refine ⟨?_,rfl⟩
  · change (if accessValid 264 8=true then some _ else none)=some _;rw [if_pos (by decide)]
  · change (if accessValid 272 8=true then some _ else none)=some _;rw [if_pos (by decide)]
  · change (if accessValid 280 8=true then some _ else none)=some _;rw [if_pos (by decide)]

private theorem linear_pc (s : MachineState) (a : Instr) (ok:linear a=true) :
    (execInstrBr s a).pc=s.pc+4 := by
  cases a <;> simp [linear,simple] at ok <;> rfl

def PlainFetch (base : Nat) (xs : List Instr) :=
  ∀ i : Fin xs.length, ∀ s : MachineState, s.pc=pc (base+i.val) → fetch chainedCommitImage s=some (.base xs[i])

theorem ArrayAt.fetch {b xs} (table:ArrayAt b xs) (room:b+xs.length≤233483) : PlainFetch b xs :=
  fun i s p=>fetchAt table room i s p

theorem Charge.cast {s : MachineState} {p : OracleComp World MachineState} {a b c a' b' c' : Nat}
    (x : Charge s p a b c) (ea : a=a') (eb : b=b') (ec : c=c') : Charge s p a' b' c' := by
  subst ea eb ec;exact x

theorem Charge.ofEq {s : MachineState} {p q : OracleComp World MachineState} {a b c : Nat}
    (x : Charge s p a b c) (e : p=q) : Charge s q a b c := by
  subst e;exact x

theorem ctlCharge (s : MachineState) (b : Nat) (xs : List Instr) (pc0:s.pc=pc b)
    (ok:validCtl xs=true) (cells:PlainFetch b xs) : Charge s (pure (ctl s xs)) xs.length xs.length 0 := by
  induction xs generalizing s b with
  | nil => intro fuel coins;simp [ctl,Execution.charge]
  | cons a xs ih =>
    have cell : fetch chainedCommitImage s=some (.base a) := by
      simpa using cells ⟨0,by simp⟩ s (by simpa using pc0)
    have isSimple : simple a=true := by
      cases xs with
      | nil=>exact ok
      | cons a' xs=>exact linear_simple a (Bool.and_eq_true_iff.mp ok).1
    have step:=simple_step s a isSimple
    have first : Charge s (pure (execInstrBr s a)) 1 1 0 := by
      intro fuel coins
      rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ cell step.1,step.2,pure_bind]
    cases xs with
    | nil => simpa [ctl] using first
    | cons a' xs =>
      have check:=Bool.and_eq_true_iff.mp ok
      have next: (execInstrBr s a).pc=pc (b+1) := by rw [linear_pc s a check.1,pc0];exact word_pc _
      have tail:=ih (execInstrBr s a) (b+1) next check.2 (by
        intro i st q
        have got:=cells ⟨i.val+1,by have:=i.isLt;simp at this ⊢;omega⟩ st
          (by rw [q];show pc (b+1+i.val)=pc (b+(i.val+1));congr 1;omega)
        simpa using got)
      have both:=first.thenDo (f:=fun t=>pure (ctl t (a'::xs))) (by
        intro t mem
        simp only [support_pure,Set.mem_singleton_iff] at mem
        subst mem;exact tail)
      refine (both.ofEq (by simp [ctl_cons])).cast ?_ ?_ rfl <;> simp <;> omega

/-! Geometry of the eight specialized heights. -/

def count (h : Low) := heightCount (height h)
def groupBase (h : Low) (g : Nat) := count h-1+16*g
def groupsN (h : Low) := count h/16
def lanePC (h : Low) (j : Nat) := levelStart h+(header h).length+j*nodeSteps h
def latch (h : Low) := (groupTail h).take 3
def shift : List Instr := [.SRLI .x4 .x4 1]

theorem count_value : ∀ h : Low, count h=2^(23-h.val) := by decide +kernel
theorem count_size : ∀ h : Low, 65536≤count h ∧ count h≤2^23 ∧ groupsN h*16=count h := by decide +kernel
theorem count_positive (h : Low) : 0<count h := by have:=(count_size h).1;omega
theorem count_next : ∀ h : Low, (h7:h.val<7) → count ⟨h.val+1,by omega⟩*2=count h := by decide +kernel

theorem node_lane (h : Low) (k : Lane) : nodeStart h k=lanePC h k.val := rfl
theorem tail_lane (h : Low) : tailStart h=lanePC h 16 := by unfold tailStart lanePC;omega
theorem lane_step (h : Low) (j : Nat) : lanePC h j+nodeSteps h=lanePC h (j+1) := by
  unfold lanePC;rw [Nat.add_mul,Nat.one_mul];omega
theorem plan_steps (h : Low) : (plan h).length=nodeSteps h := length_plan h
theorem next_level : ∀ h : Low, (h7:h.val<7) → levelStart ⟨h.val+1,by omega⟩=tailStart h+4 := by
  decide +kernel
theorem last_level : tailStart 7+4=51098 := by decide +kernel
theorem node_steps_small : ∀ h : Low, nodeSteps h≤44 := by decide +kernel

def childMaskW (h : Low) : Word := if h.val=0 then W (2^46-1) else W (2^42-1)

structure Common (s : MachineState) : Prop where
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=W heapBase
  selector : s.getReg .x5=0
  length : s.getReg .x11=64
  kind : s.getReg .x13=0
  z0 : s.getMem 264=0
  z1 : s.getMem 272=0
  flag : s.getMem 280=(2^63:Word)

structure Level (h : Low) (s : MachineState) : Prop extends Common s where
  source : s.getReg .x6=heapAddress (4*count h-2)
  target : s.getReg .x7=heapAddress (2*count h-1)
  span : s.getReg .x4=W (32*count h)
  pcAt : s.pc=pc (levelStart h)

structure Band (h : Low) (s : MachineState) : Prop extends Common s where
  span : s.getReg .x4=W (32*count h)
  stop : s.getReg .x14=heapAddress (count h-1)
  ht : s.getReg .x16=W h.val <<< 28
  tag0 : s.getReg .x17=W (7*h.val)
  tag1 : s.getReg .x18=W (7*h.val+1)
  tag2 : s.getReg .x19=W (7*h.val+2)
  childMaskReg : s.getReg .x3=childMaskW h
  parentMaskReg : h.val=7 → s.getReg .x15=W (2^42-1)

def bandRegs : List Reg := [.x3,.x4,.x5,.x8,.x9,.x11,.x13,.x14,.x15,.x16,.x17,.x18,.x19]
theorem band_saved : ∀ r∈bandRegs,r∈saved := by decide

/-- A state that agrees with `s` on the registers and words a band depends on keeps the band. -/
theorem Band.transfer {h : Low} {s t : MachineState} (b : Band h s)
    (regs : ∀ r∈bandRegs,t.getReg r=s.getReg r)
    (m264 : t.getMem 264=s.getMem 264) (m272 : t.getMem 272=s.getMem 272)
    (m280 : t.getMem 280=s.getMem 280) : Band h t := by
  have g:=fun r (hr:r∈bandRegs)=>regs r hr
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [g .x8 (by decide)];exact b.output
  · rw [g .x9 (by decide)];exact b.heap
  · rw [g .x5 (by decide)];exact b.selector
  · rw [g .x11 (by decide)];exact b.length
  · rw [g .x13 (by decide)];exact b.kind
  · rw [m264];exact b.z0
  · rw [m272];exact b.z1
  · rw [m280];exact b.flag
  · rw [g .x4 (by decide)];exact b.span
  · rw [g .x14 (by decide)];exact b.stop
  · rw [g .x16 (by decide)];exact b.ht
  · rw [g .x17 (by decide)];exact b.tag0
  · rw [g .x18 (by decide)];exact b.tag1
  · rw [g .x19 (by decide)];exact b.tag2
  · rw [g .x3 (by decide)];exact b.childMaskReg
  · intro n;rw [g .x15 (by decide)];exact b.parentMaskReg n

/-! Register and memory effects of the control lists, computed per height. -/

def latchOff (h : Low) : BitVec 13 := BitVec.ofNat 13 (8192-4*(16*nodeSteps h+2))
def latchHead : List Instr := [.ADDI .x6 .x6 3072,.ADDI .x7 .x7 3584]
theorem latch_eq (h : Low) : latch h=latchHead++[.BNE .x7 .x14 (latchOff h)] := rfl
attribute [local irreducible] latchOff
theorem ctl_one (s : MachineState) (a : Instr) : ctl s [a]=execInstrBr s a := rfl
theorem ctl_append (s : MachineState) (xs ys : List Instr) : ctl s (xs++ys)=ctl (ctl s xs) ys := by
  simp only [ctl,List.foldl_append]
theorem latch_split (h : Low) (s : MachineState) :
    ctl s (latch h)=execInstrBr (ctl s latchHead) (.BNE .x7 .x14 (latchOff h)) := by
  rw [latch_eq,ctl_append,ctl_one]

theorem bne_mem (s : MachineState) (a b : Reg) (o : BitVec 13) : (execInstrBr s (.BNE a b o)).mem=s.mem := by
  simp only [execInstrBr];split <;> rfl
theorem bne_reg (s : MachineState) (a b : Reg) (o : BitVec 13) (r : Reg) :
    (execInstrBr s (.BNE a b o)).getReg r=s.getReg r := by
  simp only [execInstrBr];split <;> simp
theorem bne_pc (s : MachineState) (a b : Reg) (o : BitVec 13) :
    (execInstrBr s (.BNE a b o)).pc=if s.getReg a=s.getReg b then s.pc+4 else s.pc+signExtend13 o := by
  simp only [execInstrBr];by_cases c : s.getReg a=s.getReg b <;> simp [c,MachineState.setPC]

theorem ctl_linear_pc (xs : List Instr) (ok : xs.all linear=true) (t : MachineState) :
    (ctl t xs).pc=t.pc+W (4*xs.length) := by
  induction xs generalizing t with
  | nil => simp [ctl]
  | cons a xs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    rw [ctl_cons,ih ok.2,linear_pc _ _ ok.1,show (4:Word)=W 4 from rfl,BitVec.add_assoc,wordplus]
    congr 2;simp;omega

theorem header_mem (h : Low) (s : MachineState) : (ctl s (header h)).mem=s.mem := by fin_cases h <;> rfl
theorem latch_mem (h : Low) (s : MachineState) : (ctl s (latch h)).mem=s.mem := by
  rw [latch_split,bne_mem];rfl
theorem shift_mem (s : MachineState) : (ctl s shift).mem=s.mem := rfl
theorem handoff_mem (s : MachineState) : (ctl s handoff).mem=s.mem := rfl

theorem getMem_of_mem {s t : MachineState} (e : t.mem=s.mem) (a : Word) : t.getMem a=s.getMem a := by
  simp [MachineState.getMem,e]

theorem header_reg (h : Low) (s : MachineState) (r : Reg)
    (keep : r∈([.x4,.x5,.x6,.x7,.x8,.x9,.x11,.x13] : List Reg)) : (ctl s (header h)).getReg r=s.getReg r := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at keep
  rcases keep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> fin_cases h <;> rfl

theorem header_values (h : Low) (s : MachineState) :
    (ctl s (header h)).getReg .x16=W h.val <<< 28 ∧
    (ctl s (header h)).getReg .x17=W (7*h.val) ∧
    (ctl s (header h)).getReg .x18=W (7*h.val+1) ∧
    (ctl s (header h)).getReg .x19=W (7*h.val+2) ∧
    (ctl s (header h)).getReg .x14=s.getReg .x9+s.getReg .x4+signExtend12 4064 := by
  fin_cases h <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem header_masks (h : Low) (s : MachineState) :
    (ctl s (header h)).getReg .x3=childMaskW h ∧
    (h.val=7 → (ctl s (header h)).getReg .x15=W (2^42-1)) := by
  have m : (0#64+signExtend12 (4095#12)) >>> (22:BitVec 6).toNat=W (2^42-1) := by decide
  have m0 : (0#64+signExtend12 (4095#12)) >>> (18:BitVec 6).toNat=W (2^46-1) := by decide
  constructor
  · by_cases h0 : h.val=0
    · have e : (ctl s (header h)).getReg .x3=(0#64+signExtend12 (4095#12)) >>> (18:BitVec 6).toNat := by
        fin_cases h <;> first | exact absurd h0 (by decide) | rfl
      rw [e,m0,childMaskW,if_pos h0]
    · have e : (ctl s (header h)).getReg .x3=(0#64+signExtend12 (4095#12)) >>> (22:BitVec 6).toNat := by
        fin_cases h <;> first | exact absurd rfl h0 | rfl
      rw [e,m,childMaskW,if_neg h0]
  · intro c
    have e : (ctl s (header h)).getReg .x15=(0#64+signExtend12 (4095#12)) >>> (22:BitVec 6).toNat := by
      fin_cases h <;> first | exact absurd c (by decide) | rfl
    rw [e,m]

theorem header_pc (h : Low) (s : MachineState) (here : s.pc=pc (levelStart h)) :
    (ctl s (header h)).pc=pc (lanePC h 0) := by
  rw [ctl_linear_pc _ ((show ∀ j : Low, (header j).all linear=true by decide +kernel) h),here,pc,wordplus]
  unfold lanePC pc;congr 1;omega

theorem latch_reg (h : Low) (s : MachineState) (r : Reg) (r6 : r≠.x6) (r7 : r≠.x7) :
    (ctl s (latch h)).getReg r=s.getReg r := by
  rw [latch_split,bne_reg]
  cases r <;> first | exact absurd rfl r6 | exact absurd rfl r7 | rfl

theorem latch_values (h : Low) (s : MachineState) :
    (ctl s (latch h)).getReg .x6=s.getReg .x6+signExtend12 3072 ∧
    (ctl s (latch h)).getReg .x7=s.getReg .x7+signExtend12 3584 := by
  rw [latch_split,bne_reg,bne_reg];exact ⟨rfl,rfl⟩

theorem latch_pc (h : Low) (s : MachineState) :
    (ctl s (latch h)).pc=if s.getReg .x7+signExtend12 3584=s.getReg .x14 then s.pc+4+4+4
      else s.pc+4+4+signExtend13 (latchOff h) := by
  have x7 : (ctl s latchHead).getReg .x7=s.getReg .x7+signExtend12 3584 := rfl
  have x14 : (ctl s latchHead).getReg .x14=s.getReg .x14 := rfl
  have p : (ctl s latchHead).pc=s.pc+4+4 := rfl
  rw [latch_split,bne_pc,x7,x14,p]

theorem shift_reg (s : MachineState) (r : Reg) (r4 : r≠.x4) : (ctl s shift).getReg r=s.getReg r := by
  cases r <;> first | exact absurd rfl r4 | rfl
theorem shift_value (s : MachineState) : (ctl s shift).getReg .x4=s.getReg .x4 >>> 1 := rfl
theorem shift_pc (s : MachineState) : (ctl s shift).pc=s.pc+4 := rfl

theorem handoff_reg (s : MachineState) (r : Reg) (r10 : r≠.x10) (r12 : r≠.x12) :
    (ctl s handoff).getReg r=s.getReg r := by
  cases r <;> first | exact absurd rfl r10 | exact absurd rfl r12 | rfl
theorem handoff_values (s : MachineState) :
    (ctl s handoff).getReg .x10=256 ∧ (ctl s handoff).getReg .x12=256 := ⟨rfl,rfl⟩
theorem handoff_pc (s : MachineState) (here : s.pc=pc 51098) : (ctl s handoff).pc=pc 45298 := by
  change s.pc+4+4+signExtend21 (BitVec.ofInt 21 (4*((45298:Int)-51100)))=_
  rw [here];decide

theorem setup_charge (s : MachineState) (here : s.pc=pc 45688) : Charge s (pure (ctl s setup)) 8 8 0 :=
  ctlCharge s 45688 setup here (by decide) (init_code.fetch (by decide))
theorem header_charge (h : Low) (s : MachineState) (here : s.pc=pc (levelStart h)) :
    Charge s (pure (ctl s (header h))) (header h).length (header h).length 0 :=
  ctlCharge s _ _ here ((show ∀ j : Low, validCtl (header j)=true by decide +kernel) h)
    ((headers h).fetch ((show ∀ j : Low, levelStart j+(header j).length≤233483 by decide +kernel) h))

private theorem array_take {b : Nat} {xs : List Instr} (t : ArrayAt b xs) (n : Nat) : ArrayAt b (xs.take n) := by
  intro i
  have lt : i.val<xs.length := by have:=i.isLt;simp at this;omega
  have got:=t ⟨i.val,lt⟩
  simpa [List.getElem_take] using got

private theorem array_drop {b : Nat} {xs : List Instr} (t : ArrayAt b xs) (n : Nat) (hn : n≤xs.length) :
    ArrayAt (b+n) (xs.drop n) := by
  intro i
  have lt : n+i.val<xs.length := by have:=i.isLt;simp at this;omega
  have got:=t ⟨n+i.val,lt⟩
  simpa [List.getElem_drop,Nat.add_assoc] using got

theorem latch_charge (h : Low) (s : MachineState) (here : s.pc=pc (tailStart h)) :
    Charge s (pure (ctl s (latch h))) 3 3 0 :=
  (ctlCharge s _ _ here ((show ∀ j : Low, validCtl (latch j)=true by decide +kernel) h)
    ((array_take (tails h) 3).fetch ((show ∀ j : Low, tailStart j+(latch j).length≤233483 by decide +kernel) h))).cast
    ((show ∀ j : Low, (latch j).length=3 by decide +kernel) h) ((show ∀ j : Low, (latch j).length=3 by decide +kernel) h) rfl

theorem shift_charge (h : Low) (s : MachineState) (here : s.pc=pc (tailStart h+3)) :
    Charge s (pure (ctl s shift)) 1 1 0 := by
  have tbl : ArrayAt (tailStart h+3) shift := by
    have d:=array_drop (tails h) 3 ((show ∀ j : Low, 3≤(groupTail j).length by decide +kernel) h)
    have e : (groupTail h).drop 3=shift := by fin_cases h <;> rfl
    rwa [e] at d
  exact ctlCharge s _ _ here (by decide) (tbl.fetch ((show ∀ j : Low, tailStart j+3+1≤233483 by decide +kernel) h))

theorem handoff_charge (s : MachineState) (here : s.pc=pc 51098) : Charge s (pure (ctl s handoff)) 3 3 0 :=
  ctlCharge s 51098 handoff here (by decide) (end_code.fetch (by decide))

end CommitGolfCandidate.Chained.Native.Fast
