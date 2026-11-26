import CommitGolfCandidate.OPBatchMemory
import CommitGolfCandidate.LateOpenRecordHead

/-! A96 batch opening: one 510-byte record (24-byte salt, three 32-byte siblings, thirteen
30-byte siblings) written by the appended code at words 140..264. -/
namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Offset of the level-`l` sibling inside the path part of a batch record. -/
def bOff (l : Nat) := if l ≤ 3 then 32*l else 96+30*(l-3)

theorem bOff_mono (a b : Nat) (h : a≤b) : bOff a ≤ bOff b := by unfold bOff; split_ifs <;> omega

theorem bOff_even (l : Nat) : bOff l % 2 = 0 := by unfold bOff; split_ifs <;> omega

def bPath (tree : Levels) (i : Index) (l n : Nat) : Proof :=
  (List.range' l n).flatMap fun j => batchSibling tree j (mate i j)

theorem bpath_cons (tree : Levels) (i : Index) (l n : Nat) :
    bPath tree i l (n+1) = batchSibling tree l (mate i l) ++ bPath tree i (l+1) n := by
  simp only [bPath,List.range'_succ,List.flatMap_cons]

theorem bpath_append (tree : Levels) (i : Index) (l m n : Nat) :
    bPath tree i l (m+n) = bPath tree i l m ++ bPath tree i (l+m) n := by
  unfold bPath; rw [← List.range'_append]; simp only [Nat.one_mul, List.flatMap_append]

theorem sibling_len (tree : Levels) (l j : Nat) :
    (batchSibling tree l j).length = bOff (l+1) - bOff l := by
  unfold batchSibling bOff; split_ifs <;> simp only [bytes,List.length_ofFn] <;> omega

theorem bpath_len (tree : Levels) (i : Index) (l n : Nat) :
    (bPath tree i l n).length = bOff (l+n) - bOff l := by
  induction n generalizing l with
  | zero => simp [bPath]
  | succ n ih =>
    rw [bpath_cons,List.length_append,sibling_len,ih (l+1)]
    have m1 := bOff_mono l (l+1) (by omega)
    have m2 := bOff_mono (l+1) (l+1+n) (by omega)
    rw [show l+(n+1)=l+1+n by omega]; omega

theorem sibling_source (s : MachineState) (tree : Levels) (l j a : Nat)
    (read : readBuffer s a 32 = node tree l j) : HasBytes s a (batchSibling tree l j) := by
  have full := read_bytes s a 32 _ read
  unfold batchSibling; split
  · exact full
  · exact full.low

inductive Lp where | a | b deriving DecidableEq

def Lp.sib : Lp → Part | .a => .bSibA | .b => .bSibB
def Lp.next : Lp → Part | .a => .bNextA | .b => .bNextB
def Lp.test : Lp → Test | .a => .bMorePathA | .b => .bMorePathB
def Lp.site : Lp → HSite | .a => .pathA | .b => .pathB
def Lp.top : Lp → Nat | .a => 177 | .b => 221
def Lp.exit : Lp → Nat | .a => 220 | .b => 262
def Lp.first : Lp → Nat | .a => 0 | .b => 3
def Lp.stop : Lp → Nat | .a => 3 | .b => 16

theorem Lp.facts (lp : Lp) : lp.sib.start = lp.top ∧ lp.sib.stop = lp.site.pc ∧
    lp.site.pc+2*lp.site.count = lp.next.start ∧ lp.next.stop = lp.test.start ∧
    lp.test.target = lp.top ∧ lp.test.start+1 = lp.exit ∧ lp.sib.reads = [] ∧ lp.next.reads = [] ∧
    lp.sib.cycles = 5 ∧ lp.next.cycles = 5 ∧ lp.sib.stop-lp.sib.start = 5 ∧
    lp.next.stop-lp.next.start = 5 ∧ lp.test.args = (.x28,.x0) ∧ lp.test ≠ .empty := by
  cases lp <;> decide

theorem Lp.width (lp : Lp) (l : Nat) (lo : lp.first ≤ l) (hi : l < lp.stop) :
    2*lp.site.count = bOff (l+1) - bOff l := by
  cases lp <;> simp only [Lp.first,Lp.stop,Lp.site,HSite.count] at * <;> unfold bOff <;> split_ifs <;> omega

theorem Lp.sib_x23 (lp : Lp) : lp.sib.equation .x23 =
    .op .add (.reg .x22) (.op .shl (.op .add (.op .xor (.reg .x20) (.lit 1)) (.op .shr (.reg .x20) (.lit 1))) (.lit 5)) := by
  cases lp <;> rfl

theorem Lp.next_eqs (lp : Lp) :
    lp.next.equation .x25 = .op .add (.reg .x25) (.lit (W (2*lp.site.count))) ∧
    lp.next.equation .x20 = .op .shr (.reg .x20) (.lit 1) ∧
    lp.next.equation .x22 = .op .add (.reg .x22) (.reg .x17) ∧
    lp.next.equation .x17 = .op .shr (.reg .x17) (.lit 1) ∧
    lp.next.equation .x28 = .op .add (.reg .x28) (.lit 18446744073709551615) := by
  cases lp <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩

def bAnchors : List Reg := [.x9,.x16,.x18,.x29,.x24,.x27]
def BKeeps (s t : MachineState) := ∀ reg ∈ bAnchors, t.getReg reg=s.getReg reg

theorem BKeeps.then {s t u : MachineState} (a : BKeeps s t) (b : BKeeps t u) : BKeeps s u :=
  fun r h => (b r h).trans (a r h)

theorem Lp.sib_keeps (lp : Lp) : ∀ r ∈ ([.x25,.x20,.x22,.x17,.x28] ++ bAnchors : List Reg),
    lp.sib.equation r = original r := by
  cases lp <;> decide

theorem Lp.next_keeps (lp : Lp) : ∀ r ∈ bAnchors, lp.next.equation r = original r := by
  cases lp <;> decide

structure BFrame (s : MachineState) (i : Index) (lp : Lp) (l out : Nat) : Prop where
  ptr : s.getReg .x25 = W (out+bOff l)
  idx : s.getReg .x20 = W (indexAbove i l)
  base : s.getReg .x22 = W (layerBase l)
  span : s.getReg .x17 = W (stride l)
  left : s.getReg .x28 = W (lp.stop - l)

def oneB (lp : Lp) (s : MachineState) :=
  lp.test.after (lp.next.after (hcopy lp.site (lp.sib.after s)))

theorem test_mem (b : Test) (s : MachineState) : (b.after s).mem = s.mem := rfl

structure LevelResult (lp : Lp) (s : MachineState) (tree : Levels) (i : Index) (l out : Nat) : Prop where
  run : Runs s (oneB lp s) (11+2*lp.site.count) (11+2*lp.site.count)
  pc : (oneB lp s).pc = pcAt (if l+1 < lp.stop then lp.top else lp.exit)
  frame : BFrame (oneB lp s) i lp (l+1) out
  keeps : BKeeps s (oneB lp s)
  bytes : BWritten s (oneB lp s) (out+bOff l) (batchSibling tree l (mate i l))

theorem one_level (lp : Lp) (s : MachineState) (tree : Levels) (i : Index) (l out : Nat)
    (lo : lp.first ≤ l) (hi : l < lp.stop) (pc : s.pc = pcAt lp.top) (f : BFrame s i lp l out)
    (source : readBuffer s (nodeAddress l (mate i l)) 32 = node tree l (mate i l))
    (high : proofBase ≤ out) (even : out%2=0) (fits : out+486 ≤ MEMORY_BYTES) :
    LevelResult lp s tree i l out := by
  obtain ⟨f1,f2,f3,f4,f5,f6,f7,f8,f9,f10,f11,f12,f13,f14⟩ := lp.facts
  have stopLe : lp.stop ≤ 16 := by cases lp <;> decide
  have firstLe : lp.first ≤ 3 := by cases lp <;> decide
  have wid := lp.width l lo hi
  have cnt : lp.site.count ≤ 16 := by cases lp <;> decide
  let a := lp.sib.after s
  let c := hcopy lp.site a
  let u := lp.next.after c
  have ha := no_load lp.sib s (by rw [f1]; exact pc) f7
  let addr := nodeAddress l (mate i l)
  have pa : a.getReg .x23 = W addr := by
    have e := ha.regs .x23
    rw [Lp.sib_x23] at e
    change _ = s.getReg .x22 + (((s.getReg .x20 ^^^ 1)+(s.getReg .x20 >>> 1)) <<< 5) at e
    rw [f.idx,f.base] at e
    have bound : indexAbove i l < 2^64 := by
      unfold indexAbove; have := i.isLt; change i.val<16777216 at this
      have := Nat.div_le_self i.val (2^l); omega
    exact e.trans (sibling_ptr _ _ bound)
  have keepA (r : Reg) (h : r ∈ ([.x25,.x20,.x22,.x17,.x28] ++ bAnchors : List Reg)) : a.getReg r = s.getReg r :=
    ha.keep r (lp.sib_keeps r h)
  have pd : a.getReg .x25 = W (out+bOff l) := (keepA _ (by decide)).trans f.ptr
  have hb := node_ok l (mate i l) (mate_bound i l (by change l < 24; omega))
  have m1 := bOff_mono (l+1) 16 (by omega)
  have b16 : bOff 16 = 486 := rfl
  have src : HasBytes a addr (batchSibling tree l (mate i l)) :=
    sibling_source a tree l _ addr ((read_congr_mem _ _ _ _ ha.mem).trans source)
  have len : (batchSibling tree l (mate i l)).length = 2*lp.site.count := by rw [sibling_len,wid]
  have hc := hcopy_run lp.site a (ha.pc.trans (by rw [f2])) addr (out+bOff l) pa pd _ len src
    (by have := hb.2.2; omega) (by have := bOff_even l; omega)
    (by have := hb.2.1; unfold indexBase at this; unfold MEMORY_BYTES; omega)
    (by have m0 := bOff_mono l (l+1) (by omega); omega)
    (Or.inl (by have := hb.2.1; unfold indexBase at this; unfold proofBase at high; omega))
  have hu := no_load lp.next c (hc.pc.trans (by rw [f3])) f8
  have keepC (r : Reg) (h : r ∈ ([.x25,.x20,.x22,.x17,.x28] ++ bAnchors : List Reg)) : c.getReg r = s.getReg r :=
    (hc.regs r (by intro e; subst e; revert h; decide)).trans (keepA r h)
  obtain ⟨e25,e20,e22,e17,e28⟩ := lp.next_eqs
  have r25 := hu.regs .x25; rw [e25] at r25
  have r20 := hu.regs .x20; rw [e20] at r20
  have r22 := hu.regs .x22; rw [e22] at r22
  have r17 := hu.regs .x17; rw [e17] at r17
  have r28 := hu.regs .x28; rw [e28] at r28
  change u.getReg .x25 = c.getReg .x25 + W (2*lp.site.count) at r25
  change u.getReg .x20 = c.getReg .x20 >>> 1 at r20
  change u.getReg .x22 = c.getReg .x22 + c.getReg .x17 at r22
  change u.getReg .x17 = c.getReg .x17 >>> 1 at r17
  change u.getReg .x28 = c.getReg .x28 + 18446744073709551615 at r28
  rw [keepC _ (by decide),f.ptr] at r25
  rw [keepC _ (by decide),f.idx] at r20
  rw [keepC _ (by decide),keepC _ (by decide),f.base,f.span] at r22
  rw [keepC _ (by decide),f.span] at r17
  rw [keepC _ (by decide),f.left,W,decrement _ (by omega)] at r28
  have idxBound : indexAbove i l < 2^64 := by
    have h := i.isLt;change i.val < 16777216 at h;unfold indexAbove;have := Nat.div_le_self i.val (2^l);omega
  have spanBound : stride l < 2^64 := by have e:=level_count_le l;change _≤16777216 at e;unfold stride;omega
  have fr : BFrame u i lp (l+1) out := by
    refine ⟨r25.trans ?_,r20.trans ?_,r22.trans ?_,r17.trans ?_,r28.trans ?_⟩
    · exact (BitVec.ofNat_add _ _).symm.trans (congrArg W (by have m0 := bOff_mono l (l+1) (by omega); omega))
    · exact (shr _ 1 idxBound).trans (congrArg W (above_next i l).symm)
    · exact (BitVec.ofNat_add (layerBase l) (stride l)).symm.trans (congrArg W (step_base _ (by change l < 24; omega)))
    · exact (shr _ 1 spanBound).trans (congrArg W (step_stride _ (by change l < 24; omega)))
    · exact congrArg W (by omega)
  have rt := test_run lp.test u (hu.pc.trans (by rw [f4]))
  have taken : lp.test.taken u = decide (l+1 < lp.stop) := by
    unfold Test.taken; rw [if_neg f14, f13]
    change (u.getReg .x28 != (0 : Word)) = _
    rw [fr.left,W,count_test (lp.stop-(l+1)) (by omega)]
    by_cases yes : l+1<lp.stop <;> simp [yes,show (lp.stop-(l+1)≠0) ↔ l+1<lp.stop by omega]
  have keepU : BKeeps s (oneB lp s) := by
    intro r h
    change (u.setPC _).getReg r = _
    rw [MachineState.getReg_setPC, hu.keep r (lp.next_keeps r h)]
    exact keepC r (List.mem_append_right _ h)
  refine ⟨?_,?_,?_,keepU,?_⟩
  · have run := ((ha.runs.trans hc.run).trans hu.runs).trans rt
    rw [f11,f12,f9,f10,show 5+2*lp.site.count+5+1 = 11+2*lp.site.count by omega] at run
    exact run
  · change pcAt (if lp.test.taken u then _ else _) = _
    rw [taken]; by_cases more : l+1 < lp.stop
    · simp [more,f5]
    · simp [more]; rw [f6]
  · exact ⟨MachineState.getReg_setPC.trans fr.ptr,MachineState.getReg_setPC.trans fr.idx,
      MachineState.getReg_setPC.trans fr.base,MachineState.getReg_setPC.trans fr.span,
      MachineState.getReg_setPC.trans fr.left⟩
  · exact hc.data.congr_mem ha.mem.symm hu.mem

def bWalk (lp : Lp) : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => bWalk lp n (oneB lp s)

structure WalkB (lp : Lp) (s : MachineState) (tree : Levels) (i : Index) (l out n : Nat) : Prop where
  run : Runs s (bWalk lp n s) ((11+2*lp.site.count)*n) ((11+2*lp.site.count)*n)
  pc : (bWalk lp n s).pc = pcAt (if l+n < lp.stop then lp.top else lp.exit)
  frame : BFrame (bWalk lp n s) i lp (l+n) out
  keeps : BKeeps s (bWalk lp n s)
  bytes : BWritten s (bWalk lp n s) (out+bOff l) (bPath tree i l n)

theorem walk_levels (lp : Lp) (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index)
    (i : Index) (l out n : Nat) (lo : lp.first ≤ l) (h : l+n ≤ lp.stop)
    (pc : s.pc = pcAt (if l < lp.stop then lp.top else lp.exit)) (f : BFrame s i lp l out)
    (src : Sources s xs tree salts) (size : xs.length ≤ LENGTH)
    (high : proofBase ≤ out) (even : out%2=0) (fits : out+486 ≤ MEMORY_BYTES) :
    WalkB lp s tree i l out n := by
  induction n generalizing l s with
  | zero => exact ⟨Runs.refl s,by simpa only [bWalk,Nat.add_zero] using pc,f,fun _ _ => rfl,BWritten.empty s _⟩
  | succ n ih =>
    have lt : l<lp.stop := by omega
    rw [if_pos lt] at pc
    have stopLe : lp.stop ≤ 16 := by cases lp <;> decide
    have one := one_level lp s tree i l out lo lt pc f (src.node l (by change l ≤ 24; omega) _
      (mate_bound i l (by change l < 24; omega))) high even fits
    have valid := src.afterB size _ _ one.bytes.outside (by omega)
    have tail := ih (oneB lp s) (l+1) (by omega) (by omega) one.pc one.frame valid
    have sumEq : l+1+n=l+(n+1) := by omega
    have m0 := bOff_mono l (l+1) (by omega)
    have m1 := bOff_mono (l+1) 16 (by omega)
    have nxt : out+bOff l+(batchSibling tree l (mate i l)).length = out+bOff (l+1) := by
      rw [sibling_len]; omega
    refine ⟨?_,by simpa only [bWalk,sumEq] using tail.pc,by simpa only [bWalk,sumEq] using tail.frame,
      one.keeps.then tail.keeps,?_⟩
    · have r := one.run.trans tail.run
      rw [Nat.mul_succ, Nat.add_comm ((11+2*lp.site.count)*n)]; exact r
    · rw [bpath_cons]
      exact one.bytes.append (nxt.symm ▸ tail.bytes) (by rw [nxt]; unfold bOff at *; split_ifs at * <;> omega)

/-! ### A whole record -/

def bRecAddr (r : Nat) := proofBase+510*r

structure BAnchor (s : MachineState) (r : Nat) : Prop where
  base : s.getReg .x9=W tdBase
  count : s.getReg .x16=W 128
  row : s.getReg .x18=W rowBase
  span : s.getReg .x29=W (stride 0)
  cursor : s.getReg .x24=W (indexBase+8*r)
  left : s.getReg .x27=W (128-r)
  dest : s.getReg .x25=W (bRecAddr r)

def recordB (s : MachineState) :=
  Test.bMoreRecords.after (Part.bRecordNext.after (bWalk .b 13 (Part.bMid.after
    (bWalk .a 3 (Part.bPathStart.after (hcopy .salt (Part.bSalt.after s)))))))

structure RecordBResult (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (r : Nat) : Prop where
  run : Runs s (recordB s) 703 703
  pc : (recordB s).pc = pcAt (if r+1 < 128 then 140 else 265)
  anchor : BAnchor (recordB s) (r+1)
  bytes : BWritten s (recordB s) (bRecAddr r) (batchRecord tree salts (ix xs r))

theorem keeps_anchor {s t : MachineState} {r : Nat} (a : BAnchor s r) (k : BKeeps s t)
    (d : t.getReg .x25 = W (bRecAddr r)) : BAnchor t r :=
  ⟨(k _ (by decide)).trans a.base,(k _ (by decide)).trans a.count,(k _ (by decide)).trans a.row,
    (k _ (by decide)).trans a.span,(k _ (by decide)).trans a.cursor,(k _ (by decide)).trans a.left,d⟩

theorem batch_record_split (tree : Levels) (salts : SaltTape) (i : Index) :
    batchRecord tree salts i = bytes (n:=24) (salts i) ++ (bPath tree i 0 3 ++ bPath tree i 3 13) := by
  rw [← bpath_append]
  simp only [batchRecord,bPath,mate,indexAbove,List.range_eq_range']

set_option maxRecDepth 20000 in
theorem record_b (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index) (r : Nat)
    (pc : s.pc = pcAt 140) (anchor : BAnchor s r) (present : r < xs.length) (card : xs.length = 128)
    (src : Sources s xs tree salts) : RecordBResult s tree salts xs r := by
  let i := ix xs r
  let dst := bRecAddr r
  have size : xs.length ≤ LENGTH := by rw [card]; decide
  have rb : r < 128 := by omega
  have fits : dst + 510 ≤ MEMORY_BYTES := by
    dsimp only [dst,bRecAddr]; unfold proofBase MEMORY_BYTES; omega
  have high : proofBase ≤ dst := by dsimp only [dst,bRecAddr]; omega
  have deven : dst % 2 = 0 := by dsimp only [dst,bRecAddr]; unfold proofBase; omega
  -- salt source
  let a := Part.bSalt.after s
  have loadAddr : accessValid (s.getReg .x24) 8=true := by
    rw [anchor.cursor];apply access_at <;> simp only [indexBase,MEMORY_BYTES] <;> omega
  have first := block_result .bSalt s pc (by
    intro e he
    change e ∈ [_] at he
    rcases List.mem_singleton.mp he with rfl
    change accessValid (s.getReg .x24+0) 8=true
    rw [word_zero];exact loadAddr)
  have loaded : s.getMem (s.getReg .x24) = W i.val := by rw [anchor.cursor];exact src.index _ present
  have id : a.getReg .x20=W i.val := by
    have eq := first.regs .x20
    change _ = s.getMem (s.getReg .x24+0) at eq
    exact eq.trans ((congrArg s.getMem (word_zero _)).trans loaded)
  have ptr : a.getReg .x23 = W (saltAddress i) := by
    have eq := first.regs .x23
    change _ = s.getReg .x18 + (((s.getMem (s.getReg .x24+0) <<< 1) + s.getMem (s.getReg .x24+0)) <<< 5) +
      (((s.getMem (s.getReg .x24+0) &&& 1) + 18446744073709551615) &&& 72) at eq
    rw [word_zero,loaded,anchor.row] at eq
    exact eq.trans (salt_ptr i)
  have keepS (reg : Reg) (h : reg ∈ ([.x25] ++ bAnchors : List Reg)) : a.getReg reg = s.getReg reg :=
    first.keep reg (by revert h reg; decide)
  have dp : a.getReg .x25 = W dst := (keepS _ (by decide)).trans anchor.dest
  have sb := salt_ok i
  have saltBytes : HasBytes a (saltAddress i) (bytes (n:=24) (salts i)) :=
    read_bytes a _ 24 _ ((read_congr_mem _ _ _ _ first.mem).trans (src.salts i))
  have hs := hcopy_run .salt a first.pc (saltAddress i) dst ptr dp _ (by simp [bytes,HSite.count]) saltBytes
    (by have := sb.2.2; omega) deven
    (by have := sb.2.1; unfold indexBase at this; unfold MEMORY_BYTES; simp only [HSite.count]; omega)
    (by simp only [HSite.count]; omega)
    (Or.inl (by have := sb.2.1; unfold indexBase at this; unfold proofBase at high; simp only [HSite.count]; omega))
  let b := hcopy .salt a
  -- path start
  have hp := no_load .bPathStart b hs.pc rfl
  let c := Part.bPathStart.after b
  have keepB (reg : Reg) (h : reg ∈ ([.x25] ++ bAnchors : List Reg)) : b.getReg reg = s.getReg reg :=
    (hs.regs reg (by intro e; subst e; revert h; decide)).trans (keepS reg h)
  have bx25 : b.getReg .x25 = W dst := (hs.regs _ (by decide)).trans dp
  have bx20 : b.getReg .x20 = W i.val := (hs.regs _ (by decide)).trans id
  have keepC (reg : Reg) (h : reg ∈ bAnchors) : c.getReg reg = s.getReg reg :=
    (hp.keep reg (by revert h reg; decide)).trans (keepB reg (List.mem_append_right _ h))
  have frameA : BFrame c i .a 0 (dst+24) := by
    constructor
    · have eq := hp.regs .x25; change _ = b.getReg .x25+24 at eq
      rw [bx25] at eq; exact eq.trans (BitVec.ofNat_add dst 24).symm
    · rw [show indexAbove i 0 = i.val by simp [indexAbove]]
      exact (hp.keep .x20 rfl).trans bx20
    · have eq := hp.regs .x22; change _ = b.getReg .x9+0 at eq
      rw [word_zero,keepB _ (by decide),anchor.base] at eq; exact eq
    · have eq := hp.regs .x17; change _ = b.getReg .x29+0 at eq
      rw [word_zero,keepB _ (by decide),anchor.span] at eq; exact eq
    · exact hp.regs .x28
  have srcB := src.afterB size _ _ hs.data.outside high
  have srcC := srcB.same_mem hp.mem
  have srcC' : Sources c xs tree salts := srcC
  -- three full levels
  have wa := walk_levels .a c tree salts xs i 0 (dst+24) 3 (by decide) (by decide) (by exact hp.pc)
    frameA srcC' size (by omega) (by omega) (by omega)
  let d := bWalk .a 3 c
  have srcD := srcC'.afterB size _ _ wa.bytes.outside (by omega)
  have hm := no_load .bMid d (by exact wa.pc) rfl
  let e := Part.bMid.after d
  have frameB : BFrame e i .b 3 (dst+24) := by
    have fr := wa.frame
    exact ⟨(hm.keep _ rfl).trans fr.ptr,(hm.keep _ rfl).trans fr.idx,(hm.keep _ rfl).trans fr.base,
      (hm.keep _ rfl).trans fr.span,hm.regs .x28⟩
  have wb := walk_levels .b e tree salts xs i 3 (dst+24) 13 (by decide) (by decide) (by exact hm.pc)
    frameB (srcD.same_mem hm.mem) size (by omega) (by omega) (by omega)
  let f := bWalk .b 13 e
  have hn := no_load .bRecordNext f (by exact wb.pc) rfl
  let g := Part.bRecordNext.after f
  have keepF (reg : Reg) (h : reg ∈ bAnchors) : f.getReg reg = s.getReg reg :=
    (wb.keeps reg h).trans ((hm.keep reg (by revert h reg; decide)).trans ((wa.keeps reg h).trans (keepC reg h)))
  have idx := hn.regs .x24; change g.getReg .x24 = f.getReg .x24+8 at idx
  have rem := hn.regs .x27; change g.getReg .x27 = f.getReg .x27+18446744073709551615 at rem
  rw [keepF _ (by decide),anchor.cursor] at idx
  rw [keepF _ (by decide),anchor.left,W,decrement (128-r) (by omega)] at rem
  have rt := test_run .bMoreRecords g hn.pc
  have taken : Test.bMoreRecords.taken g = decide (r+1<128) := by
    change (g.getReg .x27 != 0)=_
    rw [rem,count_test (128-r-1) (by omega)]
    by_cases yes : r+1<128 <;> simp [yes] <;> omega
  have ptrF : f.getReg .x25 = W (bRecAddr (r+1)) := by
    apply wb.frame.ptr.trans; apply congrArg W
    show dst+24+486 = bRecAddr (r+1)
    simp only [dst, bRecAddr]; omega
  refine ⟨?_,?_,?_,?_⟩
  · have run := (((((((first.runs.trans hs.run).trans hp.runs).trans wa.run).trans hm.runs).trans wb.run).trans hn.runs).trans rt)
    exact run
  · change pcAt (if Test.bMoreRecords.taken g then _ else _) = _
    rw [taken]; by_cases e : r+1<128 <;> simp [e,Test.target,Test.start]
  · have keepG (reg : Reg) (h : reg ∈ [.x9,.x16,.x18,.x29,.x25]) : (recordB s).getReg reg = f.getReg reg :=
      MachineState.getReg_setPC.trans (hn.keep reg (by revert h reg; decide))
    refine ⟨(keepG _ (by decide)).trans ((keepF _ (by decide)).trans anchor.base),
      (keepG _ (by decide)).trans ((keepF _ (by decide)).trans anchor.count),
      (keepG _ (by decide)).trans ((keepF _ (by decide)).trans anchor.row),
      (keepG _ (by decide)).trans ((keepF _ (by decide)).trans anchor.span),
      MachineState.getReg_setPC.trans (idx.trans ?_),MachineState.getReg_setPC.trans (rem.trans ?_),
      (keepG _ (by decide)).trans ptrF⟩
    · exact (BitVec.ofNat_add _ 8).symm.trans (congrArg W (by omega))
    · exact congrArg W (by omega)
  · rw [batch_record_split]
    have lenSalt : (bytes (n:=24) (salts i)).length = 24 := by simp [bytes]
    have l1 : (bPath tree i 0 3).length = 96 := by rw [bpath_len]; rfl
    have pathA : BWritten b d (dst+(bytes (n:=24) (salts i)).length) (bPath tree i 0 3) := by
      rw [lenSalt]; exact wa.bytes.congr_mem hp.mem.symm rfl
    have pathB : BWritten d f (dst+(bytes (n:=24) (salts i)).length+(bPath tree i 0 3).length) (bPath tree i 3 13) := by
      rw [lenSalt,l1]; exact wb.bytes.congr_mem hm.mem.symm rfl
    have whole := hs.data.append (pathA.append pathB (by rw [lenSalt,l1]; omega)) (by rw [lenSalt]; omega)
    have endMem : (Test.bMoreRecords.after g).mem = f.mem := (test_mem _ g).trans hn.mem
    exact whole.congr_mem first.mem.symm endMem

end CommitGolfCandidate.Late.Open
