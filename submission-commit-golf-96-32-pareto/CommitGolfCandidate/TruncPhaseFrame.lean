import CommitGolfCandidate.TruncChunkBytes
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 180000

def cursor (b : Bool) (k : Nat) := if b then 128-k else k
def ordinal (b : Bool) (k : Nat) := if b then 127-k else k
structure Cursors (b f : Bool) (k : Nat) (s : MachineState) : Prop where
  src : s.getReg .x18=BitVec.ofNat 64 (base+sourceStart b f (cursor b k))
  dst : s.getReg .x19=BitVec.ofNat 64 (base+destStart b f (cursor b k))
  count : s.getReg .x28=BitVec.ofNat 64 (128-k)
  pc : s.pc=if k=128 then loc (rowPC b f+(sequence b f).length+4) else loc (rowPC b f)

theorem cursor_before (b : Bool) (k : Nat) (h : k<128) : cursor b k = if b then ordinal b k+1 else ordinal b k := by
  cases b <;> simp [cursor,ordinal] <;> omega
theorem cursor_after (b : Bool) (k : Nat) (h : k<128) : cursor b (k+1) = if b then ordinal b k else ordinal b k+1 := by
  cases b <;> simp [cursor,ordinal] <;> omega

private theorem beforePointer (f : Bool) (k : Nat) (h : k<128) (table : Bool) :
    let start:=if table then sourceStart true f else destStart true f
    let w:=if table then srcWidth true f else dstWidth true f
    BitVec.ofNat 64 (base+start (cursor true k))-BitVec.ofNat 64 w =
      BitVec.ofNat 64 (base+start (ordinal true k)) := by
  cases table <;> cases f <;>
    simp only [cursor,ordinal,srcWidth,dstWidth,sourceStart,destStart,wide,short,sBase,wBase,Bool.false_eq_true,ite_false,ite_true] <;>
    rw [BitVec.ofNat_sub_ofNat_of_le (w:=64) _ _ (by omega) (by omega)] <;> congr 1 <;> omega

theorem beforePtrs (b f : Bool) (k : Nat) (hk : k<128) (s : MachineState) (c : Cursors b f k s) :
    (before b f s).getReg .x18=BitVec.ofNat 64 (base+sourceStart b f (ordinal b k)) ∧
    (before b f s).getReg .x19=BitVec.ofNat 64 (base+destStart b f (ordinal b k)) := by
  cases b
  · exact ⟨c.src,c.dst⟩
  · have x : (before true f s).getReg .x18=s.getReg .x18-BitVec.ofNat 64 (srcWidth true f) := rfl
    have y : (before true f s).getReg .x19=s.getReg .x19-BitVec.ofNat 64 (dstWidth true f) := rfl
    rw [x,y,c.src,c.dst];exact ⟨beforePointer f k hk true,beforePointer f k hk false⟩

theorem beforeMem (b f : Bool) (s : MachineState) : (before b f s).mem=s.mem := by cases b <;> rfl

theorem movedMem (b f : Bool) (k : Nat) (hk : k<128) (initial s : MachineState) (c : Cursors b f k s)
    (old : Frame b initial s (destStart b f (cursor b k))) :
    Frame b initial (moved b f s) (destStart b f (cursor b (k+1))) := by
  have hr : ordinal b k<128 := by cases b <;> simp [ordinal] <;> omega
  have pr:=beforePtrs b f k hk s c
  rw [cursor_before b k hk] at old
  rw [cursor_after b k hk]
  exact bodyBytes b f _ hr initial (before b f s) pr.1 pr.2 (frameMem old (beforeMem b f s))

theorem stepBytes (b f : Bool) (k : Nat) (hk : k<128) (initial s : MachineState) (c : Cursors b f k s)
    (old : Frame b initial s (destStart b f (cursor b k))) :
    Frame b initial (regStep b f (loc (rowPC b f)) s) (destStart b f (cursor b (k+1))) := by
  apply frameMem (movedMem b f k hk initial s c old)
  cases b <;> rfl

private theorem beforeCount (b f : Bool) (s : MachineState) : (before b f s).getReg .x28=s.getReg .x28 := by cases b <;> rfl
theorem readyCount (b f : Bool) (s : MachineState) : (ready b f s).getReg .x28=s.getReg .x28 := by
  have keep : (moved b f s).getReg .x28=s.getReg .x28 :=
    (listKept (moves b f) (before b f s) .x28 (by decide)).trans (beforeCount b f s)
  cases b <;> exact keep

theorem remaining (k : Nat) (h : k<128) : BitVec.ofNat 64 (128-k)-1=BitVec.ofNat 64 (128-(k+1)) := by
  rw [show 128-k=(128-(k+1))+1 by omega,BitVec.ofNat_add];exact BitVec.add_sub_cancel _ 1
theorem remainingZero (k : Nat) (h : k<128) : (BitVec.ofNat 64 (128-(k+1))=0#64) ↔ k+1=128 := by
  exact (show ∀ i : Fin 128, (BitVec.ofNat 64 (128-(i.val+1))=0#64) ↔ i.val+1=128 by decide) ⟨k,h⟩

private theorem afterPointer (f : Bool) (k : Nat) (table : Bool) :
    let start:=if table then sourceStart false f else destStart false f
    let w:=if table then srcWidth false f else dstWidth false f
    BitVec.ofNat 64 (base+start k)+BitVec.ofNat 64 w=BitVec.ofNat 64 (base+start (k+1)) := by
  dsimp only;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64)
  cases table <;> cases f <;> simp [sourceStart,destStart,wBase,sBase,srcWidth,dstWidth,wide,short] <;> omega

theorem readyPtrs (b f : Bool) (k : Nat) (hk : k<128) (s : MachineState) (c : Cursors b f k s) :
    (ready b f s).getReg .x18=BitVec.ofNat 64 (base+sourceStart b f (cursor b (k+1))) ∧
    (ready b f s).getReg .x19=BitVec.ofNat 64 (base+destStart b f (cursor b (k+1))) := by
  obtain ⟨a,d⟩:=beforePtrs b f k hk s c
  have x : (moved b f s).getReg .x18=_ := (listKept _ _ .x18 (by decide)).trans a
  have y : (moved b f s).getReg .x19=_ := (listKept _ _ .x19 (by decide)).trans d
  cases b
  · change (moved false f s).getReg .x18+BitVec.ofNat 64 (srcWidth false f)=_ ∧
           (moved false f s).getReg .x19+BitVec.ofNat 64 (dstWidth false f)=_
    rw [x,y];exact ⟨afterPointer f k true,afterPointer f k false⟩
  · rw [cursor_after true k hk];exact ⟨x,y⟩

theorem stepCursors (b f : Bool) (k : Nat) (hk : k<128) (s : MachineState) (c : Cursors b f k s) :
    Cursors b f (k+1) (regStep b f (loc (rowPC b f)) s) := by
  have p:=readyPtrs b f k hk s c
  have cnt := (readyCount b f s).trans c.count
  have ctr : (ready b f s).getReg .x28-1=BitVec.ofNat 64 (128-(k+1)) := (congrArg (fun v : Word=>v-1) cnt).trans (remaining k hk)
  refine ⟨p.1,p.2,ctr,?_⟩
  unfold regStep;dsimp only [MachineState.setPC];rw [ctr]
  have eq0 : (BitVec.ofNat 64 (128-(k+1))=(0:Word)) ↔ k+1=128 := remainingZero k hk
  by_cases last : k+1=128
  · rw [if_pos (eq0.mpr last),if_pos last];unfold loc;rw [←BitVec.ofNat_add];congr 1;omega
  · rw [if_neg (fun z=>last (eq0.mp z)),if_neg last]

theorem allCursors (b f : Bool) (k : Nat) (hk : k≤128) (s : MachineState) (c : Cursors b f 0 s) :
    Cursors b f k ((regStep b f (loc (rowPC b f)))^[k] s) := by
  induction k with
  | zero=>exact c
  | succ k ih=>rw [Function.iterate_succ_apply'];exact stepCursors b f k (by omega) _ (ih (by omega))

theorem allBytes (b f : Bool) (k : Nat) (hk : k≤128) (initial s : MachineState) (c : Cursors b f 0 s)
    (old : Frame b initial s (destStart b f (cursor b 0))) :
    let t:=(regStep b f (loc (rowPC b f)))^[k] s
    Cursors b f k t ∧ Frame b initial t (destStart b f (cursor b k)) := by
  induction k with
  | zero => exact ⟨c,old⟩
  | succ k ih =>
    have cb:=ih (by omega)
    rw [Function.iterate_succ_apply']
    exact ⟨stepCursors _ _ k (by omega) _ cb.1,stepBytes _ _ k (by omega) initial _ cb.1 cb.2⟩
end CommitGolfCandidate.Trunc.Wire
