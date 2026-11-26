import CommitGolfCandidate.LateOpenControl
import CommitGolfCandidate.LateOpenSources
import CommitGolfCandidate.LateOpenWrites

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def W (n : Nat) := BitVec.ofNat 64 n
def layerBase (l : Nat) := tdBase+levelOffset l
def stride (l : Nat) := 48*levelCount l
def indexAbove (i : Index) (l : Nat) := i.val/2^l
def mate (i : Index) (l : Nat) := indexAbove i l ^^^ 1

theorem above_bound (i : Index) (l : Nat) (le : l≤LOG_LENGTH) : indexAbove i l < levelCount l := by
  have power : levelCount l * 2^l = LENGTH := by
    unfold levelCount LENGTH; rw [←Nat.pow_add, Nat.sub_add_cancel le]
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^l)).mpr
  exact power.symm ▸ i.isLt

theorem mate_bound (i : Index) (l : Nat) (lt : l<LOG_LENGTH) : mate i l < levelCount l := by
  have one : 1 < 2^(LOG_LENGTH-l) := Nat.one_lt_pow (by omega) (by decide)
  exact Nat.xor_lt_two_pow (above_bound _ _ (by omega)) one

theorem above_next (i : Index) (l : Nat) : indexAbove i (l+1) = indexAbove i l/2 := by
  unfold indexAbove;rw [Nat.div_div_eq_div_mul,Nat.pow_succ]

theorem step_base (l : Nat) (lt : l<LOG_LENGTH) : layerBase l+stride l=layerBase (l+1) := by
  have s := level_successor l lt;unfold layerBase stride;rw [level_adjacent l lt];omega

theorem step_stride (l : Nat) (lt : l<LOG_LENGTH) : stride l/2=stride (l+1) := by
  have s := level_successor l lt; unfold stride;omega

def pathBytes (tree : Levels) (i : Index) (l n : Nat) : Proof :=
  (List.range' l n).flatMap fun j => bytes (n:=32) (node tree j (mate i j))

theorem path_cons (tree : Levels) (i : Index) (l n : Nat) :
    pathBytes tree i l (n+1) = bytes (n:=32) (node tree l (mate i l)) ++ pathBytes tree i (l+1) n := by
  simp only [pathBytes,List.range'_succ,List.flatMap_cons]

theorem path_len (tree : Levels) (i : Index) (l n : Nat) : (pathBytes tree i l n).length=32*n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => rw [path_cons,List.length_append,ih];simp [bytes];omega

theorem record_eq (t : Levels) (s : SaltTape) (d : Nat) (i : Index) :
    record t s d i = bytes (n:=24) (s i) ++ pathBytes t i 0 d := by
  simp only [record,pathBytes,mate,indexAbove,List.range_eq_range']

structure Fixed (s : MachineState) (k d : Nat) : Prop where
  base : s.getReg .x9=W tdBase
  count : s.getReg .x16=W k
  row : s.getReg .x18=W rowBase
  span : s.getReg .x29=W (stride 0)
  depth : s.getReg .x30=W d

structure Anchor (s : MachineState) (k d r : Nat) extends Fixed s k d : Prop where
  cursor : s.getReg .x24=W (indexBase+8*r)
  left : s.getReg .x27=W (k-r)

def anchors : List Reg := [.x9,.x16,.x18,.x29,.x30,.x24,.x27]
def Keeps (s t : MachineState) := ∀ reg ∈ anchors, t.getReg reg=s.getReg reg

theorem Anchor.transport {s t : MachineState} {k d r : Nat} (h : Anchor s k d r) (keep : Keeps s t) : Anchor t k d r :=
  ⟨⟨(keep _ (by decide)).trans h.base,(keep _ (by decide)).trans h.count,(keep _ (by decide)).trans h.row,
     (keep _ (by decide)).trans h.span,(keep _ (by decide)).trans h.depth⟩,
    (keep _ (by decide)).trans h.cursor,(keep _ (by decide)).trans h.left⟩

theorem BlockResult.keep {s : MachineState} {b : Part} (h : BlockResult b s) (r : Reg)
    (preserved : b.equation r = original r) : (b.after s).getReg r=s.getReg r := by
  rw [h.regs,preserved]; cases r <;> rfl

def anchorOK (b : Part) := anchors.all fun r => decide (b.equation r=original r)

theorem BlockResult.keeps {s : MachineState} {b : Part} (h : BlockResult b s) (ok : anchorOK b) : Keeps s (b.after s) :=
  fun r hr => h.keep r (of_decide_eq_true (List.all_eq_true.mp ok r hr))

theorem copy_anchors (s : MachineState) (n : Nat) : Keeps s (copyWords s n) := by
  intro reg hr
  apply copy_keeps
  intro eq;subst reg;exact (by decide : ¬Reg.x6 ∈ anchors) hr

theorem test_anchors (b : Test) (s : MachineState) : Keeps s (b.after s) :=
  fun _ _ => MachineState.getReg_setPC

theorem Keeps.then {s t u : MachineState} (a : Keeps s t) (b : Keeps t u) : Keeps s u :=
  fun r h => (b r h).trans (a r h)

structure PathFrame (s : MachineState) (i : Index) (d l out : Nat) : Prop where
  ptr : s.getReg .x25 = W (out+32*l)
  idx : s.getReg .x20 = W (indexAbove i l)
  base : s.getReg .x22 = W (layerBase l)
  span : s.getReg .x17 = W (stride l)
  left : s.getReg .x28 = W (d-l)

end CommitGolfCandidate.Late.Open
