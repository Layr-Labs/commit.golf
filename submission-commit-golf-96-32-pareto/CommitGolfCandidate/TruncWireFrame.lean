import CommitGolfCandidate.TruncMoves
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 9000
set_option maxHeartbeats 200000

def base : Nat := 10871640096
def srcIndex (back : Bool) (k : Nat) : Option Nat := if back then wideIndex k else some (narrowIndex k)
def wanted (back : Bool) (initial : MachineState) (k : Nat) : Byte :=
  ((srcIndex back k).map fun i=>byte initial (base+i)).getD 0
def passed (back : Bool) (cut a : Nat) : Prop :=
  if back then base+cut≤a ∧ a<base+71680 else base≤a ∧ a<base+cut
instance (b : Bool) (c a : Nat) : Decidable (passed b c a) := by unfold passed;split <;> infer_instance

def Frame (back : Bool) (initial now : MachineState) (cut : Nat) : Prop :=
  ∀ a, a<2^64 → byte now a=if passed back cut a then wanted back initial (a-base) else byte initial a

theorem initialFrame (back : Bool) (s : MachineState) : Frame back s s (if back then 71680 else 0) := by
  intro a _;cases back <;> simp [passed]

theorem frameMem {back s t z cut} (f : Frame back s t cut) (eq : z.mem=t.mem) : Frame back s z cut :=
  fun a h=>(show byte z a=byte t a from by simp only [byte,MachineState.getByte,MachineState.getMem,eq]).trans (f a h)

private theorem passedAt (back : Bool) (d k : Nat) (lim : d+2≤ if back then 71680 else 68096) (two : k<2) :
    passed back (if back then d else d+2) (base+d+k) := by
  cases back <;> simp only [passed,Bool.false_eq_true,ite_true,ite_false] at lim ⊢ <;> omega
private theorem sameAway (back : Bool) (d a : Nat) (z : a≠base+d) (o : a≠base+d+1) :
    passed back (if back then d else d+2) a ↔ passed back (if back then d+2 else d) a := by
  cases back <;> simp only [passed,Bool.false_eq_true,ite_true,ite_false] <;> omega
private theorem intWord (d : Nat) (h : d≤71680) : base+d+2≤2^64 := by unfold base;omega

theorem advanceBytes (back : Bool) (s t : MachineState) (d : Nat) (src : Option Nat)
    (lim : d+2≤ if back then 71680 else 68096) (even : d%2=0)
    (sourceBound : ∀ a∈src, a+2≤71680 ∧ a%2=0 ∧ (if back then a≤d else d≤a))
    (mapping : ∀ k<2,srcIndex back (d+k)=src.map (·+k))
    (old : Frame back s t (if back then d+2 else d)) :
    Frame back s (copy t (src.map (base+·)) (base+d)) (if back then d else d+2) := by
  have bd : d+2≤71680 := by cases back <;> simp at lim <;> omega
  have ba := intWord d (by omega)
  have ed : (base+d)%2=0 := by unfold base;omega
  have written (k : Nat) (hk : k<2) :
      byte (copy t (src.map (base+·)) (base+d)) (base+d+k)=wanted back s (d+k) := by
    unfold wanted;rw [mapping k hk]
    cases src with
    | none =>
      have h:=cleared t (base+d) ba ed
      interval_cases k <;> first | exact h.1 | exact h.2
    | some a =>
      have h:=sourceBound a (by simp)
      have pair:=copied t (base+d) (base+a) ba (intWord a (by omega)) ed (by unfold base;omega)
      have safe : ¬passed back (if back then d+2 else d) (base+a+k) := by
        cases back <;> simp only [passed,Bool.false_eq_true,ite_true,ite_false] at h ⊢ <;> omega
      have original := old (base+a+k) (by unfold base;omega)
      rw [if_neg safe] at original
      simp only [Option.map_some,Option.getD_some]
      rw [←Nat.add_assoc]
      apply Eq.trans _ original
      interval_cases k <;> first | exact pair.1 | exact pair.2
  intro q bq
  by_cases z : q=base+d
  · subst q;have y:=passedAt back d 0 lim (by decide)
    simp only [Nat.add_zero] at y
    rw [if_pos y,show base+d-base=d by omega];exact written 0 (by decide)
  by_cases o : q=base+d+1
  · subst q;rw [if_pos (passedAt back d 1 lim (by decide)),show base+d+1-base=d+1 by omega];exact written 1 (by decide)
  rw [outside t _ _ q ba bq ed ⟨z,o⟩,old q bq]
  by_cases e : passed back (if back then d+2 else d) q
  · rw [if_pos e,if_pos ((sameAway back d q z o).mpr e)]
  · rw [if_neg e,if_neg (fun n=>e ((sameAway back d q z o).mp n))]

end CommitGolfCandidate.Trunc.Wire
