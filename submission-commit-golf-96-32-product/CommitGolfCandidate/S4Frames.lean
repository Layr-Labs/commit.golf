import CommitGolfCandidate.S4Inputs
import CommitGolfCandidate.S4Auth
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)

/-- Only the first 32 KiB is used to hold checker scratch data. -/
def InputsStill (input : CheckInput) (s : MachineState) := ∀ q,32768≤q → q<2^64 → byte s q=byte (initial input) q

theorem InputsStill.read {i : CheckInput} {s : MachineState} (known : InputsStill i s)
    (a n : Nat) (lo : 32768≤a) (hi : a+n≤2^64) : readBuffer s a n=readBuffer (initial i) a n := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl
  intro j bj;have b:=Finset.mem_range.mp bj
  exact congrArg (fun x : Byte=>x.toNat*2^(8*j)) (known (a+j) (by omega) (by omega))

theorem InputsStill.moved {i : CheckInput} {s t : MachineState} {a b n : Nat} (known : InputsStill i s)
    (m : Moved s t a b n) (scratch : b+n≤32768) : InputsStill i t := by
  intro q l h;exact (m q h).trans ((if_neg (by omega)).trans (known q l h))

def firstBefore (v : View) (n u : Nat) := (List.range n).find? (fun r=>bucket v r==u)
def served (H : Compression) (v : View) (n u : Nat) := (firstBefore v n u).map (lower .byte H v)

theorem firstNext (v : View) (n u : Nat) :
    firstBefore v (n+1) u=(firstBefore v n u).or (if bucket v n=u then some n else none) := by
  simp only [firstBefore,List.range_succ,List.find?_append,List.find?_cons,List.find?_nil]
  by_cases e : bucket v n=u
  · rw [if_pos e,beq_iff_eq.mpr e]
  · rw [if_neg e,beq_eq_false_iff_ne.mpr e]

theorem servedFirst (H : Compression) (v : View) (n u : Nat) (absent : served H v n u=none) :
    served H v (n+1) u=if bucket v n=u then some (lower .byte H v n) else none := by
  unfold served at absent ⊢
  have e : firstBefore v n u=none:=by cases z : firstBefore v n u <;> simp_all
  rw [firstNext,e];split <;> rfl

theorem servedKeeps (H : Compression) (v : View) (n u : Nat) (d : Digest) (hit : served H v n u=some d) :
    served H v (n+1) u=some d := by
  unfold served at hit ⊢
  rw [firstNext];cases e : firstBefore v n u with
  | none=>simp [e] at hit
  | some r=>rw [e] at hit;exact hit

def AgreesThrough (H : Compression) (v : View) (n : Nat) :=
  ∀ r<n,served H v n (bucket v r)=some (lower .byte H v r)

theorem agreesNext (H : Compression) (v : View) (n : Nat) (agree : AgreesThrough H v n)
    (accept : ∀ x,served H v n (bucket v n)=some x → x=lower .byte H v n) : AgreesThrough H v (n+1) := by
  intro i hi
  by_cases atEnd : i=n
  · subst i;cases e : served H v n (bucket v n) with
    | none=>rw [servedFirst _ _ _ _ e,if_pos rfl]
    | some x=>exact (servedKeeps _ _ _ _ x e).trans (congrArg some (accept x e))
  · exact servedKeeps _ _ _ _ _ (agree i (by omega))

theorem disagreement {H : Compression} {v : View} {n : Nat} {x : Digest} (inRange : n<128)
    (already : served H v n (bucket v n)=some x) (different : x≠lower .byte H v n) (root : Digest) :
    ¬BatchValid .byte H v root := by
  intro valid
  have stay (k : Nat) : served H v (n+k) (bucket v n)=some x:=by
    induction k with
    | zero=>exact already
    | succ k ih=>exact servedKeeps _ _ _ _ _ ih
  have h:=stay (128-n)
  rw [show n+(128-n)=128 by omega] at h
  exact different (Option.some.inj (h.symm.trans (valid.1 n inRange)))

structure Env (i : CheckInput) (s : MachineState) : Prop where
  mode : s.getReg .x5=0
  kind : s.getReg .x13=0
  width : s.getReg .x11=96
  three : s.getReg .x23=3
  root : s.getReg .x27=W rootBase
  data : InputsStill i s

structure Cursor (i : CheckInput) (s : MachineState) (n : Nat) : Prop where
  index : s.getReg .x8=W (indexBase+8*n)
  value : s.getReg .x9=W (valueBase+256*n)
  proof : s.getReg .x18=W (proofBase+recordBytes (decide (i.positions.card=BATCH))*n)
  count : s.getReg .x19=W (i.positions.card-n)

structure Seen (H : Compression) (v : View) (n : Nat) (s : MachineState) : Prop where
  flags : ∀ u<342,byte s (768+u)=if (served H v n u).isSome then 1 else 0
  leaves : ∀ u<342,∀ d,served H v n u=some d → readBuffer s (2048+32*u) 32=d
  agree : AgreesThrough H v n

theorem InputsStill.regs {i : CheckInput} {s t : MachineState} (a : InputsStill i s) (same : t.mem=s.mem) :
    InputsStill i t := by
  intro q l h;simpa only [byte,MachineState.getByte,MachineState.getMem,same] using a q l h

end CommitGolfCandidate.S4.Machine
