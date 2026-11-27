import CommitGolfCandidate.RungAInterface
import CommitGolfCandidate.S4OpenInput
import CommitGolfCandidate.LateCachedTree
import CommitGolfCandidate.S4RecordData
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Trapdoor nodeAddress rowAddress levelCount unusedSlotAddr Digest slice)
open S4.Machine (W byte indexBase proofBase)
open S4.Open (initial)
abbrev Cover := Nat→Nat→Prop
def Novisit (C : Cover) (a : Nat) := ∀ h j,C h j → a<nodeAddress h j ∨ nodeAddress h j+32≤a
def Cell (C : Cover) (h j : Nat) : Cover := fun u v=>C u v ∨ (u=h ∧ v=j)
def Apart32 (a b : Nat) := a+32≤b ∨ b+32≤a

theorem apartCells {h j d k : Nat} (hr : h<4) (dr : d<24 ∨ d=24)
    (hj : j<levelCount h) (dk : k<levelCount d) (different : h≠d ∨ j≠k) :
    Apart32 (nodeAddress h j) (nodeAddress d k) := by
  rcases lt_trichotomy h d with hl|eq|dl
  · left;obtain ⟨u,hu⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : d≠0)
    rw [hu];exact Late.earlier_node u h j k (by omega) (by omega) hj
  · subst d
    have unequal : j≠k:=by tauto
    unfold Apart32 nodeAddress Late.gapOffset
    split <;> omega
  · right;obtain ⟨u,hu⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
    rw [hu];exact Late.earlier_node u d k j (by omega) (by omega) dk

theorem readEqual {s t : MachineState} (a n : Nat)
    (eq : ∀ k,k<n → byte s (a+k)=byte t (a+k)) : readBuffer s a n=readBuffer t a n := by
  unfold readBuffer;apply congrArg (BitVec.ofNat _);apply Finset.sum_congr rfl;intro k hk
  exact congrArg (fun b : Byte=>b.toNat*2^(8*k)) (eq k (Finset.mem_range.mp hk))

/-- Already reconstructed real nodes and the exact byte frame elsewhere. -/
structure View (H : Compression) (td : Trapdoor) (ps : Positions) (C : Cover) (s : MachineState) : Prop where
  valid : ∀ h j,C h j → h<4 ∧ j<levelCount h
  nodes : ∀ h j,C h j → readBuffer s (nodeAddress h j) 32=rebuildDigest H td h j
  frame : ∀ a,a<2^36 → Novisit C a → byte s a=byte (initial td ps) a

theorem View.ofMem {H td ps C s t} (h : View H td ps C s) (mem : t.mem=s.mem) : View H td ps C t := by
  refine ⟨h.valid,fun a b c=>?_,fun a b c=>?_⟩
  · apply (readEqual _ _ ?_).trans (h.nodes a b c)
    intro k hk;simp only [byte,MachineState.getByte,MachineState.getMem,mem]
  · simpa only [byte,MachineState.getByte,MachineState.getMem,mem] using h.frame a b c

theorem View.equiv {H td ps C D s} (h : View H td ps C s) (eq : ∀ a b,C a b ↔ D a b) : View H td ps D s :=
  ⟨fun a b hit=>h.valid _ _ ((eq a b).mpr hit),fun a b hit=>h.nodes _ _ ((eq a b).mpr hit),
   fun q lim out=>h.frame q lim (fun a b hit=>out _ _ ((eq a b).mp hit))⟩

structure Stored (s t : MachineState) (a : Nat) (v : Digest) : Prop where
  data : readBuffer t a 32=v
  outside : ∀ q,q<2^36 → (q<a ∨ a+32≤q) → byte t q=byte s q

theorem View.add {H td ps s t C h j} (old : View H td ps C s) (height : h<4) (real : j<levelCount h)
    (store : Stored s t (nodeAddress h j) (rebuildDigest H td h j)) : View H td ps (Cell C h j) t := by
  refine ⟨?_,?_,?_⟩
  · intro u v hit;rcases hit with before|⟨rfl,rfl⟩
    · exact old.valid _ _ before
    · exact ⟨height,real⟩
  · intro u v hit
    by_cases same : u=h ∧ v=j
    · obtain ⟨rfl,rfl⟩:=same;exact store.data
    have before : C u v:=hit.resolve_right same
    obtain ⟨uh,uv⟩:=old.valid _ _ before
    have apart:=apartCells uh (Or.inl (by omega)) uv real (by tauto)
    have top:=Late.parent_below_salts u v uv
    exact (readEqual _ _ (fun k hk=>store.outside _ (by unfold Late.rowBase at top;omega)
      (by unfold Apart32 at apart;omega))).trans (old.nodes _ _ before)
  · intro a lim out
    exact (store.outside a lim (out h j (Or.inr ⟨rfl,rfl⟩))).trans
      (old.frame a lim (fun u v before=>out _ _ (Or.inl before)))

theorem View.original {H td ps C s} (known : View H td ps C s) (a n : Nat) (lo : tdAddress≤a)
    (hi : a+n ≤ indexBase) (out : ∀ k,k<n → Novisit C (a+k)) : readBuffer s a n=slice td a n := by
  exact (readEqual _ _ (fun k hk=>known.frame _ (by unfold indexBase at hi;omega) (out _ hk))).trans (S4.Open.fixed_in td ps a n lo hi)

theorem View.row {H td ps C s} (known : View H td ps C s) (i : Nat) (hi : i<16777216) :
    readBuffer s (finalRowAddress i) 96 = slice td (finalRowAddress i) 96 := by
  apply known.original
  · unfold finalRowAddress Late.rowBase tdAddress;omega
  · unfold finalRowAddress Late.rowBase indexBase;omega
  · intro u hu h j hit
    right;have e:=Late.parent_below_salts h j (known.valid _ _ hit).2
    unfold finalRowAddress;omega

theorem View.gap {H td ps C s} (known : View H td ps C s) (h p k : Nat) (gap : Late.Padding h p k) :
    readBuffer s (unusedSlotAddr h p k) 32=slice td (unusedSlotAddr h p k) 32 := by
  apply known.original
  · unfold tdAddress unusedSlotAddr rowAddress;omega
  · have:=Late.padValid _ _ _ gap;unfold Late.rowBase indexBase at *;omega
  · intro u hu a j hit
    obtain ⟨ah,aj⟩:=known.valid _ _ hit
    have:=Late.node_pad a j h p k (by omega) aj gap;omega

theorem View.index {H td ps C s} (known : View H td ps C s) (n : Nat) (hn : n<ps.card) :
    s.getMem (W (indexBase+8*n)) = W (S4.recordIndex ps n).val := by
  let a:=indexBase+8*n
  have len : ps.card≤16777216:=by change ps.card≤LENGTH;simpa using Finset.card_le_univ ps
  have al : a%8=0:=by dsimp [a,indexBase];omega
  have same : readBuffer s a 8=readBuffer (initial td ps) a 8:=by
    apply readEqual;intro k hk
    apply known.frame _ (by dsimp [a,indexBase];omega)
    intro h j hit;right
    have e:=Late.parent_below_salts h j (known.valid _ _ hit).2
    dsimp [a,indexBase];unfold Late.rowBase at e;omega
  change S4.Machine.wordAt s a=_
  rw [S4.Open.wordExact _ _ al,same,←S4.Open.wordExact _ _ al]
  exact S4.Open.index_loaded td ps n (by simpa [S4.Open.indices] using hn)
end CommitGolfCandidate.RungA
