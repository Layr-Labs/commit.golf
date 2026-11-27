import CommitGolfCandidate.RungAMemory
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (levelCount nodeAddress rowAddress unusedSlotAddr)
def sizeAt (h : Nat) := slots .twentyFour h
def baseIndex (group h : Nat) := sizeAt h*group
def inGroup (group h j : Nat) := h<4 ∧ j<levelCount h ∧ j/sizeAt h=group
def frontier (C : Cover) (g h n : Nat) : Cover := fun u v=>C u v ∨ inGroup g u v ∧ (u<h ∨ u=h ∧ v%sizeAt u<n)
theorem sizePositive {h : Nat} (bh : h<4) : 0<sizeAt h:=by interval_cases h <;> decide
theorem frontierZero (C : Cover) (g h j : Nat) : C h j ↔ frontier C g 0 0 h j := by simp [frontier]
theorem frontierValidStep (C : Cover) (g h n : Nat) (bh : h<4) (bn : n<sizeAt h) (real : baseIndex g h+n<levelCount h) :
    ∀ u v, Cell (frontier C g h n) h (baseIndex g h+n) u v ↔ frontier C g h (n+1) u v := by
  intro u v
  have pos:=sizePositive bh
  constructor
  · rintro (before|⟨rfl,rfl⟩)
    · rcases before with old|⟨grp,edge⟩
      · exact Or.inl old
      · exact Or.inr ⟨grp,by rcases edge with prev|⟨rfl,lt⟩;exact Or.inl prev;exact Or.inr ⟨rfl,by omega⟩⟩
    · refine Or.inr ⟨⟨bh,real,?_⟩,Or.inr ⟨rfl,?_⟩⟩ <;> unfold baseIndex
      · rw [Nat.mul_add_div pos,Nat.div_eq_of_lt bn,Nat.add_zero]
      · rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt bn];omega
  · rintro (old|⟨grp,edge⟩)
    · exact Or.inl (Or.inl old)
    · rcases edge with prev|⟨equal,lt⟩
      · exact Or.inl (Or.inr ⟨grp,Or.inl prev⟩)
      · subst u
        by_cases done:v%sizeAt h<n
        · exact Or.inl (Or.inr ⟨grp,Or.inr ⟨rfl,done⟩⟩)
        · have e:=Nat.div_add_mod v (sizeAt h)
          rw [grp.2.2,show v%sizeAt h=n by omega] at e
          exact Or.inr ⟨rfl,e.symm⟩
theorem frontierSkip (C : Cover) (g h n : Nat) (missing : levelCount h≤baseIndex g h+n) :
    ∀ u v,frontier C g h n u v ↔ frontier C g h (n+1) u v := by
  intro u v
  unfold frontier
  apply or_congr_right
  constructor
  · rintro ⟨grp,prev|⟨equal,lt⟩⟩
    · exact ⟨grp,Or.inl prev⟩
    · exact ⟨grp,Or.inr ⟨equal,by omega⟩⟩
  · rintro ⟨grp,prev|⟨equal,lt⟩⟩
    · exact ⟨grp,Or.inl prev⟩
    · subst u
      have e:=Nat.div_add_mod v (sizeAt h)
      rw [grp.2.2] at e
      exact ⟨grp,Or.inr ⟨rfl,by have:=grp.2.1;unfold baseIndex at missing;omega⟩⟩

theorem frontierEnd (C : Cover) (g h u v : Nat) :
    frontier C g h (sizeAt h) u v ↔ frontier C g (h+1) 0 u v := by
  unfold frontier;constructor
  · rintro (c|⟨group,edge⟩);exact Or.inl c;exact Or.inr ⟨group,Or.inl (by rcases edge with h|⟨h,_⟩ <;> omega)⟩
  · rintro (c|⟨group,edge⟩);exact Or.inl c
    by_cases e:u=h
    · subst u;exact Or.inr ⟨group,Or.inr ⟨rfl,Nat.mod_lt _ (sizePositive group.1)⟩⟩
    · exact Or.inr ⟨group,Or.inl (by rcases edge with lt|⟨_,lt⟩ <;> omega)⟩

def seen (xs : List Index) : Cover := fun h j=>∃ i∈xs,inGroup (i.val/24) h j
theorem finishGroup (xs : List Index) (i : Index) (u v : Nat) :
    frontier (seen xs) (i.val/24) 4 0 u v ↔ seen (xs++[i]) u v := by
  simp only [seen,frontier,List.mem_append,List.mem_singleton]
  constructor
  · rintro (⟨j,mem,grp⟩|⟨grp,_⟩)
    · exact ⟨j,Or.inl mem,grp⟩
    · exact ⟨i,Or.inr rfl,grp⟩
  · rintro ⟨j,mem|rfl,grp⟩
    · exact Or.inl ⟨j,mem,grp⟩
    · exact Or.inr ⟨grp,Or.inl grp.1⟩

private theorem childGroup (h g n k : Nat) (hh : h<3) (hn : n<sizeAt (h+1)) (hk : k<S4.radix h) :
    (S4.radix h*(baseIndex g (h+1)+n)+k)/sizeAt h=g := by
  interval_cases h <;> simp [sizeAt,baseIndex,slots,depth,leaves,S4.radix] at * <;> omega

theorem readParent {H td ps s C} (g h n : Nat) (hh : h<3) (hn : n<sizeAt (h+1))
    (real : baseIndex g (h+1)+n<levelCount (h+1)) (known : View H td ps (frontier C g (h+1) n) s) :
    let p:=baseIndex g (h+1)+n
    let lane := fun k=>if k<S4.radix h ∧ S4.radix h*p+k<levelCount h then rebuildDigest H td h (S4.radix h*p+k)
       else Late.slice td (unusedSlotAddr h p k) 32
    readBuffer s (rowAddress h p) 96=lane 2++lane 1++lane 0 := by
  intro p lane
  have cell (k : Nat) (bk : k<3) : readBuffer s (unusedSlotAddr h p k) 32=lane k:=by
    dsimp only [lane]
    split
    next yes=>
      rw [show unusedSlotAddr h p k=nodeAddress h (S4.radix h*p+k) from (Late.row_slot h p k yes.1).symm]
      exact known.nodes _ _ (Or.inr ⟨⟨by omega,yes.2,childGroup h g n k hh hn yes.1⟩,Or.inl (by omega)⟩)
    next no=>exact known.gap _ _ _ ⟨by omega,real,bk,by omega⟩
  rw [Late.readTriple]
  rw [←cell 2 (by decide),←cell 1 (by decide),←cell 0 (by decide)]
  simp only [unusedSlotAddr,Nat.mul_zero,Nat.add_zero]
end CommitGolfCandidate.RungA
