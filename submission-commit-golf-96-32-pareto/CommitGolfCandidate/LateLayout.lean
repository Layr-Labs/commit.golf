import CommitGolfCandidate.LateMemory
import CommitGolfCandidate.S4Geometry
namespace CommitGolfCandidate.Late
open CommitGolf
def levelCount (h : Nat) := S4.width (min h 24)
def levelOffset (h : Nat) := S4.layerOffset (min h 24)
def nodeAddress (h i : Nat) := 4294971424+levelOffset h+(if h=0 then 32*i else gapOffset i)
def rowAddress (h p : Nat) := 4294971424+levelOffset h+96*p

theorem leafAddress (i : Nat) : nodeAddress 0 i=4294971424+32*i := rfl
theorem binaryAddress (h i : Nat) : nodeAddress (h+1) i=4294971424+levelOffset (h+1)+gapOffset i := rfl
theorem level_count_le (h : Nat) : levelCount h≤LENGTH :=
  (show ∀ x : Fin 25,S4.width x.val≤LENGTH by decide) ⟨min h 24,by omega⟩

theorem level_adjacent (h : Nat) (bh : h<LOG_LENGTH) :
    levelOffset (h+1)=levelOffset h+96*levelCount (h+1) := by
  change h<24 at bh
  simp only [levelOffset,levelCount,Nat.min_eq_left (by omega : h≤24),Nat.min_eq_left (by omega : h+1≤24),S4.layerOffset]
  rw [S4.row_width ⟨h,bh⟩]

theorem row_base (h p : Nat) : nodeAddress h (S4.radix h*p)=rowAddress h p := by
  by_cases e : h=0 <;> simp [nodeAddress,rowAddress,S4.radix,gapOffset,e] <;> omega

theorem row_slot (h p k : Nat) (hk : k<S4.radix h) :
    nodeAddress h (S4.radix h*p+k)=rowAddress h p+32*k := by
  by_cases e : h=0 <;> simp [nodeAddress,rowAddress,S4.radix,gapOffset,e] at hk ⊢ <;> omega

theorem row_after (h p : Nat) (bh : h<LOG_LENGTH) (bp : p<levelCount (h+1)) :
    rowAddress h p+96≤4294971424+levelOffset (h+1) := by rw [level_adjacent _ bh];unfold rowAddress;omega

theorem padded_region (h : Nat) : 4294971424+levelOffset h+96*S4.rowCount (min h 24)≤rowBase :=
  S4.addressValid ⟨min h 24,by omega⟩

theorem parent_below_salts (h i : Nat) (inside : i<levelCount h) : nodeAddress h i+32≤rowBase := by
  have top:=padded_region h
  unfold S4.rowCount at top;unfold levelCount at inside
  by_cases e : h=0
  · subst h;change i<16777216 at inside;rw [leafAddress];unfold rowBase;omega
  · have p : min h 24≠0:=by omega
    simp only [S4.radix,if_neg p] at top
    simp only [nodeAddress,if_neg e,gapOffset];omega

theorem levelOffset_mono {a b : Nat} (le : a≤b) : levelOffset a≤levelOffset b := by
  have step : ∀ n,S4.layerOffset n≤S4.layerOffset (n+1) := fun n=>Nat.le_add_right _ _
  exact (monotone_nat_of_le_succ step) (by omega)

theorem row_disjoint (h p j : Nat) (bh : h<LOG_LENGTH) (bp : p<levelCount (h+1)) :
    rowAddress h p+96 ≤ nodeAddress (h+1) j :=
  (row_after h p bh bp).trans (by rw [binaryAddress];omega)

theorem nodeAligned (h j : Nat) : nodeAddress h j%8=0 := by
  have mult : ∀ n,S4.layerOffset n%8=0 := by
    intro n;induction n with | zero=>rfl | succ n ih=>simp only [S4.layerOffset];omega
  have m:=mult (min h 24);unfold nodeAddress levelOffset gapOffset;split <;> omega

theorem rowAligned (h p : Nat) : rowAddress h p%8=0 := by rw [←row_base];apply nodeAligned
end CommitGolfCandidate.Late
