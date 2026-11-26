import CommitGolfCandidate.LateLayout
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def unusedSlotAddr (h p k : Nat) := rowAddress h p+32*k
structure Padding (h p k : Nat) : Prop where
  height : h<24
  within : p<levelCount (h+1)
  lane : k<3
  missing : S4.radix h≤k ∨ levelCount h≤S4.radix h*p+k

def Gaps (s : MachineState) : Prop := ∀ h p k,Padding h p k → readBuffer s (unusedSlotAddr h p k) 32=0

theorem padEnd (h p k : Nat) (g : Padding h p k) : unusedSlotAddr h p k+32 ≤ 4294971424+levelOffset (h+1) := by
  have b:=row_after h p g.height g.within
  have l:=g.lane;unfold unusedSlotAddr;omega

theorem padValid (h p k : Nat) (g : Padding h p k) : unusedSlotAddr h p k+32≤rowBase := by
  have a:=padEnd h p k g
  have b:=padded_region (h+1);omega

theorem nodeEnd (h i : Nat) (bh : h<24) (bi : i<levelCount h) :
    nodeAddress h i+32≤4294971424+levelOffset (h+1) := by
  rw [level_adjacent _ bh]
  have rc:=S4.row_width ⟨h,bh⟩
  simp only [S4.rowCount] at rc
  change (S4.width h+S4.radix h-1)/S4.radix h=S4.width (h+1) at rc
  have hi : i<S4.width h := by simpa only [levelCount,Nat.min_eq_left (by omega : h≤24)] using bi
  rw [show levelCount (h+1)=S4.width (h+1) by unfold levelCount;rw [Nat.min_eq_left (by omega)]]
  by_cases z : h=0 <;> simp only [nodeAddress,S4.radix,z,ite_false,ite_true,gapOffset] at rc hi ⊢ <;> omega

theorem node_pad (h i d p k : Nat) (bh : h≤24) (bi : i<levelCount h) (g : Padding d p k) :
    nodeAddress h i+32≤unusedSlotAddr d p k ∨ unusedSlotAddr d p k+32≤nodeAddress h i := by
  rcases lt_trichotomy h d with before|rfl|after
  · left;have b:=nodeEnd h i (by have:=g.height;omega) bi
    have m:=levelOffset_mono (a:=h+1) (b:=d) (by omega)
    unfold unusedSlotAddr rowAddress;omega
  · have kLim:=g.lane;have absent:=g.missing
    by_cases eq : h=0 <;> simp only [nodeAddress,unusedSlotAddr,rowAddress,S4.radix,eq,ite_true,ite_false,gapOffset] at absent bi ⊢ <;> omega
  · right;have b:=padEnd d p k g
    have m:=levelOffset_mono (a:=d+1) (b:=h) (by omega)
    unfold nodeAddress;omega

theorem earlier_node (d h i j : Nat) (le : h≤d) (ht : d<24) (hi : i<levelCount h) :
    nodeAddress h i+32≤nodeAddress (d+1) j := by
  have b:=nodeEnd h i (by omega) hi;have m : levelOffset (h+1)≤levelOffset (d+1):=levelOffset_mono (by omega)
  rw [binaryAddress];omega
end CommitGolfCandidate.Late
