import CommitGolfCandidate.ReconstructedGenerator

namespace CommitGolfCandidate.Reconstruction.HidingTape

open Generator

abbrev Position := Fin (2^24)
abbrev Lane := Fin 12
abbrev Salt := BitVec 120
abbrev Reply := BitVec 1600

/-- Twelve 120-bit lanes from the 25-word reply. Lane zero ends in the last word. -/
def saltAt (r : Reply) (l : Lane) : Salt := r.extractLsb' (saltBit l 0) 120

/-- The remaining 160 bits consist of eleven padding bytes, one unused 64-bit word
and a final padding byte. This order makes the residual coordinates contiguous. -/
def residualPosition (i : Fin 160) : Nat :=
  if i.val < 88 then 128*(i.val/8) + 120 + i.val%8
  else if i.val < 152 then 1408 + (i.val-88)
  else 1592 + (i.val-152)

def residual (r : Reply) (i : Fin 160) := r.getLsbD (residualPosition i)

private theorem partition_bits (n : Nat) (inside : n < 1600) :
    (∃ l : Lane, ∃ j : Fin 120, n = saltBit l 0 + j.val) ∨
      (∃ i : Fin 160, n = residualPosition i) := by
  by_cases first : n < 1408
  · by_cases data : n%128 < 120
    · refine Or.inl ⟨⟨n/128+1, by omega⟩, ⟨n%128,data⟩, ?_⟩
      simp [saltBit]
      omega
    · refine Or.inr ⟨⟨8*(n/128)+(n%128-120), by omega⟩, ?_⟩
      simp only [residualPosition]
      split <;> omega
  · by_cases middle : n < 1472
    · refine Or.inr ⟨⟨88+(n-1408),by omega⟩,?_⟩
      simp only [residualPosition]
      split <;> (try split) <;> omega
    · by_cases last : n < 1592
      · exact Or.inl ⟨0,⟨n-1472,by omega⟩,by change n = 1472+(n-1472); omega⟩
      · refine Or.inr ⟨⟨152+(n-1592),by omega⟩,?_⟩
        simp only [residualPosition]
        split <;> (try split) <;> omega

theorem reply_ext {r s : Reply} (salts : saltAt r = saltAt s) (rest : residual r = residual s) :
    r = s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases partition_bits i hi with ⟨l,j,eq⟩ | ⟨j,eq⟩
  · have h := congrArg (fun x : Salt => x.getLsbD j.val) (congrFun salts l)
    rw [eq]
    simpa only [saltAt, BitVec.getLsbD_extractLsb', j.isLt, decide_true, Bool.true_and] using h
  · rw [eq]
    exact congrFun rest j

abbrev Blocks := Fin 4096 → Fin 342 → Lane → Salt
abbrev Slack := Fin 4096 → Fin 8 → Salt
def select (t : Blocks) (i : Position) := t (tileOf i) (groupOf i) (laneOf i)
def unused (t : Blocks) (tile : Fin 4096) (j : Fin 8) := t tile 341 ⟨4+j.val,by omega⟩

/-- At every tile, the last eight lanes in the last generator reply are not used. -/
def assemble (values : Position → Salt) (spare : Slack) (t : Fin 4096)
    (g : Fin 342) (l : Lane) : Salt :=
  if h : 12*g.val+l.val < 4096 then values ⟨4096*t.val+12*g.val+l.val,by have := t.isLt; omega⟩
  else spare t ⟨l.val-4,by have := l.isLt; omega⟩

theorem assemble_select (t : Blocks) : assemble (select t) (unused t) = t := by
  funext i g l
  have ig := g.isLt
  have il := l.isLt
  unfold assemble
  split
  · rename_i h
    have rem : (4096*i.val + 12*g.val+l.val)%4096 = 12*g.val+l.val := by
      rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt h]
    unfold select
    congr 1 <;> apply Fin.ext <;> simp only [tileOf, groupOf, laneOf, rem] <;> omega
  · have e : g.val = 341 := by omega
    unfold unused
    congr 1 <;> apply Fin.ext
    · exact e.symm
    · change 4+(l.val-4) = l.val
      omega

theorem select_assemble (v : Position → Salt) (spare : Slack) : select (assemble v spare) = v := by
  funext i
  unfold select assemble
  have dec := position_decomposition i
  have bound : 12*(groupOf i).val+(laneOf i).val < 4096 := by simp only [groupOf,laneOf]; omega
  rw [dite_eq_left bound]
  congr 1
  exact Fin.ext dec

theorem unused_assemble (v : Position → Salt) (spare : Slack) : unused (assemble v spare) = spare := by
  funext i j
  have hj := j.isLt
  unfold unused assemble
  split
  · rename_i h
    change 12*341+(4+j.val)<4096 at h
    omega
  · congr 1 <;> apply Fin.ext <;> simp

end CommitGolfCandidate.Reconstruction.HidingTape
