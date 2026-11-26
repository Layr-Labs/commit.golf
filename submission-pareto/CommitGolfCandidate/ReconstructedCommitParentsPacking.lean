import CommitGolfCandidate.ReconstructedCommitParentsImage

namespace CommitGolfCandidate.Reconstruction.CommitParents.Image
open CommitGolf ArtifactEncoding
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- Gather a balanced tree into a single little-endian bitvector. Each tree
node is read once even when the verifier checks thousands of consecutive words. -/
def packedBits : {n : Nat} → Packed n → BitVec (32*n)
  | _, .chunk n data => BitVec.ofNat (32*n) data
  | _, @Packed.join l r x y => ((packedBits y) ++ (packedBits x)).cast (by omega)

private theorem chunk_word (n v i : Nat) (h : i<n) :
    (BitVec.ofNat (32*n) v).extractLsb' (32*i) 32 = BitVec.ofNat 32 (v >>> (32*i)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_ofNat,Nat.testBit_shiftRight,hk,decide_true,
    show 32*i+k < 32*n by omega,Bool.true_and]

theorem packed_word {n : Nat} (p : Packed n) (i : Fin n) :
    (packedBits p).extractLsb' (32*i.val) 32 = p.get 32 i := by
  induction p with
  | chunk n data => exact chunk_word n data i i.isLt
  | @join l r x y hl hr =>
    simp only [packedBits,BitVec.extractLsb'_cast,Packed.get]
    split <;> rename_i h
    · rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
      exact hl ⟨i,h⟩
    · rw [BitVec.extractLsb'_append_eq_of_le (by omega),show 32*i.val-32*l = 32*(i.val-l) by omega]
      exact hr ⟨_,by have := i.isLt;omega⟩

/-- Select the interval before joining adjacent packed chunks. -/
def window {n : Nat} (p : Packed n) (start len : Nat) : BitVec len :=
  match p with
  | .chunk n v => (BitVec.ofNat (32*n) v).extractLsb' start len
  | @Packed.join l r a b =>
    if h : start+len ≤ 32*l then window a start len
    else if h₂ : 32*l ≤ start then window b (start-32*l) len
    else
      ((window b 0 (len-(32*l-start))) ++ (window a start (32*l-start))).cast (by omega)

theorem window_eq {n : Nat} (p : Packed n) (start len : Nat) :
    window p start len = (packedBits p).extractLsb' start len := by
  induction p generalizing start len with
  | chunk => rfl
  | @join l r a b la rb =>
    simp only [window,packedBits,BitVec.extractLsb'_cast]
    split <;> rename_i h
    · exact (la _ _).trans (BitVec.extractLsb'_append_eq_of_add_le h).symm
    split <;> rename_i h'
    · exact (rb _ _).trans (BitVec.extractLsb'_append_eq_of_le h').symm
    rw [la,rb]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_cast,BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and,Nat.zero_add]
    by_cases low : i < 32*l-start
    · simp [low,show start+i < 32*l by omega,BitVec.getLsbD_append]
    · simp [low,show ¬start+i < 32*l by omega,show i-(32*l-start) < len-(32*l-start) by omega,
        show start+i-32*l=i-(32*l-start) by omega,BitVec.getLsbD_append]

def listBits : (xs : List Atom) → BitVec (32*xs.length)
  | [] => 0
  | h :: t => ((listBits t) ++ h.word).cast (by simp [Nat.mul_add])

theorem list_word (xs : List Atom) (i : Fin xs.length) :
    (listBits xs).extractLsb' (32*i.val) 32 = xs[i.val].word := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons h t ih =>
    cases i using Fin.cases with
    | zero => simp [listBits,BitVec.extractLsb'_cast,BitVec.extractLsb'_append_eq_right]
    | succ i =>
      simp only [listBits,BitVec.extractLsb'_cast,Fin.val_succ,List.getElem_cons_succ]
      rw [BitVec.extractLsb'_append_eq_of_le (by omega),show 32*(i.val+1)-32=32*i.val by omega]
      exact ih i

private theorem slice_of_slice {w : Nat} (v : BitVec w) {p n j : Nat} (inside : j+32 ≤ n) :
    (v.extractLsb' p n).extractLsb' j 32 = v.extractLsb' (p+j) 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and,show j+k < n by omega,Nat.add_assoc]

def expanded (d : Nat) (is : List Nat) := is.flatMap (body d)

theorem next_start (d i : Nat) : start d (i+1) = start d i + (body d i).length := by
  have size : (body d i).length = (body d 0).length + (shifts i).length := by
    simp [body,shifts,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  rw [size]
  simp only [start,shifts,List.length_append,Nat.mul_add,Nat.mul_one,Nat.add_sub_cancel]
  by_cases z : i=0
  · subst i;simp
  split_ifs <;> simp_all <;> omega

private theorem starts_mono (d a j : Nat) : start d a ≤ start d (a+j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [←Nat.add_assoc,next_start d (a+j)];omega

theorem nth_in_level (d a n j k : Nat) (inside : j<n) (hk : k<(body d (a+j)).length) :
    (expanded d (List.range' a n))[start d (a+j)-start d a+k]? = (body d (a+j))[k]? := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    rw [List.range'_succ,expanded,List.flatMap_cons]
    cases j with
    | zero =>
      simp only [Nat.add_zero,Nat.sub_self,Nat.zero_add] at hk ⊢
      exact List.getElem?_append_left hk
    | succ j =>
      have ch : a+(j+1)=(a+1)+j := by omega
      rw [ch] at hk ⊢
      have mono := starts_mono d (a+1) j
      have nx := next_start d a
      have off : start d (a+1+j)-start d a+k = (body d a).length+(start d (a+1+j)-start d (a+1)+k) := by omega
      rw [off,List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
      exact ih (a+1) j (by omega) hk

def levelAtoms (d : Nat) := expanded d (List.range' 0 (unroll d))
def levelMatch (d : Nat) :=
  window Artifact.commitCode (32*levelStart d) (32*(levelAtoms d).length) = listBits (levelAtoms d)

theorem receipt_fetch (d i : Nat) (isSmall : i < unroll d) (j : Fin (body d i).length)
    (same : levelMatch d) (bounded : start d i + j.val < 150132) :
    Artifact.commitCode.get 32 ⟨start d i+j.val,bounded⟩ = (body d i)[j.val].word := by
  have nth := nth_in_level d 0 (unroll d) i j isSmall (by simpa using j.isLt)
  have base : start d 0 = levelStart d := by simp [start]
  simp only [Nat.zero_add,base,List.getElem?_eq_getElem j.isLt] at nth
  obtain ⟨inside,h⟩ := List.getElem?_eq_some_iff.1 nth
  let p := start d i-levelStart d+j.val
  have left : levelStart d ≤ start d i := by unfold start;omega
  unfold levelMatch at same
  rw [window_eq] at same
  have eq := congrArg (fun x => BitVec.extractLsb' (32*p) 32 x) same
  change ((packedBits Artifact.commitCode).extractLsb' (32*levelStart d) _).extractLsb' (32*p) 32 =
    (listBits (levelAtoms d)).extractLsb' (32*p) 32 at eq
  have inP : p < (levelAtoms d).length := inside
  rw [slice_of_slice _ (by omega),show 32*levelStart d+32*p=32*(start d i+j.val) by dsimp [p];omega,
    packed_word Artifact.commitCode ⟨_,bounded⟩,list_word _ ⟨p,inP⟩] at eq
  exact eq.trans (congrArg Atom.word h)

end CommitGolfCandidate.Reconstruction.CommitParents.Image
