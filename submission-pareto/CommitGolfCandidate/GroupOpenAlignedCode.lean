import CommitGolfCandidate.GroupOpenCapCopy
import CommitGolfCandidate.GroupOpenSibling

namespace TwoPermutationPrototype.GroupedOpening.AlignedFields
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Wide Shifted30 CapCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def pcAt (w : Nat) : Word := BitVec.ofNat 64 (4096+4*w)
def cost (dest : Nat) := if dest%8=0 then 10 else if dest%8=4 then 16 else 22
def residue (c k : Nat) := (2*c+30*k)%8
def start (c : Nat) : Nat → Nat
  | 0 => 2048+256*c
  | k+1 => start c k+3+cost (residue c k)+2

def classOf (o : Nat) := recordBase o%8/2

theorem class_lt (o : Nat) : classOf o < 4 := by unfold classOf; omega

theorem record_even (o : Nat) : recordBase o % 2 = 0 := by
  have h : proofBase%2=0 := by decide
  unfold recordBase recordBytes
  omega

theorem target_class (o l : Nat) (lo : 2 ≤ l) (hi : l ≤ 12) :
    siblingDestination o l % 8 = residue (classOf o) (l-2) := by
  have even := record_even o
  unfold siblingDestination siblingOffset residue classOf
  rw [if_neg (by omega), if_pos (by omega)]
  omega

def copyBody (r : Nat) (s : MachineState) : MachineState :=
  if r=0 then pairsRun 2 .x7 28 28 0 1
    (pairsRun 4 .x7 24 24 0 1 (pairsRun 8 .x7 0 0 0 3 s))
  else if r=4 then pairsRun 2 .x7 28 28 0 1 (pairsRun 4 .x7 0 0 0 7 s)
  else copy30 s

private def Slice (word : Nat) (xs : List Instr) : Prop :=
  ((openingImage.code.drop word).take xs.length).map Opening.decodeBase = xs.map some

private instance (w : Nat) (xs : List Instr) : Decidable (Slice w xs) := by unfold Slice; infer_instance

private theorem code_of_slice {word : Nat} {xs : List Instr} (h : Slice word xs) : CodeAt word xs := by
  intro j
  have e := congrArg (fun ys : List (Option Instr) => ys[j.val]?) h
  simp only [List.getElem?_map, List.getElem?_take, j.isLt, ite_true,
    List.getElem?_drop, List.getElem?_eq_getElem j.isLt, Option.map_some] at e
  cases hit : openingImage.code[word+j.val]? with
  | none => simp [hit] at e
  | some w =>
    simp only [hit, Option.map_some, Option.some.injEq] at e
    simpa [Decodes, hit] using e

private def pairRows (n width off : Nat) : List Instr :=
  List.ofFn fun j : Fin (2*n) => if j.val%2=0 then wideLoad width .x7 (off+width*(j.val/2))
    else wideStore width (off+width*(j.val/2))

private theorem pairs_of_slice {w n width off : Nat} (h : Slice w (pairRows n width off)) :
    PairsAt w n width .x7 off off := by
  have size : (pairRows n width off).length=2*n := by simp [pairRows]
  intro j hj
  have a := code_of_slice h ⟨2*j,by omega⟩
  have b := code_of_slice h ⟨2*j+1,by omega⟩
  simp only [pairRows,List.getElem_ofFn] at a b
  refine ⟨?_,?_⟩
  · simpa [show 2*j%2=0 by omega,show 2*j/2=j by omega] using a
  · simpa [show (2*j+1)%2=1 by omega,show (2*j+1)/2=j by omega,Nat.add_assoc] using b

theorem head_code (c : Fin 4) (k : Fin 11) : CodeAt (start c k) headCode := by
  apply code_of_slice
  revert k; fin_cases c <;> decide +kernel

theorem tail_code (c : Fin 4) (k : Fin 11) :
    CodeAt (start c k+3+cost (residue c k)) [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1] := by
  apply code_of_slice
  revert k; fin_cases c <;> decide +kernel

theorem code_fits : ∀ c : Fin 4, ∀ k : Fin 11, start c k+3+cost (residue c k)+2 < 3072 := by decide
theorem residue_bound (c k : Nat) : residue c k < 8 := Nat.mod_lt _ (by decide)
theorem cost_residue (c k : Nat) : cost (residue c k)=
    (if residue c k=0 then 10 else if residue c k=4 then 16 else 22) := by
  have h := residue_bound c k
  simp only [cost, Nat.mod_eq_of_lt h]

theorem dwords_code : ∀ c : Fin 4, ∀ k : Fin 11, residue c k=0 →
    PairsAt (start c k+3) 3 8 .x7 0 0 ∧ PairsAt (start c k+3+6) 1 4 .x7 24 24 ∧
      PairsAt (start c k+3+8) 1 2 .x7 28 28 := by
  intro c k h
  refine ⟨pairs_of_slice ?_,pairs_of_slice ?_,pairs_of_slice ?_⟩ <;>
    revert k <;> fin_cases c <;> decide +kernel
theorem words_code : ∀ c : Fin 4, ∀ k : Fin 11, residue c k=4 →
    PairsAt (start c k+3) 7 4 .x7 0 0 ∧ PairsAt (start c k+3+14) 1 2 .x7 28 28 := by
  intro c k h
  refine ⟨pairs_of_slice ?_,pairs_of_slice ?_⟩ <;>
    revert k <;> fin_cases c <;> decide +kernel
theorem shifted_code : ∀ c : Fin 4, ∀ k : Fin 11, residue c k ≠ 0 → residue c k ≠ 4 →
    ∀ j : Fin 4, CodeAt (start c k+3+6*j.val) (chunkCode (8*j.val) (decide (j.val=3))) := by
  intro c k h0 h4 j
  apply code_of_slice
  revert k; fin_cases c <;> revert j <;> decide +kernel


end TwoPermutationPrototype.GroupedOpening.AlignedFields
