import CommitGolfCandidate.ReconstructedOpeningOps

namespace CommitGolfCandidate.Reconstruction.OpeningIndex
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Generator CommitWindows TwoPermutationPrototype.RV64
set_option maxRecDepth 24576
set_option maxHeartbeats 1500000

def slot (i : Index) : Fin 4096 := ⟨i.val%4096,by omega⟩
def word (j : Fin 4096) := BitVec.ofNat 64 j.val
def highProduct (j : Fin 4096) := rv64_mulhu (word j <<< 48) 2863333376
def bucket (j : Fin 4096) := (rv64_mulhu (word j <<< 52) 11186176) >>> 19
def offset (j : Fin 4096) := (word j + ((bucket j <<< 6) - (bucket j <<< 8))) &&& 65535
def markerBytes (j : Fin 4096) := (highProduct j >>> 16) &&& 120
def lane (j : Fin 4096) :=
  let a := highProduct j >>> 19
  word j + (((a <<< 2).truncate 32 - (a <<< 4).truncate 32).signExtend 64)

theorem truncate_index (i : Index) :
    (BitVec.ofNat 64 i.val <<< 52) = word (slot i) <<< 52 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,word,slot,Nat.shiftLeft_eq]
  have h : i.val < 2^24 := i.isLt
  omega

private def Correct (j : Fin 4096) : Prop :=
    ((word j <<< 52) >>> 52) = word j ∧ offset j=BitVec.ofNat 64 (j.val%192) ∧
    markerBytes j=BitVec.ofNat 64 (8*(j.val/12%16)) ∧ lane j=BitVec.ofNat 64 (j.val%12)

private def cell (a b : Fin 64) : Fin 4096 := ⟨a.val*64+b.val,by have := a.isLt;have := b.isLt;omega⟩
private theorem row0 : ∀ k : Fin 64, Correct (cell 0 k) := by unfold Correct;decide +kernel
private theorem row1 : ∀ k : Fin 64, Correct (cell 1 k) := by unfold Correct;decide +kernel
private theorem row2 : ∀ k : Fin 64, Correct (cell 2 k) := by unfold Correct;decide +kernel
private theorem row3 : ∀ k : Fin 64, Correct (cell 3 k) := by unfold Correct;decide +kernel
private theorem row4 : ∀ k : Fin 64, Correct (cell 4 k) := by unfold Correct;decide +kernel
private theorem row5 : ∀ k : Fin 64, Correct (cell 5 k) := by unfold Correct;decide +kernel
private theorem row6 : ∀ k : Fin 64, Correct (cell 6 k) := by unfold Correct;decide +kernel
private theorem row7 : ∀ k : Fin 64, Correct (cell 7 k) := by unfold Correct;decide +kernel
private theorem row8 : ∀ k : Fin 64, Correct (cell 8 k) := by unfold Correct;decide +kernel
private theorem row9 : ∀ k : Fin 64, Correct (cell 9 k) := by unfold Correct;decide +kernel
private theorem row10 : ∀ k : Fin 64, Correct (cell 10 k) := by unfold Correct;decide +kernel
private theorem row11 : ∀ k : Fin 64, Correct (cell 11 k) := by unfold Correct;decide +kernel
private theorem row12 : ∀ k : Fin 64, Correct (cell 12 k) := by unfold Correct;decide +kernel
private theorem row13 : ∀ k : Fin 64, Correct (cell 13 k) := by unfold Correct;decide +kernel
private theorem row14 : ∀ k : Fin 64, Correct (cell 14 k) := by unfold Correct;decide +kernel
private theorem row15 : ∀ k : Fin 64, Correct (cell 15 k) := by unfold Correct;decide +kernel
private theorem row16 : ∀ k : Fin 64, Correct (cell 16 k) := by unfold Correct;decide +kernel
private theorem row17 : ∀ k : Fin 64, Correct (cell 17 k) := by unfold Correct;decide +kernel
private theorem row18 : ∀ k : Fin 64, Correct (cell 18 k) := by unfold Correct;decide +kernel
private theorem row19 : ∀ k : Fin 64, Correct (cell 19 k) := by unfold Correct;decide +kernel
private theorem row20 : ∀ k : Fin 64, Correct (cell 20 k) := by unfold Correct;decide +kernel
private theorem row21 : ∀ k : Fin 64, Correct (cell 21 k) := by unfold Correct;decide +kernel
private theorem row22 : ∀ k : Fin 64, Correct (cell 22 k) := by unfold Correct;decide +kernel
private theorem row23 : ∀ k : Fin 64, Correct (cell 23 k) := by unfold Correct;decide +kernel
private theorem row24 : ∀ k : Fin 64, Correct (cell 24 k) := by unfold Correct;decide +kernel
private theorem row25 : ∀ k : Fin 64, Correct (cell 25 k) := by unfold Correct;decide +kernel
private theorem row26 : ∀ k : Fin 64, Correct (cell 26 k) := by unfold Correct;decide +kernel
private theorem row27 : ∀ k : Fin 64, Correct (cell 27 k) := by unfold Correct;decide +kernel
private theorem row28 : ∀ k : Fin 64, Correct (cell 28 k) := by unfold Correct;decide +kernel
private theorem row29 : ∀ k : Fin 64, Correct (cell 29 k) := by unfold Correct;decide +kernel
private theorem row30 : ∀ k : Fin 64, Correct (cell 30 k) := by unfold Correct;decide +kernel
private theorem row31 : ∀ k : Fin 64, Correct (cell 31 k) := by unfold Correct;decide +kernel
private theorem row32 : ∀ k : Fin 64, Correct (cell 32 k) := by unfold Correct;decide +kernel
private theorem row33 : ∀ k : Fin 64, Correct (cell 33 k) := by unfold Correct;decide +kernel
private theorem row34 : ∀ k : Fin 64, Correct (cell 34 k) := by unfold Correct;decide +kernel
private theorem row35 : ∀ k : Fin 64, Correct (cell 35 k) := by unfold Correct;decide +kernel
private theorem row36 : ∀ k : Fin 64, Correct (cell 36 k) := by unfold Correct;decide +kernel
private theorem row37 : ∀ k : Fin 64, Correct (cell 37 k) := by unfold Correct;decide +kernel
private theorem row38 : ∀ k : Fin 64, Correct (cell 38 k) := by unfold Correct;decide +kernel
private theorem row39 : ∀ k : Fin 64, Correct (cell 39 k) := by unfold Correct;decide +kernel
private theorem row40 : ∀ k : Fin 64, Correct (cell 40 k) := by unfold Correct;decide +kernel
private theorem row41 : ∀ k : Fin 64, Correct (cell 41 k) := by unfold Correct;decide +kernel
private theorem row42 : ∀ k : Fin 64, Correct (cell 42 k) := by unfold Correct;decide +kernel
private theorem row43 : ∀ k : Fin 64, Correct (cell 43 k) := by unfold Correct;decide +kernel
private theorem row44 : ∀ k : Fin 64, Correct (cell 44 k) := by unfold Correct;decide +kernel
private theorem row45 : ∀ k : Fin 64, Correct (cell 45 k) := by unfold Correct;decide +kernel
private theorem row46 : ∀ k : Fin 64, Correct (cell 46 k) := by unfold Correct;decide +kernel
private theorem row47 : ∀ k : Fin 64, Correct (cell 47 k) := by unfold Correct;decide +kernel
private theorem row48 : ∀ k : Fin 64, Correct (cell 48 k) := by unfold Correct;decide +kernel
private theorem row49 : ∀ k : Fin 64, Correct (cell 49 k) := by unfold Correct;decide +kernel
private theorem row50 : ∀ k : Fin 64, Correct (cell 50 k) := by unfold Correct;decide +kernel
private theorem row51 : ∀ k : Fin 64, Correct (cell 51 k) := by unfold Correct;decide +kernel
private theorem row52 : ∀ k : Fin 64, Correct (cell 52 k) := by unfold Correct;decide +kernel
private theorem row53 : ∀ k : Fin 64, Correct (cell 53 k) := by unfold Correct;decide +kernel
private theorem row54 : ∀ k : Fin 64, Correct (cell 54 k) := by unfold Correct;decide +kernel
private theorem row55 : ∀ k : Fin 64, Correct (cell 55 k) := by unfold Correct;decide +kernel
private theorem row56 : ∀ k : Fin 64, Correct (cell 56 k) := by unfold Correct;decide +kernel
private theorem row57 : ∀ k : Fin 64, Correct (cell 57 k) := by unfold Correct;decide +kernel
private theorem row58 : ∀ k : Fin 64, Correct (cell 58 k) := by unfold Correct;decide +kernel
private theorem row59 : ∀ k : Fin 64, Correct (cell 59 k) := by unfold Correct;decide +kernel
private theorem row60 : ∀ k : Fin 64, Correct (cell 60 k) := by unfold Correct;decide +kernel
private theorem row61 : ∀ k : Fin 64, Correct (cell 61 k) := by unfold Correct;decide +kernel
private theorem row62 : ∀ k : Fin 64, Correct (cell 62 k) := by unfold Correct;decide +kernel
private theorem row63 : ∀ k : Fin 64, Correct (cell 63 k) := by unfold Correct;decide +kernel

private theorem pieces (j : Fin 4096) : Correct j := by
  let a : Fin 64 := ⟨j.val/64,by have := j.isLt;omega⟩
  let b : Fin 64 := ⟨j.val%64,by omega⟩
  have rows (x : Fin 64) : ∀ y, Correct (cell x y) := by
    fin_cases x
    · exact row0
    · exact row1
    · exact row2
    · exact row3
    · exact row4
    · exact row5
    · exact row6
    · exact row7
    · exact row8
    · exact row9
    · exact row10
    · exact row11
    · exact row12
    · exact row13
    · exact row14
    · exact row15
    · exact row16
    · exact row17
    · exact row18
    · exact row19
    · exact row20
    · exact row21
    · exact row22
    · exact row23
    · exact row24
    · exact row25
    · exact row26
    · exact row27
    · exact row28
    · exact row29
    · exact row30
    · exact row31
    · exact row32
    · exact row33
    · exact row34
    · exact row35
    · exact row36
    · exact row37
    · exact row38
    · exact row39
    · exact row40
    · exact row41
    · exact row42
    · exact row43
    · exact row44
    · exact row45
    · exact row46
    · exact row47
    · exact row48
    · exact row49
    · exact row50
    · exact row51
    · exact row52
    · exact row53
    · exact row54
    · exact row55
    · exact row56
    · exact row57
    · exact row58
    · exact row59
    · exact row60
    · exact row61
    · exact row62
    · exact row63
  have h : cell a b = j := Fin.ext (by dsimp [cell,a,b];omega)
  exact h ▸ rows a b

theorem low (i : Index) : (BitVec.ofNat 64 i.val <<< 52) >>> 52 = word (slot i) := by
  rw [truncate_index];exact (pieces _).1

theorem lane_value (i : Index) : lane (slot i)=BitVec.ofNat 64 (laneOf i).val := (pieces _).2.2.2

theorem query_address (i : Index) :
    5637148520 - markerBytes (slot i) = wordAddress (generatorBase-marker (groupOf i)) := by
  rw [(pieces (slot i)).2.2.1]
  exact (by decide : ∀ g : Fin 16, (5637148520 : Word) - BitVec.ofNat 64 (8*g.val) =
    wordAddress (generatorBase-(1+g.val))) ⟨(slot i).val/12%16,by omega⟩

theorem query_counter (i : Index) :
    2051+((BitVec.ofNat 64 i.val-offset (slot i)) <<< 8) + signExtend12 1845 =
      BitVec.ofNat 64 (counter (tileOf i) (groupOf i)) := by
  rw [(pieces (slot i)).2.1]
  let r := (slot i).val%192
  have hr : r ≤ i.val := by dsimp [r,slot];omega
  change (2051 : Word)+((BitVec.ofNat 64 i.val-BitVec.ofNat 64 r) <<< 8) + 1845 = _
  have diff : BitVec.ofNat 64 i.val - BitVec.ofNat 64 r = BitVec.ofNat 64 (i.val-r) := by
    have eq : BitVec.ofNat 64 (i.val-r) + BitVec.ofNat 64 r = BitVec.ofNat 64 i.val := by
      rw [←BitVec.ofNat_add,Nat.sub_add_cancel hr]
    rw [←eq];exact BitVec.add_sub_cancel _ _
  rw [diff,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 2051 + BitVec.ofNat 64 (i.val-r) * BitVec.ofNat 64 256 + BitVec.ofNat 64 1845 = _
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add,←BitVec.ofNat_add]
  apply congrArg (BitVec.ofNat 64)
  dsimp [r,slot,counter,tileOf,groupOf]
  omega

end CommitGolfCandidate.Reconstruction.OpeningIndex
