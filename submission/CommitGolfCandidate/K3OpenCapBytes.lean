import CommitGolfCandidate.K3OpenPack238
import CommitGolfCandidate.K3OpenCapSpec

/-! T238 cap bytes: the machine form `foldNodes` of the packed frontier (full groups of eight as `foldPack8`, a
trailing partial group as plain 30-byte slots), its length `capOffset`, and how it grows by one node. -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

/-- Cap bytes after `c` nodes: 30 per node, 2 less per complete group of eight. -/
def capOffset (c : Nat) : Nat := 30*c-2*(c/8)

def plain30 (v : BitVec 256) : List Byte := (digestBytes v).take 30

/-- Machine form of GQ's `packNodes`. -/
def foldNodes (values : List (BitVec 256)) : List Byte :=
  if 8 ≤ values.length then foldPack8 (fun k => values.getD k 0) ++ foldNodes (values.drop 8)
  else values.flatMap plain30
termination_by values.length
decreasing_by simp only [List.length_drop]; omega

def bytesAt (state : MachineState) (address count : Nat) : List Byte :=
  (List.range count).map fun j => state.getByte (BitVec.ofNat 64 (address+j))

theorem fold_nodes_eq (values : List (BitVec 256)) : foldNodes values =
    if 8 ≤ values.length then foldPack8 (fun k => values.getD k 0) ++ foldNodes (values.drop 8)
    else values.flatMap plain30 := by
  rw [foldNodes]

theorem fold_nodes_nil : foldNodes [] = [] := by rw [fold_nodes_eq]; simp

theorem fold_nodes_short (values : List (BitVec 256)) (short : values.length < 8) :
    foldNodes values = values.flatMap plain30 := by
  rw [fold_nodes_eq, if_neg (by omega)]

/-- Complete groups split off. -/
theorem fold_nodes_append (a b : List (BitVec 256)) (whole : a.length%8=0) :
    foldNodes (a++b)=foldNodes a++foldNodes b := by
  induction h : a.length using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    by_cases empty : n=0
    · have : a=[] := List.eq_nil_of_length_eq_zero (h.trans empty)
      subst this; simp [fold_nodes_nil]
    · have big : 8 ≤ n := by omega
      rw [fold_nodes_eq (a++b), if_pos (by simp; omega), fold_nodes_eq a, if_pos (by omega)]
      have get : (fun k => (a++b).getD k 0)=(fun k => if k<8 then a.getD k 0 else (a++b).getD k 0) := by
        funext k; split
        · simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by omega)]
        · rfl
      have pack : foldPack8 (fun k => (a++b).getD k 0)=foldPack8 (fun k => a.getD k 0) := by
        unfold foldPack8
        congr 1
        · apply List.flatMap_congr; intro k hk
          have small := List.mem_range.1 hk
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
        · simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by omega)]
      rw [pack, List.drop_append_of_le_length (by omega),
        ih (n-8) (by omega) (a.drop 8) (by simp; omega) (by simp; omega), List.append_assoc]

theorem fold_nodes_length (values : List (BitVec 256)) : (foldNodes values).length=capOffset values.length := by
  induction h : values.length using Nat.strong_induction_on generalizing values with
  | _ n ih =>
    by_cases big : 8 ≤ n
    · rw [fold_nodes_eq, if_pos (by omega), List.length_append, foldPack8_length,
        ih (n-8) (by omega) _ (by simp; omega)]
      unfold capOffset; omega
    · rw [fold_nodes_short _ (by omega)]
      have each : ∀ v ∈ values, (plain30 v).length=30 := by intro v _; simp [plain30,digestBytes]
      rw [List.length_flatMap, List.map_congr_left each]
      simp only [List.map_const', List.sum_replicate, smul_eq_mul]
      unfold capOffset; omega

/-- The partial group: `r = length % 8` plain slots after the complete groups. -/
theorem fold_nodes_tail (values : List (BitVec 256)) :
    foldNodes values=foldNodes (values.take (values.length-values.length%8))++
      (values.drop (values.length-values.length%8)).flatMap plain30 := by
  conv => lhs; rw [← List.take_append_drop (values.length-values.length%8) values]
  rw [fold_nodes_append _ _ (by rw [List.length_take]; omega),
    fold_nodes_short (values.drop (values.length-values.length%8)) (by rw [List.length_drop]; omega)]

/-- A node that does not complete a group is appended as a plain slot. -/
theorem fold_nodes_snoc_plain (values : List (BitVec 256)) (v : BitVec 256) (open_ : values.length%8≠7) :
    foldNodes (values++[v])=foldNodes values++plain30 v := by
  have cut : (values++[v]).length-(values++[v]).length%8=values.length-values.length%8 := by
    rw [List.length_append, List.length_singleton]; omega
  rw [fold_nodes_tail (values++[v]), cut, fold_nodes_tail values,
    List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega)]
  simp [List.flatMap_append]

/-- The eighth node closes its group: the group's seven plain slots and the node become one `foldPack8`. -/
theorem fold_nodes_snoc_fold (values : List (BitVec 256)) (v : BitVec 256) (closes : values.length%8=7) :
    foldNodes (values++[v])=foldNodes (values.take (values.length-7))++
      foldPack8 (fun k => (values.drop (values.length-7)++[v]).getD k 0) := by
  have whole : (values.take (values.length-7)).length%8=0 := by rw [List.length_take]; omega
  rw [show values++[v]=values.take (values.length-7)++(values.drop (values.length-7)++[v]) by
      rw [← List.append_assoc, List.take_append_drop],
    fold_nodes_append _ _ whole]
  congr 1
  have len : (values.drop (values.length-7)++[v]).length=8 := by
    rw [List.length_append, List.length_drop, List.length_singleton]; omega
  rw [fold_nodes_eq, if_pos (by omega)]
  have rest : (values.drop (values.length-7)++[v]).drop 8=[] := by
    apply List.eq_nil_of_length_eq_zero; rw [List.length_drop]; omega
  rw [rest, fold_nodes_nil, List.append_nil]

theorem cap_offset_succ (n : Nat) : capOffset (n+1)=capOffset n+(if n%8=7 then 28 else 30) := by
  unfold capOffset; split <;> omega

theorem cap_offset_group (n : Nat) : capOffset n=capOffset (n-n%8)+30*(n%8) := by
  unfold capOffset; omega

theorem bytes_at_length (state : MachineState) (address count : Nat) : (bytesAt state address count).length=count := by
  simp [bytesAt]

theorem bytes_at_append (state : MachineState) (address n m : Nat) :
    bytesAt state address (n+m)=bytesAt state address n++bytesAt state (address+n) m := by
  unfold bytesAt
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left; intro j _; simp [Nat.add_assoc]

theorem bytes_at_congr (s t : MachineState) (address count : Nat)
    (same : ∀ j<count, t.getByte (BitVec.ofNat 64 (address+j))=s.getByte (BitVec.ofNat 64 (address+j))) :
    bytesAt t address count=bytesAt s address count := by
  unfold bytesAt
  apply List.map_congr_left; intro j hj; exact same j (List.mem_range.1 hj)

theorem bytes_at_getElem (state : MachineState) (address count j : Nat) (hj : j<count) :
    (bytesAt state address count)[j]'(by simp [bytesAt]; exact hj)=state.getByte (BitVec.ofNat 64 (address+j)) := by
  simp [bytesAt]

/-- One byte of a little-endian read. -/
theorem read_byte (state : MachineState) (address count j : Nat) (hj : j<count) :
    (readBuffer state address count).extractLsb' (8*j) 8=state.getByte (BitVec.ofNat 64 (address+j)) := by
  rw [read_buffer_slice state address count j 1 (by omega)]
  apply BitVec.eq_of_toNat_eq
  have := (state.getByte (BitVec.ofNat 64 (address+j))).isLt
  simp [readBuffer, BitVec.toNat_ofNat] <;> omega

/-- The digest bytes of a 32-byte read are the bytes read. -/
theorem digest_bytes_read (state : MachineState) (address : Nat) :
    digestBytes (readBuffer state address 32)=bytesAt state address 32 := by
  apply List.ext_getElem
  · simp [digestBytes, bytesAt]
  · intro j h1 h2
    have hj : j<32 := by simpa [digestBytes] using h1
    simp only [digestBytes, List.getElem_ofFn]
    rw [bytes_at_getElem _ _ _ _ hj]
    exact read_byte state address 32 j hj

theorem plain_read (state : MachineState) (address : Nat) :
    plain30 (readBuffer state address 32)=bytesAt state address 30 := by
  unfold plain30
  rw [digest_bytes_read]
  unfold bytesAt
  rw [← List.map_take, List.take_range]; rfl

theorem half_bytes (state : MachineState) (address : Nat) :
    (halfAt state address).extractLsb' 0 8=state.getByte (BitVec.ofNat 64 address) ∧
      (halfAt state address).extractLsb' 8 8=state.getByte (BitVec.ofNat 64 (address+1)) := by
  unfold halfAt
  constructor
  · exact BitVec.extractLsb'_append_eq_right
  · exact BitVec.extractLsb'_append_eq_left

theorem half_of_read (state : MachineState) (address : Nat) :
    halfAt state (address+28)=(readBuffer state address 32).extractLsb' 224 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  unfold halfAt
  rw [BitVec.getLsbD_append]
  by_cases low : i<8
  · rw [if_pos low]
    have b := congrArg (fun x : BitVec 8 => x.getLsbD i) (read_byte state address 32 28 (by decide))
    simp only [BitVec.getLsbD_extractLsb', show i<8 from low, decide_true, Bool.true_and] at b
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    rw [← b]
  · rw [if_neg low]
    have b := congrArg (fun x : BitVec 8 => x.getLsbD (i-8)) (read_byte state address 32 29 (by decide))
    simp only [BitVec.getLsbD_extractLsb', show i-8<8 by omega, decide_true, Bool.true_and] at b
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      show address+28+1=address+29 by omega]
    rw [← b]; congr 1; omega

end TwoPermutationPrototype.GroupedOpening
