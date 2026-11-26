import CommitGolfCandidate.S5PathAddress
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf RiscvZkvm.Rv64
open CommitGolfCandidate.Late (Levels SaltTape node bytes)

def ordinaryField (x : S5.Field) : Proof := (List.range (x.1/8)).map fun j=>BitVec.ofNat 8 (x.2/2^(8*j))
def bottomSibling (t : Levels) (i : Index) (k : Nat) := node t 0 (3*(i.val/3)+((i.val%3+k)%3))
def normalBytes (t : Levels) (s : SaltTape) (i : Index) : Proof :=
  bytes (n:=24) (s i) ++ bytes (n:=32) (bottomSibling t i 1) ++ bytes (n:=32) (bottomSibling t i 2) ++ pathBytes t i 1 23

private theorem word_field (n : Nat) (v : BitVec (8*n)) : ordinaryField (8*n,v.toNat)=bytes (n:=n) v := by
  apply List.ext_getElem
  · simp [ordinaryField,bytes]
  · intro j _ _
    simp only [ordinaryField,List.getElem_map,List.getElem_range,bytes,List.getElem_ofFn]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

private theorem binary_index (n : Nat) : 2*(n/2)+(n%2+1)%2=n ^^^ 1 := by
  by_cases even : n%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)];omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))];omega

def ordinaryLayer (t : Levels) (i : Index) (h : Nat) : List S5.Field :=
  (List.range (S4.radix h-1)).map fun n=>(256,(node t h (S4.radix h*S4.nodeIndex i.val (h+1)+(S4.childPos i.val h+n+1)%S4.radix h)).toNat)

private theorem binary_bytes (t : Levels) (i : Index) (h : Nat) (pos : 0<h) :
    (ordinaryLayer t i h).flatMap ordinaryField=bytes (n:=32) (node t h (mate i h)) := by
  have radix : S4.radix h=2:=if_neg (by omega)
  unfold ordinaryLayer
  rw [S4.nextIndex,S4.childPos,radix]
  simp only [show List.range (2-1)=[0] by decide,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,Nat.add_zero,binary_index]
  exact word_field 32 _

private theorem ternary_bytes (t : Levels) (i : Index) :
    (ordinaryLayer t i 0).flatMap ordinaryField=bytes (n:=32) (bottomSibling t i 1)++bytes (n:=32) (bottomSibling t i 2) := by
  unfold ordinaryLayer
  simp only [show List.range (S4.radix 0-1)=[0,1] by decide,List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,S4.nodeIndex,S4.childPos,S4.span,S4.radix,Nat.zero_add,Nat.add_zero,Nat.div_one,pow_zero,Nat.mul_one,↓reduceIte]
  rw [show List.range (3-1)=[0,1] by decide]
  simp only [List.map_cons,List.map_nil,List.flatMap_cons,List.flatMap_nil,List.append_nil,Nat.add_zero,Nat.add_assoc]
  change ordinaryField (256,(bottomSibling t i 1).toNat)++ordinaryField (256,(bottomSibling t i 2).toNat)=_
  rw [word_field 32 _,word_field 32 _]

theorem normal_record (t : Levels) (s : SaltTape) (i : Index) :
    (S5.record t s i false).flatMap ordinaryField=normalBytes t s i := by
  change ordinaryField (192,(s i).toNat)++((List.range 24).flatMap (ordinaryLayer t i)).flatMap ordinaryField=_
  rw [word_field 24 (s i),List.flatMap_assoc,show List.range 24=0::List.range' 1 23 by decide,List.flatMap_cons,ternary_bytes]
  unfold normalBytes pathBytes
  simp only [List.append_assoc]
  apply congrArg (fun bs=>bytes (n:=24) (s i)++(bytes (n:=32) (bottomSibling t i 1)++(bytes (n:=32) (bottomSibling t i 2)++bs)))
  rw [List.flatMap_def,List.flatMap_def]
  congr 1;apply List.map_congr_left
  intro j hj
  have pos:=List.mem_range'.mp hj
  exact binary_bytes t i j (by omega)

theorem normal_length (t s i) : (normalBytes t s i).length=824 := by
  simp [normalBytes,bytes,path_len]

theorem normal_opening (t : Levels) (s : SaltTape) (ps : Positions) (normal : ps.card≠BATCH) :
    S5.opening t s ps=(indices ps).flatMap (normalBytes t s) := by
  change (if ps.card=BATCH then _ else _)=_
  rw [if_neg normal,List.flatMap_def,List.flatMap_def];congr 1;apply List.map_congr_left
  intro i _;exact normal_record t s i
end CommitGolfCandidate.S5Machine.Open
