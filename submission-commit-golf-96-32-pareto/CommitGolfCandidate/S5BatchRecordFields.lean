import CommitGolfCandidate.S5BatchTernary
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf RiscvZkvm.Rv64
open Late (Levels SaltTape node)
open Writer (widths)

def batchLayer (t : Levels) (i : Index) (h : Nat) : List S5.Field :=
  (List.range (S4.radix h-1)).map fun n=>(S5.bits h,(node t h (S4.radix h*S4.nodeIndex i.val (h+1)+(S4.childPos i.val h+n+1)%S4.radix h)).toNat)
private theorem binary_peer (j : Nat) : 2*(j/2)+(j%2+1)%2=j ^^^ 1 := by
  by_cases even : j%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)];omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))];omega
private theorem layer_above (t : Levels) (i : Index) (h : Nat) (pos : 0<h) : batchLayer t i h=[siblingField t i h] := by
  rw [batchLayer,S4.nextIndex,S4.childPos,show S4.radix h=2 from if_neg (by omega)]
  simp only [show List.range (2-1)=[0] by decide,List.map_cons,List.map_nil,Nat.add_zero,binary_peer]
  rfl

theorem batch_record_fields (t : Levels) (s : SaltTape) (i : Index) :
    S5.record t s i true=(192,(s i).toNat)::(peerFields t i++binaryFields t i 0 14) := by
  change _::(List.range 15).flatMap (batchLayer t i)=_
  rw [show List.range 15=0::List.range' 1 14 by decide,List.flatMap_cons]
  have first : batchLayer t i 0=peerFields t i := by
    simp [batchLayer,peerFields,bottomField,bottomSibling,S4.radix,S4.childPos,S4.nodeIndex,S4.span,
      show List.range (3-1)=[0,1] by decide,S5.bits,Nat.add_assoc]
  rw [first];congr 2
  unfold binaryFields
  trans (List.range' 1 14).flatMap (fun h=>[siblingField t i h])
  · rw [List.flatMap_def,List.flatMap_def];congr 1;apply List.map_congr_left;intro h mem
    have hi:=List.mem_range'.mp mem;exact layer_above t i h (by omega)
  · rfl
theorem batch_record_width (t s i) : widths (S5.record t s i true)=4030 := by
  unfold widths;rw [Writer.record_widths];decide +kernel
theorem upper_width (t i) : widths (binaryFields t i 0 14)=3326 := by
  have eq:=batch_record_width t (fun _=>0) i
  rw [batch_record_fields] at eq
  simpa only [widths,peerFields,bottomField,List.cons_append,List.nil_append,List.map_cons,List.sum_cons] using
    (show widths (binaryFields t i 0 14)=3326 by
      simp only [widths,peerFields,bottomField,List.cons_append,List.nil_append,List.map_cons,List.sum_cons] at eq ⊢;omega)
end CommitGolfCandidate.S5Machine.Open
