import CommitGolfCandidate.CapBFormat
import CommitGolfCandidate.CapBRaw
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.GroupedOpening (capOffset foldNodes fold_nodes_append fold_nodes_length)
open TwoPermutationPrototype.GroupedOpening.CapB (flushBytes)
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

theorem join_stream (xs ys : List D) (whole : xs.length%32=0) (initial : Word) :
    let p:=stream initial xs
    let q:=stream p.carry ys
    (stream initial (xs++ys)).out=p.out++q.out ∧ (stream initial (xs++ys)).carry=q.carry := by
  induction ys using List.reverseRecOn with
  | nil=>simp [stream,emptyStream]
  | append_singleton ys d ih=>
    simp only [←List.append_assoc,stream_snoc,push,stream_count,List.length_append]
    have phase : (xs.length+ys.length)%32=ys.length%32 := by omega
    simp only [phase,ih.1,ih.2,List.append_assoc,and_self]

theorem join_capRaw (xs ys : List D) (whole : xs.length%32=0) :
    capRaw (xs++ys)=capRaw xs++capRaw ys := by
  obtain ⟨out,acc⟩:=join_stream xs ys whole 0
  rw [←capRaw_seed 0,←capRaw_seed 0 xs,←capRaw_seed (stream 0 xs).carry ys]
  simp only [capBytes,out,acc,List.flatMap_append,List.length_append,whole,show flushBytes 0=0 from rfl,
    List.take_zero,List.append_nil,List.append_assoc,show (xs.length+ys.length)%32=ys.length%32 by omega]

def canonicalBlock (ds : List D) (j : Nat) := Layout2.gather Layout2.Cap.enc ds.length (fun a=>(foldNodes ds)[a]?.getD 0) j
def HonestBlock (ds : List D) := ∀ j,j<Layout2.Cap.size ds.length → (capRaw ds)[j]?.getD 0=canonicalBlock ds j
theorem format_length (ds : List D) : (foldNodes ds).length=Layout2.Cap.size ds.length := by
  rw [fold_nodes_length,Layout2.Cap.size_eq];rfl

/-- A local table only reads the bytes of its own group. -/
theorem gather_congr (m j : Nat) (a b : Nat→Byte) (room : j<Layout2.Cap.size m)
    (bounded : ∀ i,i<8*Layout2.Cap.size m → Layout2.Cap.enc m i<8*Layout2.Cap.size m)
    (same : ∀ i,i<Layout2.Cap.size m → a i=b i) :
    Layout2.gather Layout2.Cap.enc m a j=Layout2.gather Layout2.Cap.enc m b j := by
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  rw [Layout2.gather_bit _ _ _ _ _ hi,Layout2.gather_bit _ _ _ _ _ hi,same _ (by have:=bounded (8*j+i) (by omega);omega)]

theorem all_blocks (localProof : ∀ ds : List D, ds.length≤32 → (∀ v∈ds,v.extractLsb' 238 18=0) → HonestBlock ds)
    (bounded : Layout2.Cap.ValidTable Layout2.Cap.enc) (ds : List D) (clean : ∀ v∈ds,v.extractLsb' 238 18=0) :
    ∀ g j,j<952 → 952*g+j<capOffset ds.length →
    (capRaw ds)[952*g+j]?.getD 0=Layout2.gather Layout2.Cap.enc
      (if g<capOffset ds.length/952 then 32 else Layout2.Cap.tag (capOffset ds.length%952))
      (fun u=>(foldNodes ds)[952*g+u]?.getD 0) j := by
  intro g j hj live
  have sz : capOffset ds.length=Layout2.Cap.size ds.length := (Layout2.Cap.size_eq _).symm
  let pre:=ds.take (32*g);let rest:=ds.drop (32*g)
  let chunk:=rest.take 32;let tail:=rest.drop 32
  have blockBound : ∀ m : Fin 32, Layout2.Cap.size m.val<952 ∧ Layout2.Cap.tag (Layout2.Cap.size m.val)=m.val := by decide +kernel
  have rem:=blockBound ⟨ds.length%32,by omega⟩
  change Layout2.Cap.size (ds.length%32)<952 ∧ _=ds.length%32 at rem
  have split:=Layout2.Cap.split_size ds.length
  have gfit : 32*g≤ds.length := by omega
  have prelen : pre.length=32*g := by simp [pre,Nat.min_eq_left gfit]
  have rn : rest.length=ds.length-32*g := by simp [rest]
  have cn : chunk.length=min 32 rest.length := by simp [chunk]
  have pl : Layout2.Cap.size pre.length=952*g := by rw [prelen];unfold Layout2.Cap.size;omega
  have p32 : pre.length%32=0 := by omega
  have p8 : pre.length%8=0 := by omega
  have decomp : pre++rest=ds := List.take_append_drop _ _
  have decomp' : chunk++tail=rest := List.take_append_drop _ _
  have agree : capRaw rest=capRaw chunk++capRaw tail ∧ foldNodes rest=foldNodes chunk++foldNodes tail := by
    by_cases full : 32≤rest.length
    · have l : chunk.length=32 := by omega
      rw [←decomp'];exact ⟨join_capRaw _ _ (by omega),fold_nodes_append _ _ (by omega)⟩
    · have n : tail=[] := List.eq_nil_of_length_eq_zero (by simp [tail];omega)
      have c : chunk=rest := List.take_of_length_le (by omega)
      rw [n,c,TwoPermutationPrototype.GroupedOpening.fold_nodes_nil,show capRaw []=[] from rfl];simp
  have item:=localProof chunk (by omega) (fun v hv=>clean v (List.mem_of_mem_drop (List.mem_of_mem_take hv)))
  have shape : chunk.length=(if g<capOffset ds.length/952 then 32 else Layout2.Cap.tag (capOffset ds.length%952)) ∧ j<Layout2.Cap.size chunk.length := by
    by_cases long : g<ds.length/32
    · have l : chunk.length=32 := by omega
      rw [l,if_pos (by omega)];exact ⟨rfl,hj⟩
    · have eq : chunk.length=ds.length%32 := by omega
      rw [eq,if_neg (by omega),show capOffset ds.length%952=Layout2.Cap.size (ds.length%32) by omega]
      exact ⟨rem.2.symm,by omega⟩
  have nonempty : 1≤chunk.length := by
    by_contra! bad
    have zero : chunk.length=0 := by omega
    have badj:=shape.2;rw [zero] at badj;exact Nat.not_lt_zero j badj
  have get (xs ys : List Byte) (idx : Nat) (len : xs.length=952*g) :
      (xs++ys)[952*g+idx]?=ys[idx]? := by rw [List.getElem?_append_right (by omega),show 952*g+idx-xs.length=idx by omega]
  rw [←decomp,join_capRaw _ _ p32,get _ _ _ ((capRaw_length _).trans pl),agree.1,List.getElem?_append_left (by rw [capRaw_length];exact shape.2)]
  rw [item _ shape.2];unfold canonicalBlock
  rw [decomp,←shape.1]
  apply gather_congr _ _ _ _ shape.2 (bounded _ nonempty (by omega))
  intro u valid
  rw [←decomp,fold_nodes_append _ _ p8,get _ _ _ ((format_length _).trans pl),agree.2,List.getElem?_append_left (by rwa [format_length])]
end CommitGolfCandidate.CapB
