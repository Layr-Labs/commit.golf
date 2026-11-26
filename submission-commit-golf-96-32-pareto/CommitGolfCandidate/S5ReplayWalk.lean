import CommitGolfCandidate.S5ReplayCode
import CommitGolfCandidate.S5HonestTree
namespace CommitGolfCandidate.S5.Replay
open CommitGolf OracleComp
open Chained (Input Output Height LayerStep children nextNode stageInput workClass calls parentQueries parentDigest)
open Chained.Replay (PublicRow rowReads rowPath)
def leafCode (odd : Bool) (s : Late.Salt) (v : Entry) : Code 4 Output :=
  join (ask (Late.firstBlock v)) fun u=>join (ask (Late.middleBlock v u)) fun a=>
    join (ask (Late.lastBlock v)) fun b=>ask (Late.finalBlock odd s a b)
theorem leaf_values (H : Compression) (odd : Bool) (s : Late.Salt) (v : Entry) :
    (leafCode odd s v).value H=Late.leaf H odd s v ∧ (leafCode odd s v).inputs H=Late.inputs H odd s v := ⟨rfl,rfl⟩

def chainCode (h : Height) (l r : Output) : (n : Nat)→Code (n+1) Output
  | 0=>ask (Chained.pack (.inl (workClass h,r++l)))
  | n+1=>join (chainCode h l r n) fun prev=>ask (Chained.encodeNext (workClass h) (n+1) prev)
theorem chain_value (H : Compression) (h : Height) (l r : Output) (n : Nat) :
    (chainCode h l r n).value H=H (stageInput H h l r n) ∧ (chainCode h l r n).inputs H=parentQueries H h l r n := by
  induction n with
  | zero=>exact ⟨rfl,rfl⟩
  | succ n ih=>
    simp only [chainCode,join,ask,ih.1,ih.2,stageInput,parentQueries,List.getLastD_concat];exact ⟨rfl,trivial⟩
def parentCode (h : Height) (l r : Output) : Code (calls h) Output :=
  widen (map (Chained.storeReply h) (chainCode h l r (calls h-1))) (by have :=Chained.calls_positive h;omega)
theorem parent_values (H : Compression) (h : Height) (l r : Output) :
    (parentCode h l r).value H=parentDigest H h l r ∧ (parentCode h l r).inputs H=Chained.queries H h l r := by
  obtain ⟨v,qs⟩:=chain_value H h l r (calls h-1)
  constructor
  · exact congrArg (Chained.storeReply h) v
  · exact (map_inputs ..).trans qs

theorem prefix_mem (H : Compression) (h : Height) (l r : Output) (n j : Nat) (inside : j≤n) :
    stageInput H h l r j∈parentQueries H h l r n := by
  induction n with
  | zero=>
    have z : j=0:=by omega
    subst j;exact List.mem_singleton_self _
  | succ n ih=>
    by_cases eq : j=n+1
    · subst j;unfold stageInput;rw [parentQueries,List.getLastD_concat];exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (ih (by omega))

def weight (path : List LayerStep):=(path.map (fun s=>calls s.height)).sum
def walkCode (x : Output) : (path : List LayerStep)→Code (weight path) Output
  | []=>done x
  | step::path=>
    let c:=children step.right x step.sibling
    join (parentCode step.height c.1 c.2) (fun y=>walkCode y path)
theorem walk_value (H : Compression) (x : Output) (path : List LayerStep) :
    (walkCode x path).value H=Chained.walk H x path := by
  induction path generalizing x with
  | nil=>rfl
  | cons s rest ih=>simp only [walkCode,Chained.walk,join,(parent_values ..).1,nextNode,ih]

theorem walk_rows (H : Compression) (x : Output) (path : List LayerStep) (table : List PublicRow)
    (inc : ∀ q∈(walkCode x path).inputs H,PublicRow.compression q (H q)∈table) : rowPath table H x path := by
  induction path generalizing x with
  | nil=>trivial
  | cons s rest ih=>
    let c:=children s.right x s.sibling
    let h:=s.height
    have input : (walkCode x (s::rest)).inputs H=Chained.queries H h c.1 c.2++(walkCode (nextNode H x s) rest).inputs H:=by
      simp only [walkCode,join,(parent_values ..).2,(parent_values ..).1];rfl
    rw [input] at inc
    refine ⟨?_,ih _ (fun q hq=>inc q (List.mem_append_right _ hq))⟩
    intro j hj;apply inc;apply List.mem_append_left
    exact prefix_mem H h c.1 c.2 _ j (by change j<calls h at hj;omega)

def stepOf (i : Index) (peers : Nat→Peers) (n : Nat) : LayerStep :=
  ⟨height n,(S4.nodeIndex i.val n).testBit 0,(peers n).1⟩
def pathOf (i : Index) (peers : Nat→Peers) (h n : Nat) := (List.range' h n).map (stepOf i peers)
private theorem binary_output (H : Compression) (h : Nat) (l r : Output) (pos : 0<h) :
    Auth.compressRow H (h+1) (Late.parentBlock l r)=parentDigest H (height h) l r := by
  have cell : Auth.row h l r 0=Late.parentBlock l r := by unfold Auth.row;split <;> rfl
  rw [←cell,Auth.row_parent];cases h <;> first | omega | rfl
theorem next_value (H : Compression) (i : Index) (data : Nat→Peers) (v : Output) (h : Nat) (hi : 0<h) :
    nextNode H v (stepOf i data h)=Auth.compressRow H (h+1) (payload (lane h (S4.nodeIndex i.val h)) v (data h)) := by
  let j:=S4.nodeIndex i.val h
  have nh : h+1≠1:=by omega
  change parentDigest H (height h) (children (j.testBit 0) v (data h).1).1 (children (j.testBit 0) v (data h).1).2=_
  by_cases even : j%2=0
  · have side : j.testBit 0=false:=by simp [Nat.testBit_eq_decide_div_mod_eq,even]
    simp only [side,children,Bool.false_eq_true,ite_false,lane,show h≠0 by omega,show S4.nodeIndex i.val h%2=0 from even,ite_true,payload]
    exact (binary_output H h _ _ hi).symm
  · have side : j.testBit 0=true:=by simp [Nat.testBit_eq_decide_div_mod_eq,show j%2=1 by omega]
    simp only [side,children,ite_true,lane,show h≠0 by omega,show ¬S4.nodeIndex i.val h%2=0 from even,ite_false,payload]
    exact (binary_output H h _ _ hi).symm

theorem model_walk (H : Compression) (i : Index) (base : Output) (data : Nat→Peers) (h n : Nat) (positive : 0<h) :
    Chained.walk H (Auth.walk H i.val base data h) (pathOf i data h n)=Auth.walk H i.val base data (h+n) := by
  induction n generalizing h with
  | zero=>rfl
  | succ n ih=>
    simp only [pathOf,List.range'_succ,List.map_cons,Chained.walk,next_value H i data _ h positive]
    change Chained.walk H (Auth.walk H i.val base data (h+1)) (pathOf i data (h+1) n)=_
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using ih (h+1) (by omega)
end CommitGolfCandidate.S5.Replay
