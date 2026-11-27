import CommitGolfCandidate.Stage3cLayout
import CommitGolfCandidate.Stage3cScheme
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf
open CommitGolfCandidate.Late (Levels Digest SaltTape leaf node)
def treeNode (H : Compression) (base : Nat→Digest) : Nat→Nat→Digest
  | 0,j=>base j
  | d+1,j=>parentDigest H (Binary.height d) (treeNode H base d (2*j)) (treeNode H base d (2*j+1))

def parents (H : Compression) (d : Height) (xs : List Digest) : List Digest := Binary.parentsM (M:=Id) H d xs
theorem parent_length (H : Compression) (d : Height) (xs : List Digest) : (parents H d xs).length=xs.length/2 := by
  match xs with
  | []=>rfl
  | [_]=>change 0=1/2;decide
  | l::r::rest=>
    change (parents H d rest).length+1=(rest.length+1+1)/2
    rw [parent_length H d rest];omega

theorem parent_index (H : Compression) (d : Height) (xs : List Digest) (j : Nat) (inside : 2*j+1<xs.length) :
    (parents H d xs)[j]?.getD 0=parentDigest H d (xs[2*j]?.getD 0) (xs[2*j+1]?.getD 0) := by
  match xs,j with
  | [],_ | [_],_=>simp only [List.length_cons,List.length_nil] at inside;omega
  | l::r::_,0=>exact Binary.parent_pure H d l r
  | l::r::rest,j+1=>
    simp only [List.length_cons] at inside
    change (parents H d rest)[j]?.getD 0=_
    rw [parent_index H d rest j (by omega),show 2*(j+1)=2*j+1+1 by omega,
      show 2*j+1+1+1=(2*j+1)+1+1 by omega];rfl

def initialList (H : Compression) (m : Message) (s : SaltTape) :=
  (List.finRange LENGTH).map fun i=>leaf H (i.val.testBit 0) (s i) (m i)
def layerList (H : Compression) (depth : Nat) (xs : List Digest) : Nat→List Digest
  | 0=>xs
  | n+1=>parents H (Binary.height (23-(depth-(n+1)))) (layerList H depth xs n)

theorem shifted (H : Compression) (d : Nat) (xs : List Digest) (n : Nat) :
    layerList H d (parents H (Binary.height (23-d)) xs) n=layerList H (d+1) xs (n+1) := by
  induction n with
  | zero=>simp [layerList]
  | succ n ih=>simp only [layerList] at ih ⊢;rw [ih,show d+1-(n+1+1)=d-(n+1) by omega]

def cached (H : Compression) (d : Nat) (xs : List Digest) : Levels := Binary.levelsM (M:=Id) H d xs

theorem stored_layer (H : Compression) (xs : List Digest) (d n : Nat) (hi : n≤d) :
    ((cached H d xs)[n]?).getD []=layerList H d xs n := by
  induction d generalizing xs n with
  | zero=>
    have e : n=0 := by omega
    subst n;rfl
  | succ d ih=>
    cases n with
    | zero=>rfl
    | succ n=>exact (ih _ n (by omega)).trans (shifted H d xs n)

theorem layer_width (H : Compression) (xs : List Digest) (size : xs.length=LENGTH) (n : Nat) (hi : n≤LOG_LENGTH) :
    (layerList H LOG_LENGTH xs n).length=levelCount n := by
  induction n with
  | zero=>exact size
  | succ n ih=>simp only [layerList,parent_length,ih (by omega),level_successor n (by omega)];omega

theorem layer_node (H : Compression) (xs : List Digest) (size : xs.length=LENGTH) (n j : Nat)
    (hi : n≤LOG_LENGTH) (inside : j<levelCount n) :
    (layerList H LOG_LENGTH xs n)[j]?.getD 0=treeNode H (fun k=>xs[k]?.getD 0) n j := by
  induction n generalizing j with
  | zero=>rfl
  | succ n ih=>
    have count:=level_successor n (by omega)
    have wide:=layer_width H xs size n (by omega)
    simp only [layerList,treeNode]
    rw [parent_index _ _ _ _ (by omega),ih (2*j) (by omega) (by omega),ih (2*j+1) (by omega) (by omega)]
    rw [show 23-(LOG_LENGTH-(n+1))=n by change n+1≤24 at hi;change 23-(24-(n+1))=n;omega]

theorem model_cached (H : Compression) (m : Message) (salt : SaltTape) :
    Binary.treeM (M:=Id) H m salt=cached H LOG_LENGTH (initialList H m salt) := by
  have mapId {α β : Type} (xs : List α) (f : α→β) : xs.mapM (m:=Id) f=xs.map f := by
    induction xs with
    | nil=>rfl
    | cons a l ih=>simp [List.mapM_cons,ih];rfl
  unfold Binary.treeM initialList;rw [mapId];rfl

theorem layer_size (H : Compression) (m : Message) (salt : SaltTape) (h : Nat) (bh:h≤LOG_LENGTH) :
    (((cached H LOG_LENGTH (initialList H m salt))[h]?).getD []).length=levelCount h:=by
  rw [stored_layer _ _ _ _ bh];apply layer_width _ _ _ _ bh;simp [initialList]

theorem fixed_tree_node (H : Compression) (m : Message) (salt : SaltTape) (n j : Nat) (hi : n≤LOG_LENGTH) (inside : j<levelCount n) :
    node (Binary.treeM (M:=Id) H m salt) n j=treeNode H (fun k=>(initialList H m salt)[k]?.getD 0) n j := by
  have ls:=model_cached H m salt
  rw [ls,node,stored_layer _ _ _ _ hi]
  exact layer_node H _ (by simp [initialList]) n j hi inside
end CommitGolfCandidate.Chained.BinaryMachine
