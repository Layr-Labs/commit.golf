import CommitGolfCandidate.Layout2CapTables
import CommitGolfCandidate.Layout2QuartetFormat
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf
set_option maxHeartbeats 1200000

def tag (r : Nat) := (r+6)/30
def Good (k len : Nat) : Prop :=
  534*k≤len ∧ size (tag ((len-534*k)%952))=(len-534*k)%952 ∧ (k=0 → len=0)
instance (k len) : Decidable (Good k len) := by unfold Good;infer_instance

theorem size_eq (m : Nat) : size m=30*m-2*(m/8) := by unfold size;omega
theorem split_size (f : Nat) : size f=952*(f/32)+size (f%32) := by
  have a : f/8=4*(f/32)+(f%32)/8 := by omega
  have b : f%8=(f%32)%8 := by omega
  unfold size;omega

private theorem smalls : ∀ m : Fin 32, size m.val<952 ∧ tag (size m.val)=m.val := by decide +kernel

theorem good_shape (k f : Nat) (empty : k=0 → f=0) : Good k (534*k+size f) := by
  have hs:=smalls ⟨f%32,by omega⟩
  change size (f%32)<952 ∧ tag (size (f%32))=f%32 at hs
  have remn : size f%952=size (f%32) := by rw [split_size];omega
  refine ⟨by omega,?_,?_⟩
  · simp only [Nat.add_sub_cancel_left,remn,hs.2]
  · intro z;rw [z,empty z];decide

def chunk (n j : Nat) := if j/952<n/952 then 32 else tag (n%952)
def atByte (τ : Tables) (n : Nat) (source : Nat→Byte) (j : Nat) :=
  gather τ (chunk n j) (fun u=>source (952*(j/952)+u)) (j%952)
def transform (τ : Tables) (k : Nat) (P : Proof) : Proof :=
  List.ofFn (fun i : Fin P.length =>
    if 534*k ≤ i.val then atByte τ (P.length-534*k) (fun u=>P[534*k+u]?.getD 0) (i.val-534*k)
    else P[i.val]?.getD 0)
@[simp] theorem length_transform (τ k P) : (transform τ k P).length=P.length := by simp [transform]
theorem read_transform (τ k P j) (h : j<P.length) :
    (transform τ k P)[j]?.getD 0 =
      if 534*k≤j then atByte τ (P.length-534*k) (fun u=>P[534*k+u]?.getD 0) (j-534*k)
      else P[j]?.getD 0 := by
  rw [List.getElem?_eq_getElem (by simpa using h : j<(transform τ k P).length)];simp [transform,h]

theorem at_chunk (τ : Tables) (n g j : Nat) (f : Nat→Byte) (small : j<952) :
    atByte τ n f (952*g+j) =
      gather τ (if g<n/952 then 32 else tag (n%952)) (fun x=>f (952*g+x)) j := by
  simp only [atByte,chunk,show (952*g+j)/952=g by omega,show (952*g+j)%952=j by omega]

def ValidTable (τ : Tables) := ∀ m,1≤m → m≤32 → ∀ i, i<8*size m → τ m i<8*size m
def Inverse (τ υ : Tables) := ∀ m,1≤m → m≤32 → ∀ i,i<8*size m → υ m (τ m i)=i

theorem inverse {τ υ} (wf : ValidTable τ) (inv : Inverse τ υ) (k P) (valid : Good k P.length) :
    transform τ k (transform υ k P)=P := by
  apply List.ext_getElem (by simp)
  intro a _ ha
  let Q:=transform υ k P
  let n:=P.length-534*k
  have eq:=read_transform τ k Q a (by simpa [Q] using ha)
  have qlen : Q.length=P.length := length_transform .. 
  rw [qlen] at eq
  have out : (transform τ k Q)[a]?.getD 0=P[a]?.getD 0 := by
    rw [eq]
    by_cases cap : 534*k≤a
    · rw [if_pos cap]
      let j:=a-534*k
      let g:=j/952
      let r:=chunk n j
      have jb : j<n := by dsimp [j,n];omega
      have good : size (tag (n%952))=n%952 := valid.2.1
      have geometry : 1≤r ∧ r≤32 ∧ j%952<size r ∧ 952*g+size r≤n ∧ size r≤952 := by
        dsimp [r,chunk,g]
        split
        · change 1≤32 ∧ 32≤32 ∧ j%952<952 ∧ 952*(j/952)+952≤n ∧ 952≤952;omega
        · have tb : tag (n%952)<32 := by unfold tag;omega
          have nz : tag (n%952)≠0 := by intro bad;rw [bad] at good;change 0=_ at good;omega
          omega
      change gather τ r (fun u=>Q[534*k+(952*g+u)]?.getD 0) (j%952)=P[a]?.getD 0
      apply BitVec.eq_of_getLsbD_eq
      intro b bit
      let i:=8*(j%952)+b
      let t:=τ r i
      have hf : i<8*size r := by dsimp [i];omega
      have ht : t<8*size r := wf r geometry.1 geometry.2.1 i hf
      have hb : t%8<8 := by omega
      have read:=read_transform υ k P (534*k+(952*g+t/8)) (by dsimp [n] at *;omega)
      rw [if_pos (by omega),Nat.add_sub_cancel_left,at_chunk _ _ _ _ _ (by omega)] at read
      rw [gather_bit _ _ _ _ _ bit]
      change (Q[534*k+(952*g+t/8)]?.getD 0).getLsbD (t%8)=_
      rw [read,gather_bit _ _ _ _ _ hb]
      change (P[534*k+(952*g+υ r (8*(t/8)+t%8)/8)]?.getD 0).getLsbD (υ r (8*(t/8)+t%8)%8)=_
      rw [show 8*(t/8)+t%8=t by omega,show υ r t=i from inv r geometry.1 geometry.2.1 i hf]
      rw [show 534*k+(952*g+i/8)=a by dsimp [g,i,j];omega,show i%8=b by dsimp [i];omega]
    · rw [if_neg cap,read_transform υ k P a ha,if_neg cap]
  simpa only [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem (show a<(transform τ k Q).length by simpa [Q] using ha),Option.getD_some] using out

def decoder (p : Positions) (P : Proof) := Quartet.decoder p (transform dec p.card P)
def encoder (p : Positions) (P : Proof) := transform enc p.card (Quartet.encoder p P)
@[simp] theorem decoder_len (p P) : (decoder p P).length=P.length := by simp [decoder]
@[simp] theorem encoder_len (p P) : (encoder p P).length=P.length := by simp [encoder]

end CommitGolfCandidate.Layout2.Cap
