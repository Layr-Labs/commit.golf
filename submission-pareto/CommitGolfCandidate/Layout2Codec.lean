import CommitGolf.Programs

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

abbrev Tables := Nat → Nat → Nat
def tableOffset (r : Nat) : Nat := if r=4 then 0 else if r=1 then 34176 else if r=2 then 42720 else 59808
def WellFormed (τ : Tables) := ∀ r, 1≤r → r≤4 → ∀ i, i<4272*r → τ r i<4272*r
def identityTable : Tables := fun _ i => i
theorem identity_wellFormed : WellFormed identityTable := fun _ _ _ _ h => h

/-- A word with just the selected source bit placed in the requested output lane. -/
def piece (source : Nat → Byte) (fromBit lane : Nat) : Word :=
  ((((source (fromBit/8)).zeroExtend 64 >>> (fromBit%8)) &&& 1) <<< lane)
def acc (τ : Tables) (r : Nat) (source : Nat → Byte) (j : Nat) : Nat → Word
  | 0 => 0
  | n+1 => acc τ r source j n ||| piece source (τ r (8*j+n)) n
def gather (τ : Tables) (r : Nat) (source : Nat → Byte) (j : Nat) : Byte :=
  (acc τ r source j 8).truncate 8

theorem piece_bit (source : Nat → Byte) (src lane i : Nat) (inWord : i<64) :
    (piece source src lane).getLsbD i =
      (decide (i=lane) && (source (src/8)).getLsbD (src%8)) := by
  by_cases e : i=lane
  · subst i
    simp [piece,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_and,BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth,inWord,show src%8<64 by omega,show src%8<8 from Nat.mod_lt _ (by decide)]
  · by_cases below : i<lane
    · simp [piece,BitVec.getLsbD_shiftLeft,below,e]
    · have pos : 0 < (i-lane) := by omega
      have one : (1#64).getLsbD (i-lane)=false := by
        rw [show (1#64)=BitVec.ofNat 64 1 from rfl,BitVec.getLsbD_ofNat]
        rw [show (1:Nat)=2^1-1 from rfl,Nat.testBit_two_pow_sub_one]
        simp [show ¬i-lane<1 by omega]
      simp [piece,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_and,below,e,one]

theorem acc_bit (τ : Tables) (r : Nat) (source : Nat → Byte) (j n i : Nat) (inWord : i<64) :
    (acc τ r source j n).getLsbD i =
      (decide (i<n) && (source (τ r (8*j+i)/8)).getLsbD (τ r (8*j+i)%8)) := by
  induction n with
  | zero => simp [acc]
  | succ n ih =>
    rw [acc,BitVec.getLsbD_or,ih,piece_bit _ _ _ _ inWord]
    by_cases h : i<n
    · simp [h,show i≠n by omega,show i<n+1 by omega]
    · by_cases e : i=n
      · subst i;simp
      · simp [h,e,show ¬i<n+1 by omega]

theorem gather_bit (τ : Tables) (r : Nat) (source : Nat → Byte) (j i : Nat) (small : i<8) :
    (gather τ r source j).getLsbD i=(source (τ r (8*j+i)/8)).getLsbD (τ r (8*j+i)%8) := by
  simp [gather,BitVec.getLsbD_setWidth,acc_bit τ r source j 8 i (by omega),small]

theorem gather_id (r : Nat) (source : Nat → Byte) (j : Nat) :
    gather identityTable r source j=source j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [gather_bit _ _ _ _ _ hi]
  simp only [identityTable,show (8*j+i)/8=j by omega,show (8*j+i)%8=i by omega]

def blockSize (k block : Nat) := if block<k/4 then 4 else k%4
def convertAt (τ : Tables) (k : Nat) (source : Nat → Byte) (j : Nat) : Byte :=
  if j<534*k then
    gather τ (blockSize k (j/2136)) (fun b => source (2136*(j/2136)+b)) (j%2136)
  else source j

def convert (τ : Tables) (k : Nat) (p : Proof) : Proof :=
  List.ofFn fun i : Fin p.length => convertAt τ k (fun j => p[j]?.getD 0) i

@[simp] theorem convert_length (τ : Tables) (k : Nat) (p : Proof) :
    (convert τ k p).length=p.length := by simp [convert]

@[simp] theorem convert_id (k : Nat) (p : Proof) : convert identityTable k p=p := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [convert,List.getElem_ofFn,convertAt]
  split
  · rw [gather_id,show 2136*(i/2136)+i%2136=i by omega];simp [h2]
  · simp [h2]

theorem gather_congr {τ : Tables} (wf : WellFormed τ) {r j : Nat} (lo : 1≤r) (hi : r≤4) (inside : j<534*r)
    {x y : Nat→Byte} (agree : ∀ q, q<534*r → x q=y q) : gather τ r x j=gather τ r y j := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  rw [gather_bit _ _ _ _ _ hb,gather_bit _ _ _ _ _ hb,agree _ (by have:=wf r lo hi (8*j+b) (by omega);omega)]

theorem at_block (τ : Tables) (k g r j : Nat) (f : Nat→Byte) (inside : j<534*r)
    (limit : g≤k/4) (mult : r=blockSize k g) :
    convertAt τ k f (2136*g+j)=gather τ r (fun q=>f (2136*g+q)) j := by
  have rBound : r≤4 := by rw [mult];unfold blockSize;split <;> omega
  have room : 2136*g+j<534*k := by rw [mult] at inside;unfold blockSize at inside;split at inside <;> omega
  simp only [convertAt,if_pos room, show (2136*g+j)/2136=g by omega, show (2136*g+j)%2136=j by omega,←mult]

/-- The encoder table supplies the inverse lookup on every bit the decoder can select. -/
def RightInverse (dec enc : Tables) :=
  ∀ r, 1≤r → r≤4 → ∀ i, i<4272*r → enc r (dec r i)=i

theorem gather_inverse {dec enc : Tables} (wf : WellFormed dec) (inv : RightInverse dec enc)
    (source : Nat→Byte) (r j : Nat) (lo : 1≤r) (hi : r≤4) (inBlock : j<534*r) :
    gather dec r (gather enc r source) j=source j := by
  apply BitVec.eq_of_getLsbD_eq
  intro b small
  let i:=8*j+b
  let h:=dec r i
  have hsmall : h%8<8 := Nat.mod_lt _ (by decide)
  have iBound : i<4272*r := by dsimp [i];omega
  have back : enc r h=i := inv _ lo hi _ iBound
  rw [gather_bit _ _ _ _ _ small]
  change (gather enc r source (h/8)).getLsbD (h%8)=_
  rw [gather_bit _ _ _ _ _ hsmall,show 8*(h/8)+h%8=h by omega,back]
  simp only [i,show (8*j+b)/8=j by omega,show (8*j+b)%8=b by omega]

theorem convert_read (τ : Tables) (k : Nat) (p : Proof) (j : Nat) (inside : j<p.length) :
    (convert τ k p)[j]?.getD 0=convertAt τ k (fun n=>p[n]?.getD 0) j := by
  rw [List.getElem?_eq_getElem (by simpa using inside : j<(convert τ k p).length)]
  simp [convert]

/-- Decode an encoded proof, for every complete record prefix and arbitrary trailing bytes.
Only a right inverse is required. -/
theorem convert_roundtrip {dec enc : Tables} (wf : WellFormed dec) (inv : RightInverse dec enc)
    (k : Nat) (p : Proof) (complete : 534*k≤p.length) :
    convert dec k (convert enc k p)=p := by
  apply List.ext_getElem (by simp)
  intro j _ inside
  let input := fun n : Nat => p[n]?.getD 0
  let encoded := fun n : Nat => (convert enc k p)[n]?.getD 0
  simp only [convert,List.getElem_ofFn]
  change convertAt dec k encoded j=p[j]
  by_cases hit : j<534*k
  · let g:=j/2136
    let r:=blockSize k g
    let b:=j%2136
    have lim : g≤k/4 := by dsimp [g];omega
    have range : 0<r ∧ r≤4 ∧ b<534*r ∧ 2136*g+534*r≤534*k := by
      unfold r blockSize b g;split <;> omega
    have atJ : 2136*g+b=j := by dsimp [g,b];omega
    have head := at_block dec k g r b encoded range.2.2.1 lim rfl
    rw [atJ] at head
    rw [head]
    have same (i : Nat) (hi : i<534*r) :
        encoded (2136*g+i)=gather enc r (fun q=>input (2136*g+q)) i := by
      have valid : 2136*g+i<p.length := by omega
      exact (convert_read enc k p _ valid).trans (at_block enc k g r i input hi lim rfl)
    rw [gather_congr wf range.1 range.2.1 range.2.2.1 same,
      gather_inverse wf inv _ r b range.1 range.2.1 range.2.2.1,atJ]
    simp [input,inside]
  · rw [convertAt,if_neg hit]
    change (convert enc k p)[j]?.getD 0=_
    rw [convert_read enc k p j inside,convertAt,if_neg hit]
    simp [inside]

end CommitGolfCandidate.Layout2
