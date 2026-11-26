import CommitGolfCandidate.ReconstructedCheckHonestRadix

namespace CommitGolfCandidate.Reconstruction.CheckHonestWalk
open CommitGolf Binding CheckWalkValues CheckHonestRadix Encoding Wire
open CheckPairPhysical
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000

theorem canonical (o : Oracle) (key : Generator.Key) (msg : Message) : RecordDigits.canonical (LeafTree.tree o key msg) := by
  intro d j
  exact CommitParents.node_canonical _ _ d.val j (by have := d.isLt;omega) (LeafTree.canonical o key msg)

theorem parent (o : Oracle) (key : Generator.Key) (msg : Message) (idx : Index) (d : Nat) (bound : d<24) :
    let tree := LeafTree.tree o key msg
    let p := sides (side idx (d+1)) (tree (d+1) (heap idx (d+1))) (tree (d+1) (sibling idx (d+1)))
    Binding.parent (oracleCompression o) d p.1 p.2=tree d (heap idx d) := by
  let n := heap idx (d+1)
  let h := heap idx d
  have half : n/2=h := by
    unfold n h heap;rw [Nat.div_div_eq_div_mul,←Nat.pow_succ,show (24-(d+1)).succ=24-d by omega]
  have sib : sibling idx (d+1)=n ^^^ 1 := by unfold sibling n heap;rw [Nat.shiftRight_eq_div_pow]
  have bit : side idx (d+1)=n.testBit 0 := by
    unfold side n heap
    rw [Nat.testBit_div_two_pow,Nat.zero_add,Nat.testBit_two_pow_add_gt (by omega : 24-(d+1)<24)]
  have test : n.testBit 0=decide (n%2=1) := by rw [Nat.testBit_eq_decide_div_mod_eq];simp
  let tree := LeafTree.tree o key msg
  have step : tree d h=Binding.parent (oracleCompression o) d (tree (d+1) (2*h)) (tree (d+1) (2*h+1)) :=
    CommitParents.parent_eq _ _ d h bound
  change Binding.parent _ d (sides _ (tree _ n) (tree _ _)).1 (sides _ (tree _ n) (tree _ _)).2=tree d h
  rw [step,sib,bit,test]
  rcases Nat.mod_two_eq_zero_or_one n with even|odd
  · have no : ¬n%2=1 := by omega
    simp only [sides,decide_eq_false no,Bool.false_eq_true,ite_false,Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    rw [show n=2*h by omega]
  · simp only [sides,decide_eq_true odd,ite_true,Nat.xor_one_of_odd (Nat.odd_iff.mpr odd)]
    rw [show n-1=2*h by omega,show n=2*h+1 by omega]

theorem run (o : Oracle) (key : Generator.Key) (msg : Message) (idx : Index) (k : Nat) (bound : k≤15)
    (a b : List Wire.Field) (v : View) (bits : Nat)
    (stream : bits=Wire.pack (a++(rows (LeafTree.tree o key msg) idx k++b)))
    (c : v.cursor=Wire.bits a) (size : v.header.length=4) (small : bounded v.header)
    (rad : HonestDivision.assemble 0 v.header=number (LeafTree.tree o key msg) idx k)
    (node : v.node=LeafTree.tree o key msg (9+k) (heap idx (9+k))) :
    let out := (CheckWalk.evaluate o idx bits k v).1
    out.header=[0,0,0,0] ∧ out.node=LeafTree.tree o key msg 9 (heap idx 9) := by
  induction k generalizing a v with
  | zero => exact ⟨zero v.header size rad,node⟩
  | succ k ih =>
    have h : k<15 := by omega
    let t := LeafTree.tree o key msg
    let d := 10+k
    let i := CheckWalk.idx15 k
    let siblingValue := t d (sibling idx d)
    let fs := lowFields siblingValue (lows d)
    let tail := rows t idx k++b
    have dc : (CheckLowerRound.depth i).val=9+k := by
      change 9+k%15=9+k;rw [Nat.mod_eq_of_lt h]
    have nextDepth : (CheckLowerRound.depth i).val+1=d := by dsimp only [d];omega
    have field := width k h
    have sep := splitHeader t (canonical o key msg) idx k h v.header size small rad
    have path : bits=Wire.pack ((a++fs)++tail) := by
      rw [stream];simp only [List.append_assoc,rows,fs,tail,siblingValue,t,d]
    have sib : CheckLowerInput.sibling bits v.cursor (CheckMixed.width i) (CheckMixed.out i v.header).2=siblingValue := by
      rw [path,c,field.1,sep.2.2.2];exact CheckHonestFields.sibling a tail siblingValue (lows d) field.2.2
    let nxt := (prep o idx bits i v).1
    have parent' : nxt.node=t (9+k) (heap idx (9+k)) := by
      change Binding.parent _ _ (sides _ v.node _).1 (sides _ v.node _).2=_
      rw [sib,dc,node]
      dsimp only [siblingValue]
      rw [show d=9+k+1 by unfold d;omega]
      exact parent o key msg idx (9+k) (by omega)
    have bitsNext : Wire.bits (a++fs)=v.cursor+CheckMixed.width i := by
      rw [Wire.bits_append,c,field.1,show Wire.bits fs=192+(lows d-192) from Encoding.low_bits _ _]
      change _+(192+(lows (10+k)-192))=_+lows (10+k)
      omega
    have rest := ih (by omega) (a++fs) nxt path bitsNext.symm sep.1 sep.2.1 sep.2.2.1 parent'
    exact rest

end CommitGolfCandidate.Reconstruction.CheckHonestWalk
