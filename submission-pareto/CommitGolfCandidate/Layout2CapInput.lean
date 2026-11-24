import CommitGolfCandidate.Layout2CapPass
import CommitGolfCandidate.Layout2CapRoundtrip
import CommitGolfCandidate.Layout2QuartetInput
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
def prepared (i : CheckInput) : CheckInput := {i with proof:=transform dec i.positions.card i.proof}
@[simp] theorem prepared_len (i : CheckInput) : (prepared i).proof.length=i.proof.length := length_transform ..

theorem same_args (c : Submission) (i : CheckInput) (r : Reg) :
    (c.initialState .check i).getReg r=(c.initialState .check (prepared i)).getReg r :=
  Quartet.same_args_for c i (prepared i) r rfl (prepared_len i).symm

attribute [local irreducible] Submission.initialState ArtifactEncoding.decode

private theorem at_congr (n j : Nat) (inside : j<n) (shape : size (tag (n%952))=n%952)
    (x y : Nat→Byte) (agree : ∀ u,u<n → x u=y u) : atByte dec n x j=atByte dec n y j := by
  let g:=j/952
  let m:=chunk n j
  have facts : 1≤m ∧ m≤32 ∧ j%952<size m ∧ 952*g+size m≤n := by
    dsimp [m,chunk,g];split
    · change 1≤32 ∧ 32≤32 ∧ j%952<952 ∧ 952*(j/952)+952≤n;omega
    · have pos : tag (n%952)≠0 := by intro z;rw [z] at shape;change 0=_ at shape;omega
      have maxTag : tag (n%952)<32 := by unfold tag;omega
      omega
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold atByte
  rw [gather_bit _ _ _ _ _ hb,gather_bit _ _ _ _ _ hb]
  have h:=dec_valid m facts.1 facts.2.1 (8*(j%952)+b) (by omega)
  change (x (952*g+dec m (8*(j%952)+b)/8)).getLsbD _=_
  rw [agree _ (by omega)]

theorem prepared_mem (i : CheckInput) (fit : i.proof.length≤8959041024) (good : Good i.positions.card i.proof.length)
    {u} (cap : Writes (candidate.initialState .check i) u (proofBase+534*i.positions.card)
      (i.proof.length-534*i.positions.card)
      (result (candidate.initialState .check i) (proofBase+534*i.positions.card) (i.proof.length-534*i.positions.card)))
    (q : Nat) (ram : q<MEMORY_BYTES) : byte u q=byte (candidate.initialState .check (prepared i)) q := by
  have len:=prepared_len i
  have long:=good.1
  have read (v : CheckInput) (j : Nat) (fits : v.proof.length≤8959041024) (inProof : j<v.proof.length) :
    byte (candidate.initialState .check v) (proofBase+j)=v.proof[j]?.getD 0 := by
    rw [below_table v _ (by unfold proofBase tableBase;omega)]
    exact (Checker.check_input_proof_byte v fits j inProof).trans (by simp [inProof])
  rw [cap q ram]
  by_cases hit : proofBase≤q ∧ q<proofBase+i.proof.length
  · let j:=q-proofBase
    have pos : q=proofBase+j := by dsimp [j];omega
    have small : j < i.proof.length := by dsimp [j];omega
    rw [pos,read (prepared i) j (by omega) (by omega)]
    change _=(transform dec i.positions.card i.proof)[j]?.getD 0
    rw [read_transform _ _ _ _ small]
    by_cases capHit : 534*i.positions.card≤j
    · rw [if_pos capHit,if_pos (by omega)]
      unfold result
      rw [show proofBase+j-(proofBase+534*i.positions.card)=j-534*i.positions.card by omega]
      apply at_congr _ _ (by omega) good.2.1
      intro z sz;rw [Nat.add_assoc];exact read i _ fit (by omega)
    · rw [if_neg capHit,if_neg (by omega)]
      exact read i j fit small
  · rw [if_neg (by omega : ¬(proofBase+534*i.positions.card≤q ∧ q<proofBase+534*i.positions.card+(i.proof.length-534*i.positions.card)))]
    apply Eq.symm
    have small : q<2^64 := by unfold MEMORY_BYTES at ram;omega
    refine (initial_input_byte candidate .check (prepared i) q small).trans
      (Eq.trans ?_ (initial_input_byte candidate .check i q small).symm)
    have none : ¬(candidate.layout.proof≤q ∧ q<candidate.layout.proof+i.proof.length) := hit
    simp only [inputByte,Submission.inputBuffers,List.find?_cons,prepared_len,none,decide_false,cond_false,List.find?_nil]
    rfl

end CommitGolfCandidate.Layout2.Cap
