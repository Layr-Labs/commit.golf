import CommitGolfCandidate.TruncCanonical
import CommitGolfCandidate.TruncCommitTruth
import CommitGolfCandidate.PairHonestRead
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 9500
set_option maxHeartbeats 160000
attribute [local irreducible] readBuffer unpack pack

private theorem highByte (v : Digest) (k : Nat) (lo : 30≤k) (hi : k<32) :
    (padLow v).extractLsb' (8*k) 8=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [padLow,BitVec.getLsbD_extractLsb',hb]
  apply (BitVec.getLsbD_append (x:=0#16) (y:=low240 v) (i:=8*k+b)).trans
  rw [if_neg (by omega : ¬8*k+b<240)]
  simp

private theorem projected (o : Oracle) (m : Message) (s : MachineState) (ok : CommittedState o m s)
    (x : Nat) (hx : masked x) :
    ∀ k,30≤k → k<32 → (PairCap.hnode s x).extractLsb' (8*k) 8=0 := by
  have bound:=hx.2
  have tree:=ok.2.1 x (by have:=hx.1;omega) (by change x<16777216;omega)
  change PairCap.hnode s x=storeNode x _ at tree
  intro k lo hi;rw [tree,storeNode,if_pos hx];exact highByte _ _ lo hi

private theorem maskSibling (x : Nat) (lo : 3≤x) (hi : x<2^22) : masked (x ^^^ 1) := by
  have up:=(heap_sibling_bounds (2^21) x (by omega) hi).2
  by_cases e : x%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr e)] at up ⊢;exact ⟨by omega,up⟩
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))] at up ⊢;exact ⟨by omega,up⟩

private theorem slotProp {α : Type} (P : α→Prop) (sel : Nat→Nat) (f : Nat→α) (p n : Nat) (v : α)
    (first : P v) (all : ∀ j,P (f j)) : P (PairCap.overrideSlot sel f p n v) := by
  induction n generalizing v with
  | zero=>exact first
  | succ n ih=>rw [PairCap.overrideSlot];split <;> apply ih <;> first | exact first | apply all

private theorem blockByte (i : CheckInput) (size : i.proof.length=71680) (off k : Nat)
    (fits : off+32≤71680) (hk : k<32) :
    i.proof[off+k]'(by omega) =
      (readBuffer (CommitGolfCandidate.submission.initialState .check i) (10871640096+off) 32).extractLsb' (8*k) 8 := by
  rw [read_buffer_byte _ _ _ _ hk,show 10871640096+off+k=10871640096+(off+k) by omega]
  exact (check_input_proof_byte i (by change i.proof.length≤13153337344;omega) (off+k) (by omega)).symm

theorem honestRoundTrip (o : Oracle) (m : Message) (s : MachineState) (ok : CommittedState o m s)
    (ps : Positions) (b : ps.card=BATCH) :
    let i:=PairCap.honestInput s m ps
    unpack (pack i.proof)=i.proof := by
  let i:=PairCap.honestInput s m ps
  have length : i.proof.length=71680 :=
    (PairCap.opening_proof_length (PairCap.saved s) ps).trans (by simp [PairCap.proofBytes,b])
  apply unpackPack i.proof length
  intro j hj nh
  rcases omitted j (by omega) nh with ⟨r,hr,l,lo,hl,k,kl,hk,rfl⟩|⟨p,hp,k,kl,hk,rfl⟩
  · let x:=openingIndex ps r
    have bx : x<16777216:=opening_index_bound _ _
    have masks : masked (((LENGTH+x)/2^l) ^^^ 1) := by
      apply maskSibling <;> unfold LENGTH LOG_LENGTH <;> interval_cases l <;> omega
    have raw := (PairCap.batchRecords s ps b r hr).2 l hl
    have got:=PairCap.parsedBlock s m ps b (528*r+16+32*l) (by omega)
    rw [show 10871640096+(528*r+16+32*l)=10871640096+528*r+16+32*l by omega] at got
    rw [blockByte i length _ k (by omega) hk,show 10871640096+(528*r+16+32*l)=10871640096+528*r+16+32*l by omega,got,raw]
    exact projected o m s ok _ masks k kl hk
  · have got:=PairCap.parsedBlock s m ps b (67584+32*p) (by omega)
    have raw:=PairCap.batchSlot s ps b p hp
    rw [show 10871640096+(67584+32*p)=PairCap.outBase+32*p by unfold PairCap.outBase;omega] at got
    rw [blockByte i length _ k (by omega) hk]
    rw [show 10871640096+(67584+32*p)=PairCap.outBase+32*p by unfold PairCap.outBase;omega,got,raw]
    apply slotProp (fun d : Digest=>d.extractLsb' (8*k) 8=0)
    · exact projected o m s ok _ ⟨by omega,by omega⟩ k kl hk
    · intro r
      have small : openingIndex ps r<16777216:=opening_index_bound _ _
      exact projected o m s ok _ (maskSibling (256+openingIndex ps r/65536) (by omega) (by omega)) k kl hk
end CommitGolfCandidate.Trunc
