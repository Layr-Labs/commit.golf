import CommitGolfCandidate.TruncWireFrame
import CommitGolfCandidate.TruncCap
import CommitGolfCandidate.BufferRefinement
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 7000
set_option maxHeartbeats 150000

private theorem localShortLimit (b : Bool) (j : Nat) (h : j<(if b then 528 else 32)) :
    ∀ k∈localShort b j,k<(if b then 502 else 30) := by
  cases b
  · exact (show ∀ j : Fin 32,∀ k∈localShort false j.val,k<30 by
      intro j;fin_cases j <;> simp [localShort]) ⟨j,h⟩
  · unfold localShort;simp only [ite_true]
    split_ifs <;> simp_all <;> omega

theorem wideLimit (j k : Nat) (bound : j<71680) (maps : wideIndex j=some k) : k<68096 := by
  unfold wideIndex at maps
  split at maps
  · rename_i small
    cases hx : localShort true (j%528) with
    | none => simp [hx] at maps
    | some u =>
      have hu:=localShortLimit true (j%528) (Nat.mod_lt _ (by decide)) u (by simp [hx])
      simp only [hx,Option.map_some,Option.some.injEq] at maps
      change u<502 at hu;omega
  · rename_i large
    cases hx : localShort false ((j-67584)%32) with
    | none => simp [hx] at maps
    | some u =>
      have hu:=localShortLimit false ((j-67584)%32) (Nat.mod_lt _ (by decide)) u (by simp [hx])
      simp only [hx,Option.map_some,Option.some.injEq] at maps
      change u<30 at hu;omega

def withProof (i : CheckInput) (p : Proof) : CheckInput := {i with proof:=p}

private theorem outsideInput (i : CheckInput) (p : Proof) (a : Nat) (ha : a<2^64)
    (x : ¬(base≤a ∧ a<base+i.proof.length)) (y : ¬(base≤a ∧ a<base+p.length)) :
    byte (submission.initialState .check (withProof i p)) a=byte (submission.initialState .check i) a := by
  apply (initial_input_byte submission .check (withProof i p) a ha).trans
  apply Eq.trans _ (initial_input_byte submission .check i a ha).symm
  change ¬(submission.layout.proof≤a ∧ a<submission.layout.proof+i.proof.length) at x
  change ¬(submission.layout.proof≤a ∧ a<submission.layout.proof+p.length) at y
  simp only [withProof,inputByte,Submission.inputBuffers,List.find?_cons,x,y,decide_false,Bool.false_eq_true,
    ite_false,List.find?_nil]

attribute [local irreducible] unpack wideIndex

private theorem inProof (i : CheckInput) (small : i.proof.length≤13153337344) (j : Nat) (hj : j < i.proof.length) :
    byte (submission.initialState .check i) (base+j)=i.proof[j] :=
  check_input_proof_byte i small j hj

private theorem unpackAt (p : Proof) (j : Nat) (h : j<(unpack p).length) :
    (unpack p)[j]=((wideIndex j).bind (fun u=>p[u]?)).getD 0 := by
  have atMap (n : Nat) (f : Nat→Byte) (k : Nat) (hk : k<((List.range n).map f).length) :
      ((List.range n).map f)[k]=f k := by simp
  unfold unpack at h ⊢
  exact atMap 71680 _ j h

private theorem inputUnpack (i : CheckInput) (length : i.proof.length=68096) (j : Nat) (hj : j<71680) :
    byte (submission.initialState .check (withProof i (unpack i.proof))) (base+j)=
      wanted true (submission.initialState .check i) j := by
  let w:=withProof i (unpack i.proof)
  have len : w.proof.length=71680:=unpack_length i.proof
  change byte (submission.initialState .check w) (base+j)=_
  have bound : j < w.proof.length := len ▸ hj
  exact (inProof w (by omega) j bound).trans ((unpackAt i.proof j bound).trans (by
    unfold wanted srcIndex
    cases eqn : wideIndex j with
    | none => rfl
    | some k =>
      have hk : k < i.proof.length:=length ▸ wideLimit j k hj eqn
      simp only [ite_true,eqn,Option.bind_some,Option.map_some,Option.getD_some]
      rw [inProof i (by omega) k hk,List.getElem?_eq_getElem hk];rfl))

theorem decodedBytes (i : CheckInput) (b : i.positions.card=BATCH) (length : i.proof.length=68096)
    (s t : MachineState) (initial : s.mem=(submission.initialState .check i).mem) (f : Frame true s t 0) :
    ∀ a,a<2^64 → byte t a=byte (submission.initialState .check (wideInput i)) a := by
  intro a ha
  have eqn:=f a ha
  have memory (u : Nat) : byte s u=byte (submission.initialState .check i) u := by
    simp only [byte,MachineState.getByte,MachineState.getMem,initial]
  rw [wideInput,if_pos b]
  change byte t a=byte (submission.initialState .check (withProof i (unpack i.proof))) a
  by_cases inside : passed true 0 a
  · rw [if_pos inside] at eqn
    have pair : base≤a ∧ a<base+71680 := inside
    have j : base+(a-base)=a:=by omega
    have target:=inputUnpack i length (a-base) (by omega)
    rw [j] at target
    rw [eqn,target];simp only [wanted,memory]
  · rw [if_neg inside,memory] at eqn
    rw [eqn];apply Eq.symm
    apply outsideInput _ _ _ ha
    · intro bad;apply inside;change base+0≤a ∧ a<base+71680;omega
    · intro bad;apply inside;change base+0≤a ∧ a<base+71680;rw [unpack_length] at bad;omega

theorem decodedWords {s t : MachineState} (all : ∀ a,a<2^64 → byte s a=byte t a)
    (w : Word) (aligned : w.toNat%8=0) : s.getMem w=t.getMem w := by
  have hw := w.isLt
  have mem := read_word_eq s w.toNat aligned
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at mem
  have other:=read_word_eq t w.toNat aligned
  rw [BitVec.ofNat_toNat,BitVec.setWidth_eq] at other
  rw [←mem,←other]
  unfold readBuffer
  apply congrArg (BitVec.ofNat 64)
  apply Finset.sum_congr rfl
  intro j hj
  have bound:=Finset.mem_range.mp hj
  exact congrArg (fun v : Byte=>v.toNat*2^(8*j)) (all (w.toNat+j) (by omega))
end CommitGolfCandidate.Trunc.Wire
