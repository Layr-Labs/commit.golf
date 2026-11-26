import CommitGolfCandidate.ReconstructedCheckLeafCall

namespace CommitGolfCandidate.Reconstruction.CheckLeafWords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckValues CheckLeafPlan CheckLeafCall
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 900000
set_option exponentiation.threshold 2048

structure Source (env : Env) (idx : Index) (nonce : Words 2) (msg : Words 32) : Prop where
  position : env.initial.getReg .x16=BitVec.ofNat 64 idx.val
  low : env.initial.getReg .x14=nonce 0
  high : env.initial.getReg .x15=nonce 1
  message : ∀ i : Fin 32, env.initial.getMem (physical env (CheckParentRun.loc 2 (8*i.val)))=msg i

private theorem tag (env : Env) (idx : Index) (n : Words 2) (msg : Words 32) (h : Source env idx n msg) :
    positionWord.val env=pinnedPositionTag idx := by
  change 3633#64+(env.initial.getReg .x16 <<< (8 : Nat))+519#64=_
  rw [h.position]
  apply BitVec.eq_of_toNat_eq
  simp only [pinnedPositionTag,BitVec.toNat_add,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  have hi : idx.val<2^24:=idx.isLt
  omega

theorem input (o : Oracle) (env : Env) (idx : Index) (n : Words 2) (msg : Words 32) (src : Source env idx n msg)
    (answers : ∀ q<2, ∀ i<25, env.answer q i=(o.permutation (request o idx n msg q)).extractLsb' (64*i) 64)
    (q : Nat) (hq : q<2) (i : Fin 25) : (operand q i).val env=(request o idx n msg q).extractLsb' (64*i.val) 64 := by
  by_cases first : q=0
  · subst q
    change _=(packBuffer (pinnedFirstInput msg)).extractLsb' (64*i.val) 64
    rw [packed_word]
    exact src.message ⟨i.val,by have:=i.isLt;omega⟩
  · rw [request,ite_eq_right first]
    change _=(packBuffer (pinnedSecondInput idx n (replyWords (pinnedFirstRow o.permutation msg).2) msg)).extractLsb' (64*i.val) 64
    rw [packed_word]
    by_cases z : i.val=0
    · simp only [operand,first,ite_false,z,ite_true,pinnedSecondInput]
      exact tag env idx n msg src
    by_cases one : i.val=1
    · simp only [operand,first,ite_false,z,one,ite_true,pinnedSecondInput]
      exact src.low
    by_cases two : i.val=2
    · simp only [operand,first,ite_false,z,one,two,ite_true,pinnedSecondInput]
      exact src.high
    have gt : ¬i.val<3:=by omega
    by_cases mid : i.val<14
    · simp only [operand,first,ite_false,z,one,two,mid,ite_true,pinnedSecondInput,gt,dite_false,dite_true,Term.val]
      have h := answers 0 (by decide) (i.val+11) (by omega)
      have hx : o.permutation (request o idx n msg 0) = (pinnedFirstRow o.permutation msg).2 := rfl
      rw [hx] at h
      rw [Nat.add_comm 11 i.val]
      exact h
    · simp only [operand,first,ite_false,z,one,two,mid,pinnedSecondInput,gt,dite_false,Term.val]
      exact src.message ⟨i.val+7,by have:=i.isLt;omega⟩

private theorem projected (b : Block) (i : Fin 4) :
    (if i.val=3 then (b.extractLsb' 192 64 <<< (16 : Nat)) >>> (16 : Nat) else b.extractLsb' (64*i.val) 64)
    =(leafDigestW 240 b).extractLsb' (64*i.val) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have bound:=i.isLt
  simp only [leafDigestW,truncDigestW,outputDigest,BitVec.getLsbD_extractLsb',BitVec.getLsbD_ofNat,
    Nat.testBit_mod_two_pow,BitVec.testBit_toNat]
  by_cases hi : i.val=3
  · simp only [hi,ite_true,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_extractLsb']
    by_cases low : k<48 <;>
      simp [hk,low,show k+16<64 ↔ k<48 by omega,show 16+k<64 ↔ k<48 by omega,
        show k+192<240 ↔ k<48 by omega,show k+192<256 by omega,Nat.add_comm]
  · have lower : 64*i.val+k<240 := by omega
    simp [hi,BitVec.getLsbD_extractLsb',hk,lower,show 64*i.val+k<256 by omega]

theorem digest (o : Oracle) (env : Env) (idx : Index) (n : Words 2) (msg : Words 32)
    (answers : ∀ q<2, ∀ i<25, env.answer q i=(o.permutation (request o idx n msg q)).extractLsb' (64*i) 64)
    (i : Fin 4) : (digestWord i).val env=(leafDigestW 240 (o.permutation (request o idx n msg 1))).extractLsb' (64*i.val) 64 := by
  rw [←projected]
  by_cases hi : i.val=3
  · rw [hi,ite_eq_left rfl]
    change (env.answer 1 3 <<< (16 : Nat)) >>> (16 : Nat) = _
    rw [answers 1 (by decide) 3 (by decide)]
  · rw [ite_eq_right hi,digestWord,ite_eq_right hi]
    exact answers 1 (by decide) _ (by have:=i.isLt;omega)

end CommitGolfCandidate.Reconstruction.CheckLeafWords
