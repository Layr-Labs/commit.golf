import CommitGolfCandidate.ChainedFirstPackContent

/-! The native first-stage buffer is exactly the canonical height/child input. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
attribute [local irreducible] firstPackPrefix

private theorem eight_concat (a b c d e f g h : Word) :
    (a ++ b ++ c ++ d) ++ (e ++ f ++ g ++ h) = a ++ b ++ c ++ d ++ e ++ f ++ g ++ h := by
  simp only [BitVec.append_assoc,BitVec.cast_eq]

theorem first_pack_input (s : MachineState) (h : Height) (left right : BitVec 238)
    (height : s.getReg .x17 = BitVec.ofNat 64 h.val)
    (aligned : (s.getReg .x10).toNat % 8 = 0)
    (inputs : ∀ k : Fin 8, s.getMem (s.getReg .x14+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord left k.val else childWord right (k.val-4)) :
    readBuffer (firstPackPrefix s 31) (s.getReg .x10).toNat 64 =
      canonicalEncoding.first h (right ++ left) := by
  have words := fun k : Fin 8 => first_pack_stored_word s left right k inputs
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,and_true,Fin.val_zero,Fin.val_succ,
    Nat.reduceAdd,Nat.reduceMul,BitVec.add_zero] at words
  rcases words with ⟨w0,w1,w2,w3,w4,w5,w6,w7⟩
  rw [read_compression_halves _ _ aligned,
    read_digest_words _ ((s.getReg .x10).toNat+32) (by omega),
    read_digest_words _ (s.getReg .x10).toNat aligned]
  simp only [Nat.add_assoc,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,Nat.reduceAdd]
  erw [w7,w6,w5,w4,w3,w2,w1,w0]
  rw [eight_concat]
  change firstPackedValue (s.getReg .x17) left right = _
  rw [height]
  exact first_packed_encoding h left right

end CommitGolfCandidate.Chained.Native
