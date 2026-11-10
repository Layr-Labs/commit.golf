import CommitGolfCandidate.NonceSaltMemory
/-! Direct library proofs for nonce word concatenation and zero extension. These proofs require no external SAT solver during verification. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem nonce_bits_group (a b c d : Word) :
    (((a++b)++c)++d : BitVec 256)=a++((b++c)++d) := by
  calc
    _ = ((a++b)++(c++d) : BitVec 256) := BitVec.append_assoc (x₁:=a++b) (x₂:=c) (x₃:=d)
    _ = (a++(b++(c++d)) : BitVec 256) := BitVec.append_assoc (x₁:=a) (x₂:=b) (x₃:=c++d)
    _ = _ := congrArg (fun value : BitVec 192 => a++value)
      (BitVec.append_assoc (x₁:=b) (x₂:=c) (x₃:=d)).symm

theorem nonce_bits_low (a b c d : Word) :
    (((a++b)++c)++d : BitVec 256).extractLsb' 0 192=(b++c)++d := by
  rw [nonce_bits_group]
  exact BitVec.extractLsb'_append_eq_right

theorem nonce_bits_high (a b c d : Word) :
    (((a++b)++c)++d : BitVec 256).extractLsb' 192 64=a := by
  rw [nonce_bits_group]
  exact BitVec.extractLsb'_append_eq_left

theorem nonce_bits_expand_low (nonce : BitVec 192) :
    (nonce.setWidth 256).extractLsb' 0 192=nonce := by
  rw [BitVec.setWidth_eq_append (by decide : 192≤256)]
  exact BitVec.extractLsb'_append_eq_right

theorem nonce_bits_expand_high (nonce : BitVec 192) :
    (nonce.setWidth 256).extractLsb' 192 64=0 := by
  rw [BitVec.setWidth_eq_append (by decide : 192≤256)]
  exact BitVec.extractLsb'_append_eq_left

theorem nonce_bits_pad_concat (a b c : Word) :
    (((0#64++c)++b)++a : BitVec 256)=expandNonce192 ((c++b)++a) := by
  change (((0#64++c)++b)++a : BitVec 256)=(((c++b)++a).setWidth 256)
  rw [BitVec.setWidth_eq_append (by decide : 192≤256)]
  exact nonce_bits_group _ _ _ _
end CommitGolfCandidate
