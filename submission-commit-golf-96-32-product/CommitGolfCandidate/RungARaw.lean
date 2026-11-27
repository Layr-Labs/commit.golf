import CommitGolfCandidate.RungAExec
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (Digest)
attribute [local irreducible] DetRun execute readBuffer writeBits
private theorem compressResult (h768 : COMPRESSION_INPUT_LENGTH = 768)
    {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 0#64)
    (hx11 : s.getReg .x11 = 96#64)
    (hx13 : s.getReg .x13 = 0#64)
    (src dst : Nat)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 96 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES)
    (out : Digest)
    (hout : oracle.compression ((readBuffer s src 96).cast h768.symm) = out) :
    DetRun oracle img s 1 (writeBits s (BitVec.ofNat 64 dst) out) 8 1 := by
  have h := DetRun.compress h768 (oracle := oracle) hfetch hx5 hx11 hx13 src dst hx10 hx12 hsrc_al hdst_al hsrc_bd hdst_bd
  have hw : writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 96).cast h768.symm)) =
      writeBits s (BitVec.ofNat 64 dst) out := by
    change writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 96).cast h768.symm) : Digest) =
      writeBits s (BitVec.ofNat 64 dst) out
    rw [hout]
    rfl
  rw [← hw]
  exact h

theorem rawInstruction (o : Oracle) (img : Image) (s : MachineState) (b a : Nat)
    (f : fetch img s=some (.base .ECALL)) (mode:s.getReg .x5=0) (width:s.getReg .x11=96) (kind:s.getReg .x13=0)
    (inp:s.getReg .x10=BitVec.ofNat 64 b) (dst:s.getReg .x12=BitVec.ofNat 64 a)
    (ba:b%8=0) (aa:a%8=0) (br:b+96≤MEMORY_BYTES) (ar:a+32≤MEMORY_BYTES) (w : Digest)
    (ans:o.compression (readBuffer s b 96)=w) :
    DetRun o img s 1 (writeBits s (BitVec.ofNat 64 a) w) 8 1 :=
  compressResult (by rfl) (oracle:=o) (img:=img) (s:=s) f mode width kind b a inp dst ba aa br ar w
    ((congrArg o.compression (BitVec.cast_eq _ _)).trans ans)
end CommitGolfCandidate.RungA
