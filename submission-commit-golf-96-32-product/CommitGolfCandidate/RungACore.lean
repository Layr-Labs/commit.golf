import CommitGolfCandidate.RungAPointers
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 R4 Late
set_option Elab.async false
set_option maxRecDepth 1500
set_option maxHeartbeats 180000
attribute [local irreducible] DetRun execute readBuffer writeBits R4.submission
structure Write (o : Oracle) (s t : MachineState) (n k a : Nat) (v : Late.Digest) : Prop where
  run : MRun o s k t (k+7) 1
  pc : t.pc=pcAt (n+k)
  result : readBuffer t a 32=v
  away : MemPreservedOutside s t a (a+32)
  ptr : t.getReg .x12=Z a
  stable : Stable s t

theorem rawInstruction (o : Oracle) (img : Image) (s : MachineState) (a b : Nat)
    (fetchOp : fetch img s=some (.base .ECALL)) (mode : s.getReg .x5=0) (kind : s.getReg .x13=0) (width : s.getReg .x11=96)
    (src : s.getReg .x10=Z b) (dst : s.getReg .x12=Z a)
    (sa : b%8=0) (da : a%8=0) (sb : b+96≤MEMORY_BYTES) (db : a+32≤MEMORY_BYTES) :
    DetRun o img s 1 (writeBits s (Z a) (o.compression (readBuffer s b 96))) 8 1 :=
  DetRun.compress_eq (by rfl) (oracle:=o) (img:=img) (s:=s) fetchOp mode width kind b a src dst sa da sb db
    (o.compression (readBuffer s b 96)) (congrArg o.compression (BitVec.cast_eq _ _))

theorem hash (o : Oracle) (s u : MachineState) (n k src dst : Nat) (e : Env s) (p : Assigned o s u n k dst src)
    (raw : Late.Digest) (input : o.compression (readBuffer s src 96)=raw) (short : Bool)
    (sa : src%8=0) (da : dst%8=0) (sb : src+96≤MEMORY_BYTES) (db : dst+32≤MEMORY_BYTES)
    (op : Site (n+k) .ECALL) (sh : short=true → Site (n+k+1) (.SH .x12 .x0 30)) :
    ∃ t, Write o s t n (k+1+(if short then 1 else 0)) dst (mask short raw) := by
  let w:=writeBits u (Z dst) raw
  have u5 : u.getReg .x5=0 := (p.stay .x5 (by decide) (by decide)).trans e.mode
  have u11 : u.getReg .x11=96 := (p.stay .x11 (by decide) (by decide)).trans e.width
  have u13 : u.getReg .x13=0 := (p.stay .x13 (by decide) (by decide)).trans e.kind
  have go0:=rawInstruction o (R4.submission.image .commit) u dst src (op u p.pc) u5 u13 u11 p.src p.dst sa da sb db
  have eqn : o.compression (readBuffer u src 96)=raw :=
    (congrArg o.compression (readBuffer_of_mem_eq (s1:=u) (s2:=s) p.mem src 96)).trans input
  have go : MRun o u 1 w 8 1 := (congrArg (fun v : Late.Digest=>MRun o u 1 (writeBits u (Z dst) v) 8 1) eqn).mp go0
  have ip : w.pc=pcAt (n+k+1):=(pc_writeBits u (Z dst) raw).trans (pc_step_idx _ _ p.pc)
  have same (t : MachineState) (v : Late.Digest) (mem : t.mem=(writeBits u (Z dst) v).mem) :
      MemPreservedOutside s t dst (dst+32) := by
    intro i fit apart
    exact (getByte_of_mem_eq mem _).trans ((memPreserved_writeBits u dst v (db.trans (by decide)) i fit apart).trans (getByte_of_mem_eq p.mem _))
  cases short with
  | false=>
    refine ⟨w,?_,?_,store_read u dst raw,same w raw rfl,(writeBits_register u (Z dst) raw .x12).trans p.dst,?_⟩
    · simpa only [Bool.false_eq_true,ite_false,Nat.add_zero, Nat.add_assoc] using p.run.trans go
    · change w.pc=pcAt (n+(k+1));simpa only [Nat.add_assoc] using ip
    · intro q h;exact (writeBits_register u (Z dst) raw q).trans (p.stay q h.1 h.2.1)
  | true=>
    obtain ⟨t,m⟩:=maskWide o u (n+k+1) dst raw ip p.dst da db (sh rfl)
    refine ⟨t,?_,?_,(readBuffer_of_mem_eq m.mem _ _).trans (store_read u dst (Trunc.padLow raw)),same t _ m.mem,
      (m.keep _ (by decide)).trans p.dst,?_⟩
    · have f:=(p.run.trans go).trans m.run
      change MRun o s (k+1+1) t (k+1+1+7) 1
      simpa only [show k+8+1=k+1+1+7 by omega] using f
    · change t.pc=pcAt (n+(k+1+1));simpa only [Nat.add_assoc] using m.pc
    · intro q h;exact (m.keep q h.2.2).trans (p.stay q h.1 h.2.1)
end CommitGolfCandidate.RungA.Kernel
