import CommitGolfCandidate.ReconstructedCommitExact
import CommitGolfCandidate.ReconstructedBindingOracle
import CommitGolfCandidate.ReconstructedCommitParentsSpec

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact

def rawC (o : Oracle) : Compress := fun k => unpack (o.compression (encodeKey k))
def cell (s : MachineState) (a : Nat) : Binding.Digest := unpack (readBuffer s a 32)

theorem pair_read (s : MachineState) (a : Nat) (aligned : a%8=0) :
    readBuffer s a 64 = encodeKey (cell s a,cell s (a+32)) := by
  rw [read_compression_halves s a aligned]
  simp [encodeKey,cell]

def Frame (dst : Nat) (before after : MachineState) :=
  ∀ a len, a+len ≤ 2^64 → (a+len ≤ dst ∨ dst+32 ≤ a) →
    readBuffer after a len = readBuffer before a len

theorem Frame.trans {dst s t u} (f : Frame dst s t) (g : Frame dst t u) : Frame dst s u :=
  fun a n h h' => (g a n h h').trans (f a n h h')

def callAfter (s : MachineState) (o : Oracle) (dst : Nat) (k : Key) :=
  writeBits s (BitVec.ofNat 64 dst) (o.compression (encodeKey k))

theorem call_exact (o : Oracle) (im : Image) (s : MachineState) (src dst : Nat) (key : Key)
    (hs : src+64 ≤ MEMORY_BYTES) (hd : dst+32 ≤ MEMORY_BYTES) (alignS : src%8=0) (alignD : dst%8=0)
    (r0 : s.getReg .x5=0) (r1 : s.getReg .x10=BitVec.ofNat 64 src) (r2 : s.getReg .x11=64)
    (r3 : s.getReg .x12=BitVec.ofNat 64 dst) (r4 : s.getReg .x13=0)
    (read : readBuffer s src 64 = encodeKey key) (f : fetch im s = some (.base .ECALL)) :
    Segment o im 1 s (callAfter s o dst key) := by
  have sv : (BitVec.ofNat 64 src).toNat = src := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at hs; omega)]
  have dv : (BitVec.ofNat 64 dst).toNat = dst := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold MEMORY_BYTES at hd; omega)]
  have args : oracleInput s = some (.inl (encodeKey key)) := by
    have kind : (s.getReg .x13).toNat=0 := by rw [r4]; rfl
    unfold oracleInput
    dsimp only
    rw [kind]
    simp [rangeValid,r1,r2,r3,sv,dv,hs,hd,alignD,alignS,read,
      COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH]
  have next := call o im s (.inl (encodeKey key)) f r0 args
  rw [r3] at next
  exact next

theorem call_contents (s : MachineState) (o : Oracle) (dst : Nat) (key : Key) (h : dst+32 ≤ 2^64) :
    cell (callAfter s o dst key) dst = rawC o key ∧ Frame dst s (callAfter s o dst key) := by
  constructor
  · unfold callAfter cell rawC
    apply congrArg unpack
    let y : BitVec 256 := o.compression (encodeKey key)
    change readBuffer (writeBits (bits := 256) s (BitVec.ofNat 64 dst) y) dst 32 = y
    simpa only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] using
      write_bits_digest (bits := 256) s dst 0 y (by decide) (by decide)
  · intro a len hi sep
    exact write_bits_read_outside _ _ _ _ _ h hi sep

def continues (s : MachineState) (o : Oracle) (dst : Nat) (key : Key) : Nat → MachineState
  | 0 => s
  | n+1 => callAfter (continues s o dst key n) o dst (lastKey (rawC o) key (n+1))

theorem continued_registers (s : MachineState) (o : Oracle) (dst : Nat) (key : Key) (n : Nat) :
    (continues s o dst key n).pc = s.pc + BitVec.ofNat 64 (4*n) ∧
    ∀ r, (continues s o dst key n).getReg r = s.getReg r := by
  induction n with
  | zero => exact ⟨(BitVec.add_zero _).symm,fun _ => rfl⟩
  | succ n ih =>
    refine ⟨?_,fun r => (writeBits_register ..).trans (ih.2 r)⟩
    change (continues s o dst key n).pc+4 = _
    rw [ih.1,BitVec.add_assoc,show 4*(n+1) = 4*n+4 by omega,BitVec.ofNat_add]
    rfl

/-- The actual repeated compressed calls at a paid slot, after the first
binary answer was stored and a0 was set to the output. -/
theorem continue_exact (s : MachineState) (o : Oracle) (im : Image) (dst : Nat) (key : Key) (n : Nat)
    (room : dst+64 ≤ MEMORY_BYTES) (aligned : dst%8=0)
    (reg : s.getReg .x5=0 ∧ s.getReg .x10=BitVec.ofNat 64 dst ∧ s.getReg .x11=64 ∧
      s.getReg .x12=BitVec.ofNat 64 dst ∧ s.getReg .x13=0)
    (initial : cell s dst = rawC o key) (zero : cell s (dst+32) = zeroDigest)
    (words : ∀ j < n, ∀ t : MachineState, t.pc = s.pc + BitVec.ofNat 64 (4*j) → fetch im t = some (.base .ECALL)) :
    let t := continues s o dst key n
    Segment o im n s t ∧ cell t dst = rawC o (lastKey (rawC o) key n) ∧ Frame dst s t := by
  have limit : dst+64 ≤ 2^64 := by unfold MEMORY_BYTES at room;omega
  induction n with
  | zero => exact ⟨empty o im s,initial,fun _ _ _ _ => rfl⟩
  | succ n ih =>
    let t := continues s o dst key n
    obtain ⟨seg,value,frame⟩ := ih (fun j hj => words j (by omega))
    have touched := continued_registers s o dst key n
    have zeros : cell t (dst+32) = zeroDigest :=
      (congrArg unpack (frame (dst+32) 32 (by omega) (Or.inr le_rfl))).trans zero
    have pair : readBuffer t dst 64 = encodeKey (lastKey (rawC o) key (n+1)) := by
      rw [pair_read _ _ aligned,value,zeros];rfl
    have call₁ := call_exact o im t dst dst _ room (by omega) aligned aligned
      ((touched.2 _).trans reg.1) ((touched.2 _).trans reg.2.1) ((touched.2 _).trans reg.2.2.1)
      ((touched.2 _).trans reg.2.2.2.1) ((touched.2 _).trans reg.2.2.2.2) pair (words n (by omega) t touched.1)
    have contents := call_contents t o dst (lastKey (rawC o) key (n+1)) (by omega)
    exact ⟨compose seg call₁,contents.1,frame.trans contents.2⟩

end CommitGolfCandidate.Reconstruction.CommitParents
