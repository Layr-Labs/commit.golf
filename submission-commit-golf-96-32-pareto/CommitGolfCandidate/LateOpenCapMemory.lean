import CommitGolfCandidate.LateOpenPathStep

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def capBase := proofBase+68608
def slotAddr (p : Nat) := capBase+32*p
def SlotData (s : MachineState) (p : Nat) (v : Digest) := HasBytes s (slotAddr p) (bytes (n:=32) v)

theorem slot_bounds (p : Nat) (hi : p<128) : capBase≤slotAddr p ∧ slotAddr p+32≤capBase+4096 ∧
    slotAddr p%8=0 ∧ slotAddr p+32≤MEMORY_BYTES := by
  unfold slotAddr capBase proofBase MEMORY_BYTES;omega

theorem Outside.weaken {s t : MachineState} {b n : Nat} (old : Outside s t b n)
    (a m : Nat) (lo : a≤b) (hi : b+n≤a+m) : Outside s t a m :=
  fun q h al away => old q h al (by omega)

theorem Outside.chain {s t u : MachineState} {a n : Nat} (x : Outside s t a n) (y : Outside t u a n) :
    Outside s u a n := fun q h al away => (y _ h al away).trans (x _ h al away)

theorem HasBytes.after_outside {s t : MachineState} {a b n : Nat} {x : Proof}
    (data : HasBytes s a x) (frame : Outside s t b n) (al : b%8=0) (nl : n%8=0)
    (hi : a+x.length≤MEMORY_BYTES) (apart : a+x.length≤b ∨ b+n≤a) : HasBytes t a x := by
  intro i inside
  exact (outside_byte frame al nl (by omega) (by omega)).trans (data i inside)

theorem HasBytes.append {s : MachineState} {a : Nat} {xs ys : Proof} (x : HasBytes s a xs)
    (y : HasBytes s (a+xs.length) ys) : HasBytes s a (xs++ys) := by
  intro i hi; by_cases left : i<xs.length
  · rw [List.getElem_append_left left];exact x i left
  · have right : i-xs.length<ys.length := by simp only [List.length_append] at hi;omega
    rw [List.getElem_append_right (by omega)]
    simpa only [show a+xs.length+(i-xs.length)=a+i by omega] using y _ right

structure CopiedDigest (site : CopySite) (s : MachineState) (dst : Nat) (v : Digest) : Prop where
  run : Runs s (copyWords s 4) 8 8
  pc : (copyWords s 4).pc=pcAt (site.pc+8)
  data : Written s (copyWords s 4) dst (bytes (n:=32) v)

theorem copy_digest (site : CopySite) (width : site.words=4) (s : MachineState) (src dst : Nat) (v : Digest)
    (pc : s.pc=pcAt site.pc) (sp : s.getReg .x23=W src) (dp : s.getReg .x25=W dst)
    (read : readBuffer s src 32=v) (sa : AddrOK src 32) (da : AddrOK dst 32) (sep : src+32≤dst) :
    CopiedDigest site s dst v := by
  refine ⟨copy_run site s pc _ _ sp dp 4 (by omega) sa da,?_,
    copied_bytes (copied _ _ _ sp dp 4 le_rfl sa da sep) sa.1 da.1 v read⟩
  rw [copy_pc,pc];unfold pcAt;rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);omega

theorem copy_node (site : CopySite) (width : site.words=4) (s : MachineState) {xs t salts} (input : Sources s xs t salts)
    (d j p : Nat) (depth : d≤LOG_LENGTH) (ix : j<levelCount d) (small : p<128)
    (pc : s.pc=pcAt site.pc) (sp : s.getReg .x23=W (nodeAddress d j)) (dp : s.getReg .x25=W (slotAddr p)) :
    CopiedDigest site s (slotAddr p) (node t d j) := by
  obtain ⟨_,sb,sa⟩ := node_ok d j ix
  obtain ⟨lo,_,al,hi⟩ := slot_bounds p small
  have bound : nodeAddress d j+32≤MEMORY_BYTES := by unfold indexBase at sb;unfold MEMORY_BYTES;omega
  have sep : nodeAddress d j+32≤slotAddr p := by unfold indexBase at sb;unfold capBase proofBase at lo;omega
  exact copy_digest _ width _ _ _ _ pc sp dp (input.node d depth j ix) ⟨sa,bound⟩ ⟨al,hi⟩ sep

theorem slot_transfer {s t : MachineState} {p q : Nat} {v : Digest}
    (old : SlotData s p v) (hp : p<128) (hq : q<128) (diff : p≠q) (write : Outside s t (slotAddr q) 32) : SlotData t p v := by
  apply old.after_outside write (slot_bounds q hq).2.2.1 (by decide)
  · simpa only [bytes,List.length_ofFn] using (slot_bounds p hp).2.2.2
  · simp only [bytes,List.length_ofFn,slotAddr];omega

end CommitGolfCandidate.Late.Open
