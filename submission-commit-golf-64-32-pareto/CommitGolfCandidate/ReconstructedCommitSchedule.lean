import CommitGolfCandidate.ReconstructedCommitSetup

namespace CommitGolfCandidate.Reconstruction.CommitSchedule
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitControl CommitBlocks CommitLoop CommitSlices CommitSetup

set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local irreducible] ArtifactEncoding.decode

abbrev StateAt (i n : Nat) := At (addr i) (BitVec.ofNat 64 n)

theorem line (a b cycles queries n : Nat) (ord : a ≤ b) (fin : b ≤ 150132)
    (receipt : summarize Artifact.commitCode a b = ⟨true,cycles,queries⟩) :
    Fragment im (b-a) cycles queries (StateAt a n) (StateAt b n) := by
  have h := sound im Artifact.commitCode 0 a b (BitVec.ofNat 64 n) commit_view ord fin
    (show (summarize _ a b).good = true by rw [receipt])
  rw [receipt] at h
  simpa only [Nat.zero_add] using h

theorem lineWord (a b cycles queries : Nat) (c : Word) (ord : a ≤ b) (fin : b ≤ 150132)
    (receipt : summarize Artifact.commitCode a b = ⟨true,cycles,queries⟩) :
    Fragment im (b-a) cycles queries (At (addr a) c) (At (addr b) c) := by
  simpa [StateAt] using line a b cycles queries c.toNat ord fin receipt

abbrev StateAtC (i n : Nat) := AtC (addr i) (BitVec.ofNat 64 n)

theorem lineC (a b cycles queries n : Nat) (ord : a ≤ b) (fin : b ≤ 150132)
    (receipt : summarizeC Artifact.commitCode a b = ⟨true,cycles,queries⟩) :
    Fragment im (b-a) cycles queries (StateAtC a n) (StateAtC b n) := by
  have h := soundC im Artifact.commitCode 0 a b (BitVec.ofNat 64 n) commit_view ord fin
    (show (summarizeC _ a b).good = true by rw [receipt])
  rw [receipt] at h
  simpa only [Nat.zero_add] using h

theorem lineWordC (a b cycles queries : Nat) (c : Word) (ord : a ≤ b) (fin : b ≤ 150132)
    (receipt : summarizeC Artifact.commitCode a b = ⟨true,cycles,queries⟩) :
    Fragment im (b-a) cycles queries (AtC (addr a) c) (AtC (addr b) c) := by
  simpa [StateAtC] using lineC a b cycles queries c.toNat ord fin receipt

def reads (i : Nat) (op : Instr) : Prop :=
  ∀ s : MachineState, s.pc = addr i → fetch im s = some (.base op)

theorem reads_at (i : Fin 150132) (op : Instr)
    (dec : decodeInstruction (Artifact.commitCode.get 32 i) = some (.base op)) : reads i op :=
  fetch_at i _ dec

theorem loop (a b n cycles queries : Nat) (range : n+1 < 2^64) (offset : BitVec 21)
    (body : ∀ c : Word, Fragment im (b-a) cycles queries (At (addr a) c) (At (addr b) c))
    (d : reads b (.ADDI .x20 .x20 4095)) (br : reads (b+1) (.BEQ .x20 .x0 8))
    (back : reads (b+2) (.JAL .x0 offset))
    (target : addr (b+2) + signExtend21 offset = addr a) :
    Fragment im ((n+1)*(b-a+3)-1) ((n+1)*(cycles+3)-1) ((n+1)*queries)
      (StateAt a (n+1)) (StateAt (b+3) 0) := by
  have b1 := addr_next b
  have b2 : addr (b+2) = addr b + 8 := by
    rw [addr_next (b+1),b1,BitVec.add_assoc]; rfl
  have b3 : addr (b+3) = addr b + 12 := by
    rw [addr_next (b+2),b2,BitVec.add_assoc]; rfl
  have hf (c : Word) := branch_zero im (addr (b+1)) c br
  have hb (c : Word) := jump_back im (addr (b+2)) (addr a) c offset back target
  rw [b2] at hb
  have branch (c : Word) : Fragment im 1 1 0 (At (addr b+4) c)
      (At (if c=0 then addr b+12 else addr b+8) c) := by
    have h := hf c
    rw [b1] at h
    simp only [BitVec.add_assoc] at h
    exact h
  have h := counted im (addr a) (addr b) (b-a) cycles queries body
    (fun k => decrement im (addr b) k d) branch hb n range
  have hn := work_eq (b-a) n
  have hc := work_eq cycles n
  rw [show work (b-a) (n+1) = (n+1)*(b-a+3)-1 by omega,
      show work cycles (n+1) = (n+1)*(cycles+3)-1 by omega,← b3] at h
  exact h

theorem loopC (a b n cycles queries : Nat) (range : n+1 < 2^64) (offset : BitVec 21)
    (body : ∀ c : Word, Fragment im (b-a) cycles queries (AtC (addr a) c) (AtC (addr b) c))
    (d : reads b (.ADDI .x20 .x20 4095)) (br : reads (b+1) (.BEQ .x20 .x0 8))
    (back : reads (b+2) (.JAL .x0 offset))
    (target : addr (b+2) + signExtend21 offset = addr a) :
    Fragment im ((n+1)*(b-a+3)-1) ((n+1)*(cycles+3)-1) ((n+1)*queries)
      (StateAtC a (n+1)) (StateAtC (b+3) 0) := by
  have b1 := addr_next b
  have b2 : addr (b+2) = addr b + 8 := by
    rw [addr_next (b+1),b1,BitVec.add_assoc]; rfl
  have b3 : addr (b+3) = addr b + 12 := by
    rw [addr_next (b+2),b2,BitVec.add_assoc]; rfl
  have hf (c : Word) := branch_zeroC im (addr (b+1)) c br
  have hb (c : Word) := jump_backC im (addr (b+2)) (addr a) c offset back target
  rw [b2] at hb
  have branch (c : Word) : Fragment im 1 1 0 (AtC (addr b+4) c)
      (AtC (if c=0 then addr b+12 else addr b+8) c) := by
    have h := hf c
    rw [b1] at h
    simp only [BitVec.add_assoc] at h
    exact h
  have h := countedC im (addr a) (addr b) (b-a) cycles queries body
    (fun k => decrementC im (addr b) k d) branch hb n range
  have hn := work_eq (b-a) n
  have hc := work_eq cycles n
  rw [show work (b-a) (n+1) = (n+1)*(b-a+3)-1 by omega,
      show work cycles (n+1) = (n+1)*(cycles+3)-1 by omega,← b3] at h
  exact h

end CommitGolfCandidate.Reconstruction.CommitSchedule
