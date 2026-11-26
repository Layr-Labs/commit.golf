import CommitGolfCandidate.ReconstructedCommitParentsNode

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CommitExact
attribute [local irreducible] readBuffer

theorem aligned32 (d k : Nat) : addr d k % 32 = 0 := by unfold addr;omega

private theorem apart {a b : Nat} (ha : a%32=0) (hb : b%32=0) (ne : a≠b) :
    a+32 ≤ b ∨ b+32 ≤ a := by omega

private theorem room_of_slot {e j : Nat} (de : e≤24) (upper : j≤2^(e+1)) : addr e j+32 ≤ 2^64 := by
  have exp := Nat.pow_le_pow_right (n:=2) (by decide) (show e+1≤25 by omega)
  unfold addr
  omega

/-- A completed node body updates precisely the two heap cells specified by
the trapdoor traversal and retains every level's continuation guard. -/
theorem snapshot_after_node {s t : MachineState} {tree : Nat → Nat → Binding.Digest}
    {d k : Nat} (snap : Snapshot (cell s) tree d k)
    (dep : d < 24) (lo : 2^d ≤ k) (hi : k < 2^(d+1))
    (dst : cell t (addr d k)=written d (tree d k))
    (right : cell t (addr (d+1) (2*k)+32)=marked (d+1) true (tree (d+1) (2*k+1)))
    (frame : NodeWrites (addr (d+1) (2*k)) (addr d k) s t) :
    Snapshot (cell t) tree d (k+1) := by
  let out := advance snap dep lo hi
  have eqn (e j : Nat) (he : e≤24) (hj : j ≤ 2^(e+1)) :
      cell t (addr e j) = update (cell s) tree d k (addr e j) := by
    unfold update
    split <;> rename_i isDst
    · rw [isDst];exact dst
    split <;> rename_i isRight
    · rw [isRight,pair_contiguous,right,consumed]
      simp
    · have src := apart (aligned32 e j) (aligned32 (d+1) (2*k+1)) isRight
      rw [pair_contiguous] at src
      have clean := frame.frame (addr e j) 32 (room_of_slot he hj)
        (apart (aligned32 e j) (aligned32 d k) isDst) (by omega)
      exact congrArg unpack clean
  constructor
  · intro e j bounds
    rw [eqn e j bounds.1 bounds.2.2.le]
    exact out.1 e j bounds
  · intro e he
    rw [Guard,eqn e (2^(e+1)) (by omega) le_rfl]
    exact out.2 e he

theorem actual_parent (o : Oracle) (im : CommitGolf.Riscv.Image) (s : MachineState) (d : Fin 24)
    (i k : Nat) (lo : 2^d.val ≤ k) (hi : k < 2^(d.val+1))
    (leaves : Nat → Binding.Digest) (canonical : ∀ j, Canonical 24 (leaves j))
    (snap : Snapshot (cell s) (node (rawC o) leaves) d k)
    (inp : srcReg s i+signExtend12 (Image.sourceImm ⟨i%64,by omega⟩) = BitVec.ofNat 64 (addr (d.val+1) (2*k)))
    (out : dstReg s i+signExtend12 (Image.destImm ⟨i%128,by omega⟩) = BitVec.ofNat 64 (addr d k))
    (regs : NodeRegisters d s) (f : Loaded im s.pc (Image.body d i)) :
    ∃ t, Segment o im (Image.body d i).length s t ∧ t.pc=s.pc+BitVec.ofNat 64 (4*(Image.body d i).length) ∧
      Snapshot (cell t) (node (rawC o) leaves) d (k+1) ∧ NodeWrites (addr (d.val+1) (2*k)) (addr d k) s t ∧
      t.getReg .x18=srcReg s i ∧ t.getReg .x19=dstReg s i ∧ t.getReg .x12=BitVec.ofNat 64 (addr d k) ∧
      ∀ q, q ≠ .x6 → q ≠ .x10 → q ≠ .x12 → q ≠ .x18 → q ≠ .x19 → t.getReg q=s.getReg q := by
  have ⟨left,right,blank⟩ := ready_pair snap d.isLt lo hi
  have bounds := parent_memory_bounds d k d.isLt lo hi
  rw [pair_contiguous] at right
  have zero : cell s (addr d k+32)=zeroDigest := by
    rw [show addr d k+32=addr d (k+1) by unfold addr;omega];exact blank
  obtain ⟨t,sg,pc,value,mark,frame,stable⟩ := node_step o im s d i (addr (d.val+1) (2*k)) (addr d k)
    (by unfold MEMORY_BYTES;omega) (by unfold MEMORY_BYTES;omega) (aligned ..) (aligned ..) bounds.2.1 _ _
    (node_canonical (rawC o) leaves (d.val+1) _ (by have := d.isLt;omega) canonical)
    left right zero inp out regs f
  rw [←parent_eq (rawC o) leaves d k d.isLt] at value
  exact ⟨t,sg,pc,snapshot_after_node snap d.isLt lo hi value mark frame,frame,stable⟩

end CommitGolfCandidate.Reconstruction.CommitParents
