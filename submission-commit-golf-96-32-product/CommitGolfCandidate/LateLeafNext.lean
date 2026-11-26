import CommitGolfCandidate.LateLeafControl

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem updated_pc_table : ∀ i : Fin 32, latchStart i + (updates i).length =
    if i.val=31 then 929 else leafPC ((i.val+1)%32) 0 := by decide

private theorem finish_branch (s : MachineState) : leafBranch s =
    if s.getReg .x20 != 0 then s.setPC (s.pc+signExtend13 6632) else s.setPC (s.pc+4) := rfl

private theorem nonpc (h : Compression) (s : MachineState) (k : Nat) (r : Reg) :
    (afterLeaf h s k).getReg r =
    (updatesState (finalLeafState h s (k/32) (slotIndex k)) (slotIndex k)).getReg r := by
  have choose (q : MachineState) (cond : Bool) (yes no : Word) :
      (if cond then q.setPC yes else q.setPC no).getReg r = q.getReg r := by
    cases cond <;> exact MachineState.getReg_setPC
  by_cases e : (slotIndex k).val=31
  · simp only [afterLeaf,if_pos e,finish_branch]
    exact choose _ _ _ _
  · simp only [afterLeaf,if_neg e]

theorem tail_mem (h : Compression) (s : MachineState) (k : Nat) :
    (afterLeaf h s k).mem = (finalLeafState h s (k/32) (slotIndex k)).mem := by
  let f := finalLeafState h s (k/32) (slotIndex k)
  have eq := (update_regs f (slotIndex k)).mem
  have br (t : MachineState) : (leafBranch t).mem = t.mem := by
    have choose (cond : Bool) (yes no : Word) :
        (if cond then t.setPC yes else t.setPC no).mem = t.mem := by cases cond <;> rfl
    exact choose (t.getReg .x20 != 0) (t.pc+signExtend13 6632) (t.pc+4)
  by_cases e : (slotIndex k).val=31
  · simp only [afterLeaf,if_pos e]
    exact (br _).trans eq
  · simpa only [afterLeaf,if_neg e] using eq

private theorem ofAdd (n k : Nat) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 k = BitVec.ofNat 64 (n+k) := (BitVec.ofNat_add ..).symm

theorem after_regs (h : Compression) (s : MachineState) (k : Nat) (inside : k < LENGTH)
    (a : AtLeaf s k) : AtLeaf (afterLeaf h s k) (k+1) := by
  let i := slotIndex k
  let f := finalLeafState h s (k/32) i
  let t := updatesState f i
  have keep (r : Reg) (h₁ : Reg.x10 ≠ r) (h₂ : Reg.x12 ≠ r) :
      f.getReg r = s.getReg r := final_keeps h s _ i _ h₁ h₂
  have unchanged (r : Reg) (h₁ : Reg.x10 ≠ r) (h₂ : Reg.x12 ≠ r) (h₃ : Reg.x8 ≠ r)
      (h₄ : Reg.x18 ≠ r) (h₅ : Reg.x23 ≠ r) (h₆ : Reg.x20 ≠ r) :
      (afterLeaf h s k).getReg r = s.getReg r :=
    (nonpc h s k r).trans ((update_keeps f i r h₃ h₄ h₅ h₆).trans (keep r h₁ h₂))
  have ur := update_regs f i
  have lt : k < 16777216 := inside
  have rem (x : Nat) : i.val = k%32 := rfl
  have c : t.getReg .x20 = BitVec.ofNat 64 (524288-(k+1)/32) := by
    rw [ur.count,keep _ (by decide) (by decide),a.counter]
    change (if k%32=31 then _ else _) = _
    split
    · exact (BitVec.ofNat_sub_ofNat_of_le (w := 64) (524288-k/32) 1 (by decide) (by omega)).trans
        (congrArg (BitVec.ofNat 64) (by omega))
    · apply congrArg (BitVec.ofNat 64); omega
  constructor
  · have pc := a.pc; rw [if_pos inside] at pc
    have tp : t.pc = pcAt (latchStart i+(updates i).length) := by
      rw [ur.pc, exit_pc _ _ _ _ pc]; unfold pcAt; rw [←BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64); dsimp only [i]; omega
    rw [updated_pc_table] at tp
    change (if i.val=31 then leafBranch t else t).pc = _
    by_cases e : i.val=31
    · simp only [e,if_true] at tp ⊢
      rw [finish_branch, c, tp]
      by_cases last : k+1=LENGTH
      · have z : 524288-(k+1)/32=0 := by rw [last]; decide
        rw [z,if_neg (by omega : ¬ k+1 < LENGTH)]; rfl
      · have more : k+1<LENGTH := by omega
        have b : 0 < 524288-(k+1)/32 := by change k+1 < 16777216 at more; omega
        have ne : BitVec.ofNat 64 (524288-(k+1)/32) ≠ 0 := by
          intro e; have n := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at n
          change _ = 0 at n; omega
        rw [if_pos (bne_iff_ne.mpr ne), if_pos more]
        have z : (slotIndex (k+1)).val = 0 := by change k%32=31 at e; change (k+1)%32=0; omega
        rw [z]; rfl
    · have mod : (i.val+1)%32 = (slotIndex (k+1)).val := by change (k%32+1)%32=(k+1)%32; omega
      have more : k+1<LENGTH := by change k%32≠31 at e; change k+1<16777216; omega
      simpa only [if_neg e,mod,if_pos more] using tp
  · rw [nonpc,ur.message,keep _ (by decide) (by decide),keep _ (by decide) (by decide),a.message,a.stride]
    change (if k%32%16=15 then _ else _) = _
    split
    · rw [BitVec.add_assoc, BitVec.add_comm (2048 : Word) 4096, ←BitVec.add_assoc]
      apply congrArg (fun w : Word => w+2048)
      change BitVec.ofNat 64 _ + BitVec.ofNat 64 4096 = _
      rw [ofAdd]; apply congrArg (BitVec.ofNat 64); unfold msgAddr; omega
    · apply congrArg (fun w : Word => w+2048)
      apply congrArg (BitVec.ofNat 64); unfold msgAddr; omega
  · rw [nonpc,ur.row,keep _ (by decide) (by decide),a.rows]
    change (if k%32%16=15 then _ else _) = _
    split
    · change BitVec.ofNat 64 _ + BitVec.ofNat 64 1536 = _
      rw [ofAdd]; apply congrArg (BitVec.ofNat 64); unfold rowAddr; omega
    · apply congrArg (BitVec.ofNat 64); unfold rowAddr; omega
  · rw [nonpc,ur.nodes,keep _ (by decide) (by decide),a.nodes]
    change (if k%32=31 then _ else _) = _
    split
    · change BitVec.ofNat 64 _ + BitVec.ofNat 64 1536 = _
      rw [ofAdd]; apply congrArg (BitVec.ofNat 64); unfold nodeAddress gapOffset; omega
    · apply congrArg (BitVec.ofNat 64); unfold nodeAddress gapOffset; omega
  · exact (nonpc ..).trans c
  all_goals first | exact (unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.stride
                  | exact (unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.base
                  | exact (unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.root
                  | exact (unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.selector
                  | exact (unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.len
                  | exact (unchanged _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans a.kind

end CommitGolfCandidate.Late
