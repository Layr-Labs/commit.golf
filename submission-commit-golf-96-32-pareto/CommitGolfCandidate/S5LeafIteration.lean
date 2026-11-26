import CommitGolfCandidate.S5LeafStep
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem update_pc {s k} (H : Compression) (a : AtLeaf s k) (inside : k<LENGTH) :
    (afterUpdates H s k).pc=pcAt (updateStart (slotIndex k)+(updates (slotIndex k)).length) := by
  let i:=slotIndex k
  have pc : s.pc=pcAt (tileSite i 0) := by rw [a.pc,if_pos inside]
  have pre:=exit_pc H s (k/256) i pc
  change (updatesState (afterHashes H s k) i).pc=_
  rw [(update_regs ..).pc,show (afterHashes H s k).pc=pcAt (updateStart i) from pre]
  unfold pcAt
  rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64);dsimp only [i];omega

private theorem post_run {s k} (H : Compression) (a : AtLeaf s k) (inside : k<LENGTH) (fuel : Nat) :
    execute commitImage (fuel+tailCount k) (afterHashes H s k) true=
      (do let r←execute commitImage fuel (afterLeaf H s k) true;return r.charge (tailCount k) 0) := by
  let i:=slotIndex k
  let t:=afterHashes H s k
  let u:=afterUpdates H s k
  have pc : t.pc=pcAt (updateStart i) := exit_pc H s _ _ (by rw [a.pc,if_pos inside])
  by_cases endTile : k%256=255
  · have hi : i=(255:Fin 256):=Fin.ext endTile
    have bpc : u.pc=pcAt 7222 := by rw [show u.pc=pcAt (updateStart i+(updates i).length) from update_pc H a inside,hi,last_branch_pc]
    have eq : u.getReg .x20=0 ↔ ¬k+1<LENGTH := by
      rw [show u.getReg .x20=BitVec.ofNat 64 (65536-(k+1)/256) from updated_count H a inside]
      change k<16777216 at inside
      constructor
      · intro e;have v:=congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at v
        change _=0 at v;change ¬k+1<16777216;omega
      · intro e;change ¬k+1<16777216 at e;rw [show 65536-(k+1)/256=0 by omega];rfl
    unfold tailCount afterLeaf;rw [if_pos endTile,if_pos endTile]
    rw [show fuel+((updates (slotIndex k)).length+branchSteps k)=fuel+branchSteps k+(updates i).length by dsimp [i];omega,
      updates_run i t pc]
    change (do let r←execute commitImage (fuel+branchSteps k) u true;return r.charge (updates i).length 0)=_
    rw [landed_run u k fuel bpc eq]
    simp only [bind_assoc,pure_bind,Execution.charge,Nat.add_zero]
    congr 1;funext r;congr 2 <;> (try dsimp only [i]) <;> omega
  · unfold tailCount afterLeaf;rw [if_neg endTile,if_neg endTile,Nat.add_zero];exact updates_run i t pc fuel

theorem fixed_iteration (o : Oracle) (s : MachineState) (k : Nat) (inside : k<LENGTH) (a : AtLeaf s k) (fuel : Nat) :
    o.run (execute commitImage (fuel+(12+tailCount k)) s true)=
      (do let (out,n)←o.run (execute commitImage fuel (afterLeaf o.compression s k) true)
          return (out.charge (40+tailCount k) 4,4+n)) := by
  let i:=slotIndex k
  have pos : 256*(k/256)+i.val=k:=Nat.div_add_mod k 256
  have pc : s.pc=pcAt (tileSite i 0):=by rw [a.pc,if_pos inside]
  rw [show fuel+(12+tailCount k)=fuel+tailCount k+12 by omega,fixed_leaf o s (k/256) i (toRegs a) pc (by rw [pos];exact inside)]
  change (do let (out,n)←o.run (execute commitImage (fuel+tailCount k) (afterHashes o.compression s k) true); _) = _
  rw [post_run o.compression a inside fuel,oracle_run_bind]
  simp only [bind_assoc,oracle_run_pure,pure_bind,Execution.charge,Nat.add_zero,Nat.zero_add]
  apply bind_congr;rintro ⟨r,n⟩;simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
end CommitGolfCandidate.S5Machine
