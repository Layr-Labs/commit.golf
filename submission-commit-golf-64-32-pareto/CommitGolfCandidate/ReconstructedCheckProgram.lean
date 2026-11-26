import CommitGolfCandidate.ReconstructedCheckSpecial

namespace CommitGolfCandidate.Reconstruction.CheckProgram
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckRecorded
set_option maxHeartbeats 1200000

structure Hit where
  ticks : Nat
  state : State

def run (tab : Tables) (lookup : Word→Option CheckSpecial.Op) (target : Word) : Nat→State→Option Hit
  | 0,_=>none
  | n+1,m=>if m.pc=target then some ⟨0,m⟩ else do
    let op ← lookup m.pc
    let next ← CheckSpecial.step tab m op
    let hit ← run tab lookup target n next
    return {hit with ticks:=hit.ticks+1}

theorem sound (o : Oracle) (env : Env) (tab : Tables) (layout : Layout env tab)
    (lookup : Word→Option CheckSpecial.Op)
    (decoded : ∀ s : MachineState, ∀ op, lookup s.pc=some op → fetch image s=some op.instr)
    (target : Word) (fuel : Nat) (m : State) (s : MachineState) (matched : Matches env m s) (safe : Safe tab m.writes)
    (hit : Hit) (receipt : run tab lookup target fuel m=some hit) :
    ∃ t, Segment o hit.ticks s t [] ∧ Matches env hit.state t ∧ Safe tab hit.state.writes ∧ t.pc=target := by
  induction fuel generalizing m s hit with
  | zero=>cases receipt
  | succ n ih=>
    by_cases stop : m.pc=target
    · simp [run,stop] at receipt;subst hit;exact ⟨s,empty _ _,matched,safe,matched.pc.trans stop⟩
    · cases found : lookup m.pc with
      | none=>simp [run,stop,found] at receipt
      | some op=>
        cases next : CheckSpecial.step tab m op with
        | none=>simp [run,stop,found,next] at receipt
        | some v=>
          cases rest : run tab lookup target n v with
          | none=>simp [run,stop,found,next,rest] at receipt
          | some r=>
            simp [run,stop,found,next,rest] at receipt;subst hit
            obtain ⟨u,one,hu,uv⟩ := CheckSpecial.sound o env tab layout m v s matched safe op
              (decoded s op (matched.pc ▸ found)) next
            obtain ⟨t,tail,ht,vt,pc⟩ := ih v u hu uv r rest
            exact ⟨t,by simpa [Nat.add_comm] using compose one tail,ht,vt,pc⟩

end CommitGolfCandidate.Reconstruction.CheckProgram
