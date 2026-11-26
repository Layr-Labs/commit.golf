import CommitGolfCandidate.ReconstructedCheckParentImage

namespace CommitGolfCandidate.Reconstruction.CheckParentRun
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary CheckParentImage CheckRecorded
set_option maxHeartbeats 1500000

structure Hit where
  steps : Nat
  state : State
  site : Fin 122

def next (tab : Tables) : Nat→State→Option Hit
  | 0,_ => none
  | n+1,m => do
    let i ← find m.pc
    match entry i with
    | .plain op =>
      let newState ← step tab m op
      let result ← next tab n newState
      return {result with steps:=result.steps+1}
    | _ => return ⟨0,m,i⟩

theorem sound (o : Oracle) (env : Env) (tab : Tables) (layout : Layout env tab)
    (n : Nat) (m : State) (s : MachineState) (matched : Matches env m s) (safe : Safe tab m.writes)
    (hit : Hit) (checked : next tab n m=some hit) :
    ∃ t, Segment o hit.steps s t [] ∧ Matches env hit.state t ∧ Safe tab hit.state.writes ∧
      t.pc=CommitBlocks.addr (674+hit.site.val) := by
  induction n generalizing m s hit with
  | zero => cases checked
  | succ n ih =>
    cases found : find m.pc with
    | none => simp [next,found] at checked
    | some i =>
      have pc := matched.pc.trans (find_pc found)
      cases a : entry i with
      | plain op =>
        cases advanced : step tab m op with
        | none => simp [next,found,a,advanced] at checked
        | some v =>
          cases res : next tab n v with
          | none => simp [next,found,a,advanced,res] at checked
          | some r =>
            simp [next,found,a,advanced,res] at checked;subst hit
            have word := fetch_action i s pc
            rw [a] at word
            obtain ⟨u,seg,hm,ok⟩ := CheckOrdinary.sound o env tab layout m v s matched safe op word advanced
            obtain ⟨t,rest,final,unspoiled,last⟩ := ih v u hm ok r res
            exact ⟨t,by simpa [Nat.add_comm] using compose seg rest,final,unspoiled,last⟩
      | oracle site | ret =>
        simp [next,found,a] at checked;subst hit
        exact ⟨s,empty o s,matched,safe,pc⟩

def loc (region offset : Nat) : Loc := ⟨region,BitVec.ofNat 64 offset⟩
def ptr (region offset : Nat) : Term := .ptr (loc region offset)

def ro (offset : Nat) : Option Word :=
  if 2097560≤offset ∧ offset<2097760 then
    some (BitVec.ofNat 64 (modulus ((offset-2097560)/8)))
  else if 2097760≤offset ∧ offset<2097960 then
    some (BitVec.ofNat 64 (width ((offset-2097760)/8)))
  else if 2097960≤offset ∧ offset<2098152 then
    some (BitVec.ofNat 64 (sameSize.calls[(offset-2097960)/8]?.getD 0))
  else none

def table : Tables where
  allowed := fun a => decide (a.offset.toNat%8=0) &&
    match a.region with
    | 0 => (ro a.offset.toNat).isSome
    | 1 => decide (a.offset.toNat < 144)
    | 2 => decide (a.offset.toNat < 64)
    | 3 => decide (a.offset.toNat < 32)
    | _ => false
  initial := fun a=> if a.region=0 ∧ a.offset.toNat%8=0 then ro a.offset.toNat else none

def start (d : Nat) : State where
  regs := fun r=> match r with
    | .x2 => ptr 1 144
    | .x10 => ptr 3 0
    | .x11 => .lit (BitVec.ofNat 64 d)
    | .x12 => ptr 2 0
    | _ => .reg r
  writes := []
  pc:=CommitBlocks.addr 674

def initialArgs (s : MachineState) (env : Env) (d : Nat) :=
  env.initial=s ∧ s.pc=CommitBlocks.addr 674 ∧ s.getReg .x2=physical env (loc 1 144) ∧
    s.getReg .x10=physical env (loc 3 0) ∧ s.getReg .x11=BitVec.ofNat 64 d ∧
    s.getReg .x12=physical env (loc 2 0)

theorem initial_matches (s : MachineState) (env : Env) (d : Nat) (args : initialArgs s env d) :
    Matches env (start d) s := by
  obtain ⟨init,pc,stack,out,depth,pair⟩ := args
  refine ⟨pc,?_,fun q=>by simp [start,memory,init]⟩
  intro r
  cases r <;> simp [State.get,start,ptr,Term.val,init,MachineState.getReg] <;> assumption

end CommitGolfCandidate.Reconstruction.CheckParentRun
