import CommitGolfCandidate.ReconstructedCheckCursorImage
import CommitGolfCandidate.ReconstructedCheckParentRun

namespace CommitGolfCandidate.Reconstruction.CheckHeaderPlan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckParentRun CheckCursorImage
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def table : Tables where
  allowed:=fun a=>decide (a.region=3 ∧ a.offset.toNat%8=0 ∧ a.offset.toNat<40)
  initial:=fun _=>none

def start (r : Nat) : State where
  pc:=CommitBlocks.addr 122
  regs:=fun reg=>match reg with
    | .x24=>ptr 1 r
    | .x19=>ptr 4 0
    | _=>.reg reg
  writes:=[]

def run (r : Nat) := CheckCursorOps.run table (decode 122 headCode) (CommitBlocks.addr 175) 61 (start r)
def done (r : Nat) := (run r).getD ⟨0,start r⟩

def word (i : Nat) : Term := .old (loc 3 (8*i))

def shift (left : Bool) (x : Term) (w : Nat) :=
  if w%64=0 then x else .bin (if left then .shl else .shr) x (.lit (BitVec.ofNat 64 (w%64)))

def field (cursor width : Nat) : Term :=
  let off:=cursor%64
  let k:=cursor/64
  let low:=shift false (word k) off
  if 64<off+width then .bin .bitOr (shift true (word (k+1)) (64-off)) low else low

def result (r : Nat) : Prop :=
  let m:=(done r).state
  m.get .x14=field r 64 ∧ m.get .x10=field (r+64) 56 ∧
  m.get .x11=field (r+120) 64 ∧ m.get .x12=field (r+184) 38 ∧
  m.writes=[] ∧ (done r).ticks≤53 ∧
  (∀ reg : Reg, reg≠.x10 → reg≠.x11 → reg≠.x12 → reg≠.x13 → reg≠.x14 → reg≠.x15 → reg≠.x16 →
      m.get reg=(start r).get reg)

def preserve : List Reg := [.x0,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]

def receipt (r : Nat) := let m:=(done r).state
  (run r).isSome && decide (m.get .x14=field r 64 ∧ m.get .x10=field (r+64) 56 ∧
    m.get .x11=field (r+120) 64 ∧ m.get .x12=field (r+184) 38 ∧ m.writes=[] ∧ (done r).ticks≤53) &&
    preserve.all (fun reg=>decide (m.get reg=(start r).get reg))

theorem checked (r : Fin 64) : receipt r=true := by
  exact (by decide +kernel : ∀ k : Fin 64,receipt k=true) r

theorem positive (o : Oracle) (env : Env) (ctx : CheckCursorValues.Context env) (layout : Layout env table)
    (r : Fin 64) (s : MachineState) (initial : Matches env (start r) s) :
    ∃ t, CheckRecorded.Segment o (done r).ticks s t [] ∧ Matches env (done r).state t ∧
      t.pc=CommitBlocks.addr 175 ∧ result r := by
  have ok:=checked r
  simp only [receipt,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  obtain ⟨⟨defined,first,second,third,fourth,memory,cost⟩,keep⟩:=ok
  have replay : run r=some (done r) := by unfold done;cases v:run r <;> simp_all
  obtain ⟨t,seg,h,_,pc⟩:=CheckCursorOps.run_sound o env ctx table layout _ head_decoded _ 61 _ s initial (fun _ h=>by cases h) _ replay
  refine ⟨t,seg,h,pc,first,second,third,fourth,memory,cost,?_⟩
  intro reg a b c d e f g
  apply keep
  cases reg <;> simp_all [preserve]

end CommitGolfCandidate.Reconstruction.CheckHeaderPlan
