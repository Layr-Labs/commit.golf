import CommitGolfCandidate.S5CapBranch
import CommitGolfCandidate.S5CapLatch
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape node)
open Writer (widths)
structure CapRegs (s : MachineState) (p : Nat) : Prop where
  pc : s.pc=pcAt (if p<171 then 355 else 381)
  counter : s.getReg .x22=W p
  end_ : s.getReg .x9=W 171
  marks : s.getReg .x21=W 1024
  lower : s.getReg .x14=W (layerBase 15)
  upper : s.getReg .x15=W (layerBase 16)
  proof : s.getReg .x18=W proofBase

theorem slot_eq (tree : Levels) (xs : List Index) (p : Nat) :
    let l:=(flags xs p).1;let r:=(flags xs p).2
    S5.slot tree xs p=(230,(node tree (slotLevel l r) (slotIndex p l r)).toNat) := by
  dsimp only [S5.slot,flags,slotLevel,slotIndex,secondSide]
  split <;> simp_all

def costAt (xs : List Index) (p : Nat) := Writer.capCost (flags xs p).1 (flags xs p).2
theorem cap_field (s : MachineState) (p : Nat) (hp : p<171) (xs : List Index) (tree : Levels) (salt : SaltTape)
    (fs : List S5.Field) (size : xs.length≤LENGTH) (lim : widths fs≤555170)
    (old : CapRegs s p) (env : InputRows s xs xs tree salt) (cur : FieldCursor tree s fs) :
    let cost:=costAt xs p+(Writer.measureField ⟨widths fs%64,0⟩ 230).cycles
    ∃ t,Runs s t cost cost ∧ CapRegs t (p+1) ∧ InputRows t xs xs tree salt ∧ FieldCursor tree t (fs++[S5.slot tree xs p]) := by
  let l:=(flags xs p).1
  let r:=(flags xs p).2
  let d:=slotLevel l r
  let j:=slotIndex p l r
  have layer : d≤16:=by dsimp [d,slotLevel];split <;> decide
  have span : S5.bits d=230:=by dsimp [d,slotLevel];split <;> decide
  obtain ⟨u,fetch,ip,src,mem,keep⟩:=cap_source s xs p hp env.marks (old.pc.trans (by rw [if_pos hp])) old.marks old.counter old.lower old.upper
  have indexOk:=slot_fits p hp l r
  have bounds:=node_ok d j indexOk
  have cu:=cursor_same cur mem (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide)) (keep _ (by decide))
  have val:=env.sources.node d (show d≤LOG_LENGTH from layer.trans (by decide)) j indexOk
  have write:=put_field u .cap fs tree (nodeAddress d j) 32 (node tree d j) cu ip src bounds.2.2
    (bounds.2.1.trans (by decide)) lim (fun fits=>by simpa only [span,EmitSite.width] using fits d layer j)
    ((read_congr_mem u s _ 32 mem).trans val) (by decide)
  let v:=emitted .cap (widths fs) u
  have kept (q : Reg) (valid : Writer.preserved q) (q1 : q≠.x1) (q11 : q≠.x11)
      (safe : q∉([.x6,.x7,.x10,.x28,.x29] : List Reg)) : v.getReg q=s.getReg q :=
    (write.keep q valid q1 q11).trans (keep q safe)
  obtain ⟨back,ep,idx,eq,same⟩:=cap_latch v p hp write.pc
    ((kept _ (by simp [Writer.preserved]) (by decide) (by decide) (by decide)).trans old.counter)
    ((kept _ (by simp [Writer.preserved]) (by decide) (by decide) (by decide)).trans old.end_)
  let t:=pathEnd v capLatch
  have ct:=cursor_same write.cursor eq (same _ (by decide)) (same _ (by decide)) (same _ (by decide)) (same _ (by decide))
  have reg : CapRegs t (p+1) := by
    refine ⟨ep,idx,?_,?_,?_,?_,?_⟩
    all_goals apply (same _ (by decide)).trans;apply (kept _ (by simp [Writer.preserved]) (by decide) (by decide) (by decide)).trans
    all_goals first | exact old.end_ | exact old.marks | exact old.lower | exact old.upper | exact old.proof
  refine ⟨t,?_,reg,inputs_mem (inputs_below (inputs_mem env mem) size write.low) eq,?_⟩
  · have all:=(fetch.trans write.run).trans back
    have enough : 4≤costAt xs p := (by decide : ∀ a b : Bool,4≤Writer.capCost a b) l r
    let a:=costAt xs p
    let b:=(Writer.measureField ⟨widths fs%64,0⟩ 230).cycles
    change Runs s t (a-4+(2+b)+2) (a-4+(2+b)+2) at all
    change Runs s t (a+b) (a+b)
    have good : 4≤a:=enough
    have eqn : a-4+(2+b)+2=a+b:=by omega
    simpa only [eqn] using all
  · rw [slot_eq];exact ct
end CommitGolfCandidate.S5Machine.Open
