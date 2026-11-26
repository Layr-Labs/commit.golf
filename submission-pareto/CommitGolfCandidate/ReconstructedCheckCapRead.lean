import CommitGolfCandidate.ReconstructedCheckLowerLayout

namespace CommitGolfCandidate.Reconstruction.CheckCapRead
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckParentRun CheckCursorImage
set_option maxRecDepth 22000
set_option maxHeartbeats 5000000

def code : Array CheckLink.Op := #[
  .plain (.basic (.arith (.srli .x5 .x24 3))),
  .plain (.andi .x7 .x5 4088),
  .plain (.basic (.arith (.rr .add .x7 .x7 .x27))),
  .plain (.basic (.ld .x5 .x7 0)),
  .plain (.andi .x6 .x24 63),
  .plain (.basic (.arith (.rr .shr .x5 .x5 .x24))),
  .plain (.basic (.branch .eq .x6 .x0 108)),
  .plain (.basic (.ld .x7 .x7 8)),
  .plain (.basic (.arith (.rr .sub32 .x28 .x0 .x6))),
  .plain (.basic (.arith (.addi .x29 .x24 64))),
  .plain (.basic (.arith (.srli .x29 .x29 3))),
  .plain (.andi .x29 .x29 4088),
  .plain (.basic (.arith (.rr .add .x29 .x29 .x27))),
  .plain (.basic (.ld .x30 .x29 0)),
  .plain (.basic (.ld .x29 .x29 8)),
  .plain (.basic (.arith (.rr .shl .x7 .x7 .x28))),
  .plain (.basic (.arith (.rr .bitOr .x5 .x7 .x5))),
  .plain (.basic (.arith (.rr .shr .x7 .x30 .x24))),
  .plain (.basic (.arith (.slli .x29 .x29 1))),
  .xori .x28 .x24 4095,
  .plain (.basic (.arith (.addi .x30 .x24 128))),
  .plain (.basic (.arith (.srli .x30 .x30 3))),
  .plain (.andi .x30 .x30 4088),
  .plain (.basic (.arith (.rr .add .x30 .x30 .x27))),
  .plain (.basic (.ld .x31 .x30 0)),
  .plain (.basic (.ld .x30 .x30 8)),
  .plain (.basic (.arith (.rr .shl .x29 .x29 .x28))),
  .plain (.basic (.arith (.rr .bitOr .x7 .x29 .x7))),
  .plain (.basic (.arith (.rr .shr .x29 .x31 .x24))),
  .plain (.basic (.arith (.slli .x30 .x30 1))),
  .plain (.basic (.arith (.rr .shl .x28 .x30 .x28))),
  .plain (.basic (.arith (.rr .bitOr .x28 .x28 .x29))),
  .plain (.basic (.jal .x0 36)),
  .plain (.basic (.arith (.addi .x7 .x24 64))),
  .plain (.basic (.arith (.srli .x7 .x7 3))),
  .plain (.basic (.arith (.rr .add .x7 .x7 .x27))),
  .plain (.basic (.ld .x7 .x7 0)),
  .plain (.basic (.arith (.addi .x28 .x24 128))),
  .plain (.basic (.arith (.srli .x28 .x28 3))),
  .plain (.basic (.arith (.rr .add .x28 .x28 .x27))),
  .plain (.basic (.ld .x28 .x28 0)),
  .plain (.basic (.arith (.addi .x29 .x24 192))),
  .plain (.basic (.arith (.srli .x29 .x29 3))),
  .plain (.andi .x30 .x29 4088),
  .plain (.basic (.arith (.rr .add .x30 .x30 .x27))),
  .plain (.basic (.ld .x29 .x30 0)),
  .plain (.basic (.arith (.rr .add .x31 .x13 .x6))),
  .plain (.basic (.arith (.rr .shr .x29 .x29 .x6))),
  .plain (.basic (.branch .lt .x31 .x1 7956)),
  .plain (.basic (.ld .x30 .x30 8)),
  .plain (.basic (.arith (.rr .sub32 .x6 .x0 .x6))),
  .plain (.basic (.arith (.rr .shl .x6 .x30 .x6))),
  .plain (.basic (.arith (.rr .bitOr .x29 .x6 .x29))),
  .plain (.basic (.jal .x0 2096896))]

theorem decoded : ∀ s : MachineState,∀ op,decode 495 code s.pc=some op→fetch image s=some op.instr :=
  decode_sound 495 code (by decide) (by unfold agree;decide +kernel)

def start (r w : Nat) : State where
  regs:=fun reg=>match reg with
    | .x24=>ptr 1 r
    | .x27=>ptr 4 0
    | .x13=>.lit (BitVec.ofNat 64 (w-192))
    | .x14=>.lit (BitVec.ofNat 64 (2^(w-192)-1))
    | .x1=>.lit 65
    | _=>.reg reg
  pc:=CommitBlocks.addr 495
  writes:=[]

def run (r w : Nat) := CheckCursorOps.run CheckHeaderPlan.table (decode 495 code) (CommitBlocks.addr 484) 60 (start r w)
def done (r w : Nat) := (run r w).getD ⟨0,start r w⟩

def receipt (r w : Nat) :=
  let m:=(done r w).state
  (run r w).isSome && decide (m.get .x5=CheckHeaderPlan.field r 64 ∧ m.get .x7=CheckLowerPlan.middle r 1 ∧
    m.get .x28=CheckLowerPlan.middle r 2 ∧ m.get .x29=CheckHeaderPlan.field (r+192) (w-192) ∧
    m.get .x14=.lit (BitVec.ofNat 64 (2^(w-192)-1)) ∧ m.writes=[] ∧ (done r w).ticks≤54)

private theorem wide0 : ∀ j : Fin 8, receipt (0+j.val) 240=true := by decide +kernel
private theorem wide1 : ∀ j : Fin 8, receipt (8+j.val) 240=true := by decide +kernel
private theorem wide2 : ∀ j : Fin 8, receipt (16+j.val) 240=true := by decide +kernel
private theorem wide3 : ∀ j : Fin 8, receipt (24+j.val) 240=true := by decide +kernel
private theorem wide4 : ∀ j : Fin 8, receipt (32+j.val) 240=true := by decide +kernel
private theorem wide5 : ∀ j : Fin 8, receipt (40+j.val) 240=true := by decide +kernel
private theorem wide6 : ∀ j : Fin 8, receipt (48+j.val) 240=true := by decide +kernel
private theorem wide7 : ∀ j : Fin 8, receipt (56+j.val) 240=true := by decide +kernel
private theorem wide (r : Fin 64) : receipt r 240=true := by
  let j : Fin 8:=⟨r.val%8,by omega⟩
  let k : Fin 8:=⟨r.val/8,by have:=r.isLt;omega⟩
  have idx : r.val=8*k.val+j.val:=by change r.val=8*(r.val/8)+r.val%8;omega
  rw [idx]
  generalize k=z
  fin_cases z
  · exact wide0 j
  · exact wide1 j
  · exact wide2 j
  · exact wide3 j
  · exact wide4 j
  · exact wide5 j
  · exact wide6 j
  · exact wide7 j

private theorem narrow0 : ∀ j : Fin 8, receipt (0+j.val) 224=true := by decide +kernel
private theorem narrow1 : ∀ j : Fin 8, receipt (8+j.val) 224=true := by decide +kernel
private theorem narrow2 : ∀ j : Fin 8, receipt (16+j.val) 224=true := by decide +kernel
private theorem narrow3 : ∀ j : Fin 8, receipt (24+j.val) 224=true := by decide +kernel
private theorem narrow4 : ∀ j : Fin 8, receipt (32+j.val) 224=true := by decide +kernel
private theorem narrow5 : ∀ j : Fin 8, receipt (40+j.val) 224=true := by decide +kernel
private theorem narrow6 : ∀ j : Fin 8, receipt (48+j.val) 224=true := by decide +kernel
private theorem narrow7 : ∀ j : Fin 8, receipt (56+j.val) 224=true := by decide +kernel
private theorem narrow (r : Fin 64) : receipt r 224=true := by
  let j : Fin 8:=⟨r.val%8,by omega⟩
  let k : Fin 8:=⟨r.val/8,by have:=r.isLt;omega⟩
  have idx : r.val=8*k.val+j.val:=by change r.val=8*(r.val/8)+r.val%8;omega
  rw [idx]
  generalize k=z
  fin_cases z
  · exact narrow0 j
  · exact narrow1 j
  · exact narrow2 j
  · exact narrow3 j
  · exact narrow4 j
  · exact narrow5 j
  · exact narrow6 j
  · exact narrow7 j

theorem positive (o : Oracle) (env : Env) (ctx : CheckCursorValues.Context env) (layout : Layout env CheckHeaderPlan.table)
    (r : Fin 64) (w : Nat) (range : w=224 ∨ w=240) (s : MachineState) (initial : Matches env (start r w) s) :
    ∃ t, CheckRecorded.Segment o (done r w).ticks s t [] ∧ Matches env (done r w).state t ∧ t.pc=CommitBlocks.addr 484 ∧
      (done r w).state.get .x5=CheckHeaderPlan.field r 64 ∧ (done r w).state.get .x7=CheckLowerPlan.middle r 1 ∧
      (done r w).state.get .x28=CheckLowerPlan.middle r 2 ∧ (done r w).state.get .x29=CheckHeaderPlan.field (r.val+192) (w-192) ∧
      (done r w).state.get .x14=.lit (BitVec.ofNat 64 (2^(w-192)-1)) ∧ (done r w).state.writes=[] ∧ (done r w).ticks≤54 := by
  have ok : receipt r w=true := by rcases range with h|h <;> subst w;exact narrow r;exact wide r
  simp only [receipt,Bool.and_eq_true,decide_eq_true_eq] at ok
  have replay : run r w=some (done r w) := by have defn:=(ok.1);unfold done;cases v:run r w <;> simp_all
  obtain ⟨t,seg,h,_,pc⟩:=CheckCursorOps.run_sound o env ctx _ layout _ decoded _ 60 _ s initial (fun _ h=>by cases h) _ replay
  exact ⟨t,seg,h,pc,ok.2⟩

end CommitGolfCandidate.Reconstruction.CheckCapRead
