import CommitGolfCandidate.LateParentLoop
import CommitGolfCandidate.LateHeaderInterpreter

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def passStart (d : Fin 24) := if d.val=0 then 930 else parentHeaderPC d

def baseAt (n : Nat) : Instr :=
  match decodeInstruction (packedWord n) with
  | some (.base op) => op
  | _ => .EBREAK

def headerOps (d : Fin 24) :=
  (List.range (parentBodyPC d-passStart d)).map fun j => baseAt (passStart d+j)

def entered (s : MachineState) (d : Fin 24) := (headerOps d).foldl execInstrBr s

structure Entry (s : MachineState) (pc : Nat) : Prop where
  atPC : s.pc=pcAt pc
  mode : s.getReg .x5=0
  kind : s.getReg .x13=0
  len : s.getReg .x11=96
  td : s.getReg .x9=4294971424
  root : s.getReg .x26=4294971392

private def seed : KnownRegs
  | .x0 | .x5 | .x13 => some 0
  | .x9 => some 4294971424
  | .x11 => some 96
  | .x26 => some 4294971392
  | _ => none

private theorem seed_ok (s : MachineState) (n : Nat) (e : Entry s n) : Agrees seed s := by
  intro r v eq
  cases r <;> simp only [seed,Option.some.injEq,reduceCtorEq] at eq
  all_goals subst v; first | rfl | exact e.mode | exact e.kind | exact e.len | exact e.td | exact e.root

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem computed : ∀ d : Fin 24,
    let ops := headerOps d
    let q := ops.foldl knownStep seed
    (ops.all setupOp = true) ∧ passStart d+ops.length=parentBodyPC d ∧ parentBodyPC d < 2351 ∧
    (q .x21 = some (BitVec.ofNat 64 (nodeAddress d 0))) ∧
    (q .x22 = some (BitVec.ofNat 64 (nodeAddress (d.val+1) 0))) ∧
    (q .x5 = some 0) ∧ (q .x11 = some 96) ∧ (q .x13 = some 0) ∧
    (16 ≤ levelSize d → q .x20 = some (BitVec.ofNat 64 (levelSize d/16))) ∧
    (q .x9 = some 4294971424) ∧ (q .x26 = some 4294971392) := by decide

private theorem ops_ok (d : Fin 24) (op : Instr) (member : op ∈ headerOps d) : setupOp op :=
  List.all_eq_true.mp (computed d).1 op member

theorem enter_frame (s : MachineState) (d : Fin 24) (entry : Entry s (passStart d)) :
    ParentFrame (entered s d) d 0 := by
  obtain ⟨_,hlen,_,src,dst,m,l,k,count,td,root⟩ := computed d
  have known := known_header (headerOps d) seed s (ops_ok d) (seed_ok s _ entry)
  have pos : ∀ d : Fin 24, 0<levelSize d := by decide
  refine ⟨⟨known _ _ src,known _ _ dst,known _ _ m,known _ _ l,known _ _ k⟩,
    ?_,fun large => known _ _ (count large),known _ _ td,known _ _ root⟩
  have pc := (header_properties (headerOps d) s (ops_ok d)).2
  simp only [parentNextPC,if_pos (pos d),parentPC,Nat.zero_mod,Nat.mul_zero,Nat.add_zero]
  rw [entered,pc,entry.atPC]; unfold pcAt; rw [←BitVec.ofNat_add]
  exact congrArg (BitVec.ofNat 64) (by omega)

theorem enter_mem (s : MachineState) (d : Fin 24) : (entered s d).mem=s.mem :=
  (header_properties (headerOps d) s (ops_ok d)).1

theorem enter_run (s : MachineState) (d : Fin 24) (entry : Entry s (passStart d)) (fuel : Nat) :
    execute commitImage (fuel+(headerOps d).length) s true =
      (do let out ← execute commitImage fuel (entered s d) true; pure (out.charge (headerOps d).length 0)) := by
  apply execute_linear _ _ _ _ entry.atPC (fun op h => header_straight op (ops_ok d op h))
  intro j hj
  have len := (computed d).2.1
  have small := (computed d).2.2.1
  apply decoded_word _ (by omega)
  have eq : (headerOps d)[j] = baseAt (passStart d+j) := by simp only [headerOps,List.getElem_map,List.getElem_range]
  have good := ops_ok d _ (List.getElem_mem hj)
  rw [eq] at good ⊢
  unfold baseAt at good ⊢
  cases h : decodeInstruction (packedWord (passStart d+j)) with
  | none => simp [h,setupOp] at good
  | some x => cases x <;> simp_all [setupOp]

end CommitGolfCandidate.Late
