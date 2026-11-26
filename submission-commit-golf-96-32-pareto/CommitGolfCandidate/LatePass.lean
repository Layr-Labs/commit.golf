import CommitGolfCandidate.LatePassHeader

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def pass (h : Compression) (s : MachineState) (d : Fin 24) :=
  parentFold h (entered s d) d (levelSize d)

def passSteps (d : Fin 24) := parentBodyPC d-passStart d+levelSteps d (levelSize d)
def passCycles (d : Fin 24) := parentBodyPC d-passStart d+levelCycles d (levelSize d)

theorem pass_run (o : Oracle) (s : MachineState) (d : Fin 24) (en : Entry s (passStart d)) (fuel : Nat) :
    o.run (execute commitImage (fuel+passSteps d) s true) =
      (do let (out,c) ← o.run (execute commitImage fuel (pass o.compression s d) true)
          return (out.charge (passCycles d) (levelSize d),levelSize d+c)) := by
  have length : (headerOps d).length = parentBodyPC d-passStart d := by simp [headerOps]
  rw [show fuel+passSteps d=(fuel+levelSteps d (levelSize d))+(headerOps d).length by unfold passSteps; omega,
    enter_run s d en, oracle_run_bind, parents_run o _ d (enter_frame s d en) (levelSize d) le_rfl fuel]
  simp only [bind_assoc, pure_bind, oracle_run_pure, Execution.charge, Nat.add_zero, Nat.zero_add,
    passCycles,length, Nat.add_assoc,pass]

theorem pass_end (h : Compression) (s : MachineState) (d : Fin 24) (en : Entry s (passStart d)) :
    Entry (pass h s d) (parentEndPC d) := by
  have fr := parents_frame h _ d (enter_frame s d en) (levelSize d) le_rfl
  refine ⟨?_,fr.mode,fr.kind,fr.len,fr.td,fr.root⟩
  simpa only [pass,parentNextPC,lt_self_iff_false,if_false] using fr.pc

theorem pass_nodes (h : Compression) (s : MachineState) (d : Fin 24) (en : Entry s (passStart d))
    (base : Nat → Digest) (tree : LevelsThrough h base d s) (g : Gaps s) :
    LevelsThrough h base (d.val+1) (pass h s d) := by
  have entryMem := enter_mem s d
  have eq := parents_memory h _ d (enter_frame s d en) (levelSize d) le_rfl
  have filled := fill_correct h base (entered s d) d d.isLt
    (fun l hl j hj => (read_congr_mem _ _ _ _ entryMem).trans (tree l hl j hj))
    (fun x p k hp => (read_congr_mem _ _ _ _ entryMem).trans (g x p k hp))
  exact fun l hl j hj => (read_congr_mem _ _ _ _ eq).trans (filled l hl j hj)

theorem pass_gaps (h : Compression) (s : MachineState) (d : Fin 24) (en : Entry s (passStart d)) (g : Gaps s) :
    Gaps (pass h s d) := by
  have eq := parents_memory h _ d (enter_frame s d en) (levelSize d) le_rfl
  have g' := level_keeps_gaps (layerHash h d) (entered s d) d (levelSize d) d.isLt le_rfl
    (fun x p k hp => (read_congr_mem _ _ _ _ (enter_mem s d)).trans (g x p k hp))
  exact fun x p k hp => (read_congr_mem _ _ _ _ eq).trans (g' x p k hp)

theorem pass_salt (h : Compression) (s : MachineState) (d : Fin 24) (en : Entry s (passStart d)) (i : Index) :
    readBuffer (pass h s d) (saltAddress i) 24 = readBuffer s (saltAddress i) 24 :=
  (read_congr_mem _ _ _ _ (parents_memory h _ d (enter_frame s d en) (levelSize d) le_rfl)).trans
    ((all_salts_survive (layerHash h d) d (levelSize d) (entered s d) i le_rfl).trans (read_congr_mem _ _ _ _ (enter_mem s d)))

private theorem replyTarget (s : MachineState) (d : Fin 24) (p : Nat) (w : Digest) :
    (laneReply s d p w).getReg .x12=(parentReady s p).getReg .x12 := by
  unfold laneReply
  rw [MachineState.getReg_setPC]
  exact writeBits_register (parentReady s p) _ _ .x12

attribute [local irreducible] entered parentResult
theorem final_source (h : Compression) (s : MachineState) (en : Entry s (passStart 23)) :
    (pass h s 23).getReg .x12 = BitVec.ofNat 64 (nodeAddress 24 0) := by
  let t := entered s 23
  have addr := (parent_addresses (enter_frame s 23 en).toParentRegs).2
  unfold pass
  rw [show levelSize (23 : Fin 24)=1 by decide,parentFold,parentFold,parentTick,if_neg (by decide : ¬0%16=15)]
  unfold parentResult
  exact (replyTarget _ _ _ _).trans addr

end CommitGolfCandidate.Late
