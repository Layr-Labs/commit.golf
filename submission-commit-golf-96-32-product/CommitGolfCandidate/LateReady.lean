import CommitGolfCandidate.LateSetupFrame
import CommitGolfCandidate.LateLeafLoop

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def hashSetup : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 96, .ADDI .x13 .x0 0,
   .ADDI .x20 .x0 256, .SLLI .x20 .x20 11, .ADDI .x20 .x20 0,
   .LUI .x29 1, .ADD .x8 .x8 .x29, .ADDI .x8 .x8 2048]

def ready (s : MachineState) := hashSetup.foldl execInstrBr s

theorem run_ready (s : MachineState) (pc : s.pc = pcAt 530) (fuel : Nat) :
    execute commitImage (fuel+9) s true =
      (do let r ← execute commitImage fuel (ready s) true
          return r.charge 9 0) := by
  apply execute_linear hashSetup 530 s fuel pc
  · intro op present; simp only [hashSetup,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with h|h|h|h|h|h|h|h|h <;> subst op <;> intro q <;> exact ⟨rfl,rfl,rfl⟩
  · intro i hi t tp
    change i < 9 at hi
    have e := smallWord (530+i) (by omega) (by omega)
    obtain ⟨w,eq,dec⟩ : ∃ w, leafWords[530+i-528]? = some w ∧ decodeInstruction w =
        some (.base (hashSetup[i]'hi)) := by interval_cases i <;> exact ⟨_,rfl,rfl⟩
    exact (fetch_word tp (by omega) (e.trans eq)).trans dec

def sampled (m : Message) (ws : List PairCoins) :=
  applyPairs 0 (setupState (startState m) 16) ws

private theorem ready_frame (q : MachineState) :
    (ready q).pc=q.pc+36 ∧ (ready q).getReg .x20=524288 ∧ (ready q).getReg .x29=4096 ∧
    (ready q).getReg .x5=0 ∧ (ready q).getReg .x11=96 ∧ (ready q).getReg .x13=0 := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · change q.pc+4+4+4+4+4+4+4+4+4=_
    simp only [BitVec.add_assoc]; rfl
  all_goals simp [ready, hashSetup, execInstrBr, MachineState.setPC, MachineState.setReg,
    MachineState.getReg,signExtend12]

private theorem ready_mem (q : MachineState) : (ready q).mem = q.mem := rfl

theorem hash_start (m : Message) (ws : List PairCoins) (len : ws.length = pairCount) :
    AtLeaf (ready (sampled m ws)) 0 := by
  let s := setupState (startState m) 16
  let t := sampled m ws
  have state := apply_pairs_invariant ws 0 s (setup_pair _ rfl rfl) (by omega)
  have ip : t.pc = pcAt 530 := by change (applyPairs 0 s ws).pc = _; simpa only [Nat.zero_add,len,lt_self_iff_false,if_false] using state.pc
  obtain ⟨x8,x9,x18,x23,x26⟩ := setup_frame (startState m) rfl rfl rfl
  have kept (reg : Reg) (a : Reg.x10 ≠ reg) (b : Reg.x20 ≠ reg) : t.getReg reg = s.getReg reg :=
    unchanged_draws _ _ _ _ a b
  obtain ⟨pc,ctr,stride,sel,length,kind⟩ := ready_frame t
  constructor
  · change (ready t).pc = pcAt 539
    rw [pc,ip]; rfl
  · have biased : (ready t).getReg .x8 = t.getReg .x8+2048 := by
      change t.getReg .x8 + 4096 + signExtend12 2048 = _
      rw [BitVec.add_assoc]
      rfl
    rw [biased,(kept _ (by decide) (by decide)).trans x8]
    rfl
  · exact (kept _ (by decide) (by decide)).trans x18
  · exact (kept _ (by decide) (by decide)).trans x23
  · exact ctr
  · exact stride
  · exact (kept _ (by decide) (by decide)).trans x9
  · exact (kept _ (by decide) (by decide)).trans x26
  · exact sel
  · exact length
  · exact kind

theorem ready_contents (m : Message) (h : Compression) (ws : List PairCoins) (len : ws.length=pairCount) :
    LeafContents h m (wordTape ws) 0 (ready (sampled m ws)) :=
  contents_congr (ready_mem (sampled m ws))
    (sampled_contents m h ws len)

end CommitGolfCandidate.Late
