import CommitGolfCandidate.GroupOpenAlignedCode

namespace TwoPermutationPrototype.GroupedOpening.AlignedFields
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Wide Shifted30 CapCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

theorem copy_body_run (c : Fin 4) (k : Fin 11) (s : MachineState) (S T : Nat)
    (pc : s.pc=pcAt (start c k+3)) (src : s.getReg .x7=BitVec.ofNat 64 S)
    (dst : s.getReg .x21=BitVec.ofNat 64 T) (sa : S%8=0) (ta : T%2=0)
    (r : T%8=residue c k) (apart : S+30 ≤ T) (room : T+30 ≤ MEMORY_BYTES) :
    Done s (copyBody (T%8) s) S T 30 (cost T) (start c k+3+cost T) := by
  have b := code_fits c k
  have ce : cost T = cost (residue c k) := by
    simp only [cost, ← r, Nat.mod_mod]
  by_cases d : residue c k=0
  · have cls : T%8=0 := r.trans d
    have z : cost T=10 := by simp [cost, cls]
    obtain ⟨ca,cb,cc⟩ := dwords_code c k d
    have a := pairs s S T (start c k+3) 0 8 3 (by decide) ca (by omega) pc src dst sa cls
      (by decide) (by omega) (by omega)
    have b1 := pairs _ S T (start c k+3+6) 24 4 1 (by decide) cb (by omega) a.pc
      ((a.regs _ (by decide)).trans src) ((a.regs _ (by decide)).trans dst)
      (by omega) (by omega) (by decide) (by omega) (by omega)
    have ab := append a b1 (by omega) (by omega)
    have last := pairs _ S T (start c k+3+8) 28 2 1 (by decide) cc (by omega) b1.pc
      ((ab.regs _ (by decide)).trans src) ((ab.regs _ (by decide)).trans dst)
      (by omega) (by omega) (by decide) apart room
    simpa [copyBody,cls,z,Nat.add_assoc] using append ab last apart room
  · by_cases f : residue c k=4
    · have cls : T%8=4 := r.trans f
      have z : cost T=16 := by simp [cost, cls]
      obtain ⟨ca,cb⟩ := words_code c k f
      have a := pairs s S T (start c k+3) 0 4 7 (by decide) ca (by omega) pc src dst
        (by omega) (by omega) (by decide) (by omega) (by omega)
      have last := pairs _ S T (start c k+3+14) 28 2 1 (by decide) cb (by omega) a.pc
        ((a.regs _ (by decide)).trans src) ((a.regs _ (by decide)).trans dst)
        (by omega) (by omega) (by decide) apart room
      simpa [copyBody,cls,z,Nat.add_assoc] using append a last apart room
    · have h0 : T%8 ≠ 0 := by omega
      have h4 : T%8 ≠ 4 := by omega
      have z : cost T=22 := by simp [cost,h0,h4]
      have step := copy30_done (start c k+3) s S T (by omega) (shifted_code c k d f) pc src dst sa
        (by omega) apart (by omega) room
      simp only [copyBody, if_neg h0, if_neg h4, z]
      exact ⟨step.run,step.pc,step.regs,step.bytes,step.below⟩


theorem head_run (c : Fin 4) (k : Fin 11) (s : MachineState)
    (pc : s.pc = pcAt (start c k)) : RunsOpeningBlock s (headPrefix s 3) 3 := by
  exact code_run headCode _ s (by have := code_fits c k; change _+3≤_; omega)
    (head_code c k) ⟨rfl,rfl,rfl,trivial⟩ pc
    (by intro i hi; simp only [headCode,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl <;> rfl)
    (by intro u i hi; simp only [headCode,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl <;> rfl)

theorem tail_run (c : Fin 4) (k : Fin 11) (s : MachineState) (l : Fin 14) (width : siblingWidth l=30)
    (pc : s.pc = pcAt (start c k+3+cost (residue c k))) :
    RunsOpeningBlock s (tailPrefix s l 2) 2 := by
  have e : tailCode l = [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1] := by simp [tailCode,width]
  unfold tailPrefix
  rw [e]
  exact code_run [.ADDI .x21 .x21 30, .SRLI .x6 .x6 1] _ s
    (by have := code_fits c k; change _+2≤_; omega) (tail_code c k) ⟨rfl,rfl,trivial⟩ pc
    (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl <;> rfl)
    (by intro u i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl <;> rfl)

private def selectorRows : List Instr :=
  [.ANDI .x31 .x21 7, .SLLI .x31 .x31 9, .LUI .x29 3, .ADD .x31 .x31 .x29]

def dispatch (s : MachineState) : MachineState :=
  execInstrBr (execCode (execInstrBr s (.JAL .x0 7016)) selectorRows) (.JALR .x0 .x31 0)

theorem dispatch_run (s : MachineState) (c : Fin 4) (pc : s.pc=pcAt 222)
    (sel : s.getReg .x21 &&& signExtend12 7 = BitVec.ofNat 64 (2*c.val)) :
    RunsOpeningBlock s (dispatch s) 6 ∧ (dispatch s).pc = pcAt (start c 0) ∧
    (dispatch s).mem=s.mem ∧ ∀ r, r ≠ .x31 → r ≠ .x29 → (dispatch s).getReg r=s.getReg r := by
  let entry := execInstrBr s (.JAL .x0 7016)
  let mid := execCode entry selectorRows
  have hop := run_step s 222 (.JAL .x0 7016) (by decide) pc (by decide +kernel) rfl rfl
  have pc1 : entry.pc=pcAt 1976 := by change s.pc+signExtend21 7016=_; rw [pc]; rfl
  have setup : RunsOpeningBlock entry mid 4 := code_run selectorRows 1976 entry
    (by decide) (by unfold CodeAt; decide +kernel) ⟨rfl,rfl,rfl,rfl,trivial⟩ pc1
    (by intro i hi; simp only [selectorRows,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> rfl)
    (by intro u i hi; simp only [selectorRows,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl <;> rfl)
  have pc2 : mid.pc=pcAt 1980 := by change entry.pc+4+4+4+4=_; rw [pc1]; rfl
  have finish := run_step mid 1980 (.JALR .x0 .x31 0) (by decide) pc2 (by decide +kernel) rfl rfl
  refine ⟨(hop.next setup).next finish, ?_, rfl, ?_⟩
  · change ((((s.getReg .x21 &&& signExtend12 7) <<< (9 : Nat)) + (12288#64) + 0) &&& ~~~1#64) = _
    rw [sel]
    fin_cases c <;> decide
  · intro r h31 h29
    simp [dispatch, selectorRows, execCode, execInstrBr, Ne.symm h31, Ne.symm h29,
      Opening.getReg_setReg]

private def returnOffset (c : Nat) := BitVec.ofNat 21 (2^21+4*607-4*(start c 11))

private theorem return_table : ∀ c : Fin 4, Decodes (start c 11) (.JAL .x0 (returnOffset c)) ∧
    pcAt (start c 11)+signExtend21 (returnOffset c)=pcAt 607 ∧ start c 11<3072 := by decide +kernel

theorem return_run (s : MachineState) (c : Fin 4) (pc : s.pc=pcAt (start c 11)) :
    RunsOpeningBlock s (s.setPC (pcAt 607)) 1 := by
  obtain ⟨code,dest,fit⟩ := return_table c
  have h := run_step s _ _ (by omega) pc code rfl rfl
  have eq : execInstrBr s (.JAL .x0 (returnOffset c))=s.setPC (pcAt 607) := by
    change s.setPC (s.pc+signExtend21 (returnOffset c))=_
    rw [pc,dest]
  rwa [eq] at h

def enterCost (l : Nat) := if l=2 then 6 else 0
def leaveCost (l : Nat) := if l=12 then 1 else 0
def enter (l : Fin 14) (s : MachineState) := if l.val=2 then dispatch s else s
def leave (l : Fin 14) (s : MachineState) := if l.val=12 then s.setPC (pcAt 607) else s
def block (l : Fin 14) (s : MachineState) :=
  leave l (tailPrefix (copyBody ((s.getReg .x21).toNat%8) (headPrefix (enter l s) 3)) l 2)

end TwoPermutationPrototype.GroupedOpening.AlignedFields
