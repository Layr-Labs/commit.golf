import CommitGolfCandidate.ReconstructedCommitParentsLine
import CommitGolfCandidate.CopyRefinement

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding
open Image (Atom)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer

def aux (d : Nat) (s : MachineState) :=
  (width d = 240 → s.getReg .x17 = BitVec.ofNat 64 d) ∧
  (modulus d ≠ 0 → s.getReg .x21 = BitVec.ofNat 64 (modulus d)) ∧
  (width d < 240 → modulus d = 0 → s.getReg .x21 = BitVec.ofNat 64 (narrowMarker d))

private theorem source24 (a : Nat) : BitVec.ofNat 64 a + signExtend12 24#12 = BitVec.ofNat 64 (a+24) :=
  (BitVec.ofNat_add ..).symm
private theorem source28 (a : Nat) : BitVec.ofNat 64 a + signExtend12 28#12 = BitVec.ofNat 64 (a+28) :=
  (BitVec.ofNat_add ..).symm
private theorem source30 (a : Nat) : BitVec.ofNat 64 a + signExtend12 30#12 = BitVec.ofNat 64 (a+30) :=
  (BitVec.ofNat_add ..).symm

private theorem source24o (a : Nat) : BitVec.ofNat 64 a + signExtend12 24 = BitVec.ofNat 64 (a+24) := source24 a
private theorem source28o (a : Nat) : BitVec.ofNat 64 a + signExtend12 28 = BitVec.ofNat 64 (a+28) := source28 a
private theorem source30o (a : Nat) : BitVec.ofNat 64 a + signExtend12 30 = BitVec.ofNat 64 (a+30) := source30 a

private theorem access (a sz : Nat) (align : a%sz=0) (room : a+sz≤MEMORY_BYTES) (small : a<2^64) :
    accessValid (BitVec.ofNat 64 a) sz = true := by
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨room,align⟩

private theorem save_low (d : Nat) (x : Binding.Digest) : (written d (project d x)).1 = x.1 := by
  unfold written;split <;> rfl

theorem cell_congr {s t : MachineState} (mem : s.mem=t.mem) (a : Nat) : cell s a = cell t a :=
  congrArg unpack (read_buffer_memory_congr s t mem a 32)

private theorem installed {s t : MachineState} {dst : Nat} (align : dst%8=0) (size : dst+32 ≤ 2^64)
    (win : Binding.Digest) (low : win.1 = (cell s dst).1) (same : t.mem = (putTop s dst win.2).mem) :
    cell t dst = win ∧ Frame dst s t := by
  constructor
  · rw [cell_congr same,putTop_cell s dst win.2 align size,←low]
  · intro a n h sep
    exact (read_buffer_memory_congr _ _ same a n).trans (putTop_frame s dst win.2 align size a n h sep)

/-- Under the single precondition on the output pointer, all ordinary memory
operations in the emitted projection suffix pass the interpreter's access checks. -/
theorem save_ready (d : Fin 24) (s : MachineState) (dst : Nat) (room : dst+32 ≤ MEMORY_BYTES)
    (align : dst%8=0) (reg : s.getReg .x12 = BitVec.ofNat 64 dst) :
    ready s (Image.save d) := by
  have limit : dst+32 ≤ 2^64 := by unfold MEMORY_BYTES at room;omega
  have a24 := access (dst+24) 8 (by omega) (by omega) (by omega)
  have a28 := access (dst+28) 4 (by omega) (by omega) (by omega)
  have a28h := access (dst+28) 2 (by omega) (by omega) (by omega)
  have a30 := access (dst+30) 2 (by omega) (by omega) (by omega)
  unfold Image.save
  split_ifs <;> simp [ready,Image.Atom.op,memoryArgumentsValid,memAccess,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne,reg,source24,source28,source30,
    a24,a28,a28h,a30]

private theorem save_regs (s : MachineState) {ops : List Atom} (h : ∀ a ∈ ops, a = .saveWide ∨ a = .loadTop ∨ a = .reduceTop ∨
        a = .storeTop ∨ a = .loadNarrow ∨ a = .fillNarrow ∨ a = .saveNarrow) :
      ∀ r, r ≠ .x6 → (runPlain s ops).getReg r = s.getReg r := by
    intro r ne
    induction ops generalizing s with
    | nil => rfl
    | cons a ops ih =>
      rw [runPlain,ih (execInstrBr s a.op) (fun x hx => h x (by simp [hx]))]
      rcases h a (by simp) with h | h | h | h | h | h | h <;> subst a <;> cases r <;>
        simp_all [Image.Atom.op,execInstrBr,MachineState.getReg,MachineState.setReg] <;> rfl

/-- All four projection paths affect just the last word of the output and scratch t1. -/
theorem save_effect (d : Fin 24) (s : MachineState) (dst : Nat) (room : dst+32 ≤ MEMORY_BYTES)
    (align : dst%8=0) (reg : s.getReg .x12 = BitVec.ofNat 64 dst) (masks : aux d s) :
    let t := runPlain s (Image.save d)
    cell t dst = written d (project d (cell s dst)) ∧ Frame dst s t ∧
      ∀ r, r ≠ .x6 → t.getReg r = s.getReg r := by
  have limit : dst+32 ≤ 2^64 := by unfold MEMORY_BYTES at room;omega
  have hi : (cell s dst).2 = atWord s (dst+24) := congrArg Prod.snd (cell_words s dst align)
  let win := written d (project d (cell s dst))
  have low : win.1 = (cell s dst).1 := save_low _ _
  have keep : ∀ r, r ≠ .x6 → (runPlain s (Image.save d)).getReg r = s.getReg r := by
    apply save_regs
    unfold Image.save
    split_ifs <;> simp_all
  have effect : cell (runPlain s (Image.save d)) dst = win ∧ Frame dst s (runPlain s (Image.save d)) := by
    by_cases wide : width d = 240
    · apply installed align limit win low
      simp only [Image.save,wide,ite_true,runPlain,Image.Atom.op,execInstrBr,reg,source30o,masks.1 wide]
      rw [half_store s dst _ align]
      have val := wide_store d wide (cell s dst)
      rw [hi] at val
      rw [val]
      rfl
    by_cases modded : modulus d ≠ 0
    · apply installed align limit win low
      have key := masks.2.1 modded
      have spine : Image.save d = [.loadTop,.reduceTop,.storeTop] := by unfold Image.save;rw [ite_eq_right wide,ite_eq_left modded]
      simp only [spine,runPlain,Image.Atom.op,execInstrBr,
        MachineState.getReg_setPC,MachineState.getReg_setReg_eq (show Reg.x6≠Reg.x0 by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x6≠Reg.x12 by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x6≠Reg.x21 by decide),reg,key,source24o]
      have val := residue_store d modded (cell s dst)
      rw [hi] at val
      have nz : ∀ i : Fin 24, modulus i ≠ 0 → (BitVec.ofNat 64 (modulus i) == 0#64) = false := by decide
      simp only [rv64_remu,nz d modded,Bool.false_eq_true,ite_false]
      change (s.setMem _ (atWord s (dst+24) % BitVec.ofNat 64 (modulus d))).mem = _
      rw [val];rfl
    have m : modulus d = 0 := not_not.mp modded
    by_cases narrow : width d < 240
    · apply installed align limit win low
      have key := masks.2.2 narrow m
      simp only [Image.save,wide,ite_false,modded,narrow,ite_true,runPlain,Image.Atom.op,execInstrBr,
        MachineState.getReg_setPC,MachineState.getReg_setReg_eq (show Reg.x6≠Reg.x0 by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x6≠Reg.x12 by decide),
        MachineState.getReg_setReg_ne _ _ _ _ (show Reg.x6≠Reg.x21 by decide),reg,key,source28o]
      have v := narrow_store d narrow m (cell s dst)
      rw [hi] at v
      change (s.setWord32 _ (((s.getHalfword _).zeroExtend 64 ||| BitVec.ofNat 64 (narrowMarker d)).truncate 32)).mem = _
      rw [top_half_load s dst align,word_store s dst _ align,v]
    · have isRoot : ∀ i : Fin 24, width i ≠ 240 → modulus i = 0 → ¬ width i < 240 → i.val=0 := by decide
      have h := isRoot d wide m narrow
      simp only [Image.save,wide,ite_false,modded,narrow,runPlain]
      exact ⟨by dsimp [win];rw [h,root_store],fun _ _ _ _ => rfl⟩

  exact ⟨effect.1,effect.2,keep⟩

end CommitGolfCandidate.Reconstruction.CommitParents
