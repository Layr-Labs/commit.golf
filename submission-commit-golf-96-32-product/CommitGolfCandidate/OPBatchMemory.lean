import CommitGolfCandidate.LateOpenPathModel
import CommitGolfCandidate.OPHalfMemory

/-! A96 batch opening: byte-level write frames and straight-line halfword copies
(`LHU x6, 2j(x23)` / `SH x6, 2j(x25)`), used by the appended batch code (words 140..405). -/
namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Byte-level frame: every byte outside `[base, base+size)` keeps its value. -/
def BOut (s t : MachineState) (base size : Nat) :=
  ∀ a < MEMORY_BYTES, a<base ∨ base+size≤a → byteAt t a=byteAt s a

structure BWritten (s t : MachineState) (a : Nat) (bs : List Byte) : Prop where
  outside : BOut s t a bs.length
  data : HasBytes t a bs

theorem BWritten.empty (s : MachineState) (a : Nat) : BWritten s s a [] :=
  ⟨fun _ _ _ => rfl,fun _ hi => by simp at hi⟩

theorem BOut.weaken {s t : MachineState} {b n : Nat} (old : BOut s t b n)
    (a m : Nat) (lo : a≤b) (hi : b+n≤a+m) : BOut s t a m :=
  fun q h away => old q h (by omega)

theorem BOut.chain {s t u : MachineState} {a n : Nat} (x : BOut s t a n) (y : BOut t u a n) :
    BOut s u a n := fun q h away => (y q h away).trans (x q h away)

theorem BOut.of_mem {s t : MachineState} (e : t.mem=s.mem) (a n : Nat) : BOut s t a n := by
  intro q _ _
  simp only [byteAt,MachineState.getByte,MachineState.getMem,e]

theorem HasBytes.frame {s t : MachineState} {a b n : Nat} {x : Proof} (data : HasBytes s a x)
    (frame : BOut s t b n) (hi : a+x.length≤MEMORY_BYTES) (apart : a+x.length≤b ∨ b+n≤a) :
    HasBytes t a x := by
  intro i inside
  exact (frame (a+i) (by omega) (by omega)).trans (data i inside)

theorem HasBytes.same_mem {s t : MachineState} {a : Nat} {x : Proof} (data : HasBytes s a x)
    (e : t.mem=s.mem) : HasBytes t a x := by
  intro i hi
  have := data i hi
  simpa only [byteAt,MachineState.getByte,MachineState.getMem,e] using this

theorem BWritten.append {s t u : MachineState} {a : Nat} {xs ys : List Byte}
    (x : BWritten s t a xs) (y : BWritten t u (a+xs.length) ys)
    (bounded : a+xs.length≤MEMORY_BYTES) : BWritten s u a (xs++ys) := by
  constructor
  · intro w hw outside
    simp only [List.length_append] at outside
    exact (y.outside w hw (by omega)).trans (x.outside w hw (by omega))
  · intro i hi
    by_cases left : i<xs.length
    · rw [List.getElem_append_left left]
      exact (y.outside (a+i) (by omega) (by omega)).trans (x.data i left)
    · have right : i-xs.length<ys.length := by simp only [List.length_append] at hi;omega
      rw [List.getElem_append_right (by omega)]
      simpa only [show a+xs.length+(i-xs.length)=a+i by omega] using y.data _ right

theorem BWritten.congr_mem {s t s' t' : MachineState} {a : Nat} {xs : List Byte}
    (w : BWritten s t a xs) (b : s'.mem=s.mem) (e : t'.mem=t.mem) : BWritten s' t' a xs := by
  constructor
  · intro q hi out
    have := w.outside q hi out
    simpa only [byteAt,MachineState.getByte,MachineState.getMem,b,e] using this
  · exact w.data.same_mem e

theorem Sources.afterB {s t : MachineState} {xs : List Index} {tree : Levels} {salt : SaltTape}
    (src : Sources s xs tree salt) (size : xs.length≤LENGTH) (a n : Nat)
    (frame : BOut s t a n) (high : proofBase≤a) : Sources t xs tree salt := by
  have cap : xs.length≤16777216 := size
  have below (q : Nat) (hq : q < proofBase) : t.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q) :=
    frame q (by unfold proofBase at hq; unfold MEMORY_BYTES; omega) (Or.inl (by omega))
  constructor
  · intro r hr
    have e := OPHalf.get_mem_of_bytes t s (indexBase+8*r) (by unfold indexBase; omega)
      (fun i hi => below _ (by unfold indexBase proofBase; omega))
    exact e.trans (src.index r hr)
  · intro d hd j hj
    have e := (node_ok d j hj).2.1; unfold indexBase at e
    exact (OPHalf.read_buffer_bytes_congr t s _ _ 32
      (fun i hi => below _ (by unfold proofBase; omega))).trans (src.node d hd j hj)
  · intro i
    have e := (salt_ok i).2.1; unfold indexBase at e
    exact (OPHalf.read_buffer_bytes_congr t s _ _ 24
      (fun i hi => below _ (by unfold proofBase; omega))).trans (src.salts i)

/-! ### The low 30 bytes of a stored digest -/

theorem low_bytes (v : Digest) (j : Nat) (hj : j<30) :
    (bytes (n:=30) (low240 v))[j]'(by simp [bytes]; omega) =
      (bytes (n:=32) v)[j]'(by simp [bytes]; omega) := by
  simp only [bytes,List.getElem_ofFn,low240]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb']
  have : 8*j+k < 240 := by omega
  simp [hk, this]

theorem HasBytes.low {s : MachineState} {a : Nat} {v : Digest} (h : HasBytes s a (bytes (n:=32) v)) :
    HasBytes s a (bytes (n:=30) (low240 v)) := by
  intro j hj
  have small : j<30 := by simpa [bytes] using hj
  rw [low_bytes v j small]
  exact h j (by simp [bytes]; omega)

/-! ### Halfword copy sites of the batch code -/

inductive HSite where | salt | pathA | pathB | capFirst | capSecond | override
deriving DecidableEq

def HSite.pc : HSite → Nat
  | .salt => 149 | .pathA => 182 | .pathB => 226 | .capFirst => 271 | .capSecond => 303 | .override => 368

def HSite.count : HSite → Nat
  | .salt => 12 | .pathA => 16 | _ => 15

private def represents (n : Nat) (op : Instr) : Bool :=
  match decodeInstruction (openWord n) with
  | some (.base actual) => decide (actual=op)
  | _ => false

private theorem represented {n : Nat} {op : Instr} (h : represents n op = true) :
    decodeInstruction (openWord n) = some (.base op) := by
  unfold represents at h
  split at h
  · next actual eq => rw [eq,of_decide_eq_true h]
  · contradiction

private def siteOK (h : HSite) : Bool :=
  (List.range h.count).all fun j =>
    represents (h.pc+2*j) (.LHU .x6 .x23 (BitVec.ofNat 12 (0+2*j))) &&
    represents (h.pc+2*j+1) (.SH .x25 .x6 (BitVec.ofNat 12 (0+2*j)))

set_option maxRecDepth 8000 in
private theorem site_ok (h : HSite) : siteOK h = true ∧ h.pc+2*h.count ≤ 406 := by
  cases h <;> decide

theorem site_words (h : HSite) (j : Nat) (hj : j<h.count) :
    decodeInstruction (openWord (h.pc+2*j)) = some (.base (.LHU .x6 .x23 (BitVec.ofNat 12 (0+2*j)))) ∧
    decodeInstruction (openWord (h.pc+2*j+1)) = some (.base (.SH .x25 .x6 (BitVec.ofNat 12 (0+2*j)))) := by
  have all := List.all_eq_true.mp (site_ok h).1 j (List.mem_range.mpr hj)
  simp only [Bool.and_eq_true] at all
  exact ⟨represented all.1,represented all.2⟩

def hcopy (h : HSite) (s : MachineState) := OPHalf.halfRun .x23 .x25 s 0 0 h.count

structure HCopied (h : HSite) (s : MachineState) (D : Nat) (bs : List Byte) : Prop where
  run : Runs s (hcopy h s) (2*h.count) (2*h.count)
  pc : (hcopy h s).pc = pcAt (h.pc+2*h.count)
  regs : ∀ r, r ≠ .x6 → (hcopy h s).getReg r = s.getReg r
  data : BWritten s (hcopy h s) D bs

theorem pc_of (n m t k : Nat) (e : 4*k=m) (f : t=n+k) : pcAt n + BitVec.ofNat 64 m = pcAt t := by
  unfold pcAt; rw [←BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); omega

theorem hcopy_run (h : HSite) (s : MachineState) (pc : s.pc=pcAt h.pc) (S D : Nat)
    (sp : s.getReg .x23=W S) (dp : s.getReg .x25=W D) (bs : List Byte) (len : bs.length=2*h.count)
    (src : HasBytes s S bs) (se : S%2=0) (de : D%2=0)
    (sb : S+2*h.count≤MEMORY_BYTES) (db : D+2*h.count≤MEMORY_BYTES)
    (sep : S+2*h.count≤D ∨ D+2*h.count≤S) : HCopied h s D bs := by
  have cnt : h.count ≤ 16 := by cases h <;> decide
  have fits := (site_ok h).2
  have mem : MEMORY_BYTES < 2^64 := by unfold MEMORY_BYTES; decide
  refine ⟨?_,?_,?_,?_⟩
  · intro fuel
    have e := OPHalf.half_run_execute image .x23 .x25 s 0 0 S D h.count (by decide) (by decide) sp dp
      (by omega) (by omega) (by omega) (by omega) sb db
      (fun j hj t tp => fetched _ (by omega) _ (site_words h j hj).1 t
        (tp.trans (by rw [pc]; exact pc_of _ _ _ (2*j) (by omega) rfl)))
      (fun j hj t tp => fetched _ (by omega) _ (site_words h j hj).2 t
        (tp.trans (by rw [pc]; exact pc_of _ _ _ (2*j+1) (by omega) (by omega))))
      fuel true
    rw [Nat.add_comm fuel]; exact e
  · rw [hcopy,OPHalf.half_run_pc,pc]; exact pc_of _ _ _ (2*h.count) (by omega) rfl
  · intro r hr; exact OPHalf.half_run_register _ _ _ _ _ _ _ hr
  · constructor
    · intro q hq away
      rw [len] at away
      exact OPHalf.half_run_byte_outside .x23 .x25 s 0 0 D h.count q (by decide) dp (by omega)
        (by omega) (by omega) (by omega) (by omega)
    · intro j hj
      have jb : j < 2*h.count := len ▸ hj
      have e := OPHalf.half_run_byte .x23 .x25 s 0 0 S D h.count (D+j) (by decide) (by decide) sp dp
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      rw [if_pos (by omega)] at e
      change (hcopy h s).getByte (BitVec.ofNat 64 (D+j)) = _
      rw [hcopy,e,show S+0+(D+j-(D+0))=S+j by omega]
      exact src j hj

end CommitGolfCandidate.Late.Open
