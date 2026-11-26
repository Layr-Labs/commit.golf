import CommitGolfCandidate.TwoPermutationPackedChildCopy
import CommitGolfCandidate.TwoPermutationPackedDecode
import CommitGolfCandidate.TwoPermutationPackedCapBytes

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000

def slotWord (high : Bool) : Nat := if high then 1572 else 1568

structure OperandFacts (s t : MachineState) (steps next dest : Nat) (value : BitVec 256) : Prop where
  execute : GroupHop s t steps
  pc : t.pc=BitVec.ofNat 64 (4096+4*next)
  register : ∀ r, r≠.x31 → t.getReg r=s.getReg r
  digest : readBuffer t (8*dest) 32=value
  frame : ∀ w<2^61, (w<dest ∨ dest+4≤w) → memoryView t w=memoryView s w

def childSite (leaf even : Bool) : Nat :=
  if leaf then (if even then 193 else 183) else (if even then 108 else 99)

def siblingSite (leaf even : Bool) : FieldSite :=
  if leaf then (if even then .leftLeaf else .rightLeaf) else (if even then .leftInternal else .rightInternal)

def lowSite (leaf even : Bool) : LowSite :=
  if leaf then (if even then .leftLeaf else .rightLeaf) else (if even then .left else .right)

/-- Every sibling copies fifteen halfwords and then stores its two top bytes. -/
def siblingCost (_leaf : Bool) : Nat := 31

def siblingState (s : MachineState) (leaf even : Bool) : MachineState :=
  decode (lowSite leaf even) s (8*slotWord even)

/-- The leaf-level top bytes come from the trailer byte in `t3`; internal ones are zero. -/
def wire (s : MachineState) (proof : Nat) (_leaf : Bool) : BitVec 256 :=
  0#16 ++ readBuffer s proof 30

/-- Leaf digests keep their low 240 bits (`projectLeaf true`). -/
def truncLeaf (digest : BitVec 256) : BitVec 256 := BitVec.ofNat 256 (digest.toNat % 2^240)

/-- The child digest a level hashes: the leaf level first clears bytes 30 and 31. -/
def own (s : MachineState) (leaf : Bool) : BitVec 256 :=
  if leaf then truncLeaf (readBuffer s 12288 32) else readBuffer s 12288 32

/-- `sh zero,30(s7)` at the leaf level; nothing at internal levels. -/
def truncCost (leaf : Bool) : Nat := if leaf then 1 else 0

def truncState (s : MachineState) (leaf : Bool) : MachineState :=
  if leaf then execInstrBr s (.SH .x23 .x0 30) else s

theorem child_operand (s : MachineState) (leaf even : Bool)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*childSite leaf even))
    (source : s.getReg .x23=12288) (dest : s.getReg .x24=12544) :
    OperandFacts s (childCopied s (childSite leaf even)) 8 (childSite leaf even+8)
      (slotWord (!even)) (readBuffer s 12288 32) := by
  let start := childSite leaf even
  let target := slotWord (!even)
  let prev := if childOffset start=32 then 86 else 95
  have site : ChildSite start := by unfold ChildSite; cases leaf <;> cases even <;> decide
  have old : TwoPermutationPrototype.Checker.CopyBlock prev := by unfold TwoPermutationPrototype.Checker.CopyBlock; cases leaf <;> cases even <;> decide
  have fromOld : s.getReg (TwoPermutationPrototype.Checker.copySource prev)=wordAddress 1536 := by
    cases leaf <;> cases even <;> exact source
  have toOld : s.getReg (TwoPermutationPrototype.Checker.copyTarget prev)+
      BitVec.ofNat 64 (TwoPermutationPrototype.Checker.copyOffset prev)=wordAddress target := by
    cases leaf <;> cases even <;> change s.getReg .x24+_=_
    all_goals rw [dest]; rfl
  have bound : target+4≤2^61 := by cases even <;> decide
  have apart : 1536+4≤target := by cases even <;> decide
  have readAccess (i : Fin 4) : accessValid (s.getReg .x23+BitVec.ofNat 64 (8*i.val)) 8=true := by
    rw [source]; fin_cases i <;> decide
  have writeAccess (i : Fin 4) : accessValid (s.getReg .x24+BitVec.ofNat 64 (childOffset start+8*i.val)) 8=true := by
    rw [dest]; cases leaf <;> cases even <;> fin_cases i <;> decide
  refine ⟨execute_child_copy s start site pc readAccess writeAccess,?_,childCopied_register _ _,?_,?_⟩
  · rw [childCopied_pc,pc]
    cases leaf <;> cases even <;> rfl
  · rw [child_as_old _ _ site]
    exact TwoPermutationPrototype.Checker.copied_digest s prev 1536 target old fromOld toOld
      (by decide) bound (Or.inl apart)
  · intro w hw outside
    rw [child_as_old _ _ site]
    exact TwoPermutationPrototype.Checker.copied_word_outside s prev 1536 target w old fromOld toOld
      (by decide) bound hw (Or.inl apart) outside

private theorem word_clear (dest w : Nat) (hw : w<2^61) (bd : dest+4≤2^61)
    (outside : w<dest ∨ dest+4≤w) (i : Nat) (hi : i<8) (j : Nat) (hj : j<32) :
    BitVec.ofNat 64 (8*w+i) ≠ BitVec.ofNat 64 (8*dest+j) := by
  intro eq
  have n := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*w+i<2^64),
    Nat.mod_eq_of_lt (by omega : 8*dest+j<2^64)] at n
  omega

theorem sibling_operand (s : MachineState) (leaf even : Bool) (proof : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(siblingSite leaf even).start)) (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (dst : s.getReg .x24=12544) (above : 32768≤proof) (aligned : proof%2=0)
    (room : proof+30≤MEMORY_BYTES) :
    OperandFacts s (siblingState s leaf even) (siblingCost leaf)
      ((siblingSite leaf even).start+siblingCost leaf) (slotWord even) (wire s proof leaf) := by
  let site := siblingSite leaf even
  let target := 8*slotWord even
  have bounded : target+32≤MEMORY_BYTES := by cases even <;> decide
  have small : target+32≤32768 := by cases even <;> decide
  have targetWord : slotWord even+4≤2^61 := by cases even <;> decide
  have low : (lowSite leaf even).field=siblingSite leaf even := by cases leaf <;> cases even <;> rfl
  have count : 2*(fieldCode (lowSite leaf even).field).count=30 := by cases leaf <;> cases even <;> rfl
  have r : CopyReady (fieldCode (lowSite leaf even).field) s proof target 0 := by
    refine ⟨by rw [low]; exact pc,src,?_,?_,?_,aligned,by cases even <;> decide⟩
    · cases leaf <;> cases even <;> change s.getReg .x24+_=_ <;> rw [dst] <;> rfl
    · rw [count]; omega
    · rw [count]; omega
  have top : (lowSite leaf even).top s = 0#16 := by
    cases leaf <;> cases even <;> rfl
  refine ⟨decode_execute _ _ _ _ r bounded, ?_,decode_register _ _ _, ?_, ?_⟩
  · change (decode (lowSite leaf even) s target).pc=BitVec.ofNat 64 (4096+4*((siblingSite leaf even).start+31))
    simpa only [low] using decode_pc _ _ _ _ r
  · rw [wire,← top]
    exact decode_read _ _ _ _ r bounded (by omega) (by cases even <;> decide)
  · intro w hw outside
    apply word_eq_of_byte_frame
    intro i hi
    apply decode_byte_frame _ _ _ _ r bounded (by omega)
    exact word_clear (slotWord even) w hw targetWord outside i hi

theorem trunc_leaf_byte (x : BitVec 256) (j : Nat) (inside : j < 32) :
    (truncLeaf x).extractLsb' (8*j) 8 = if j < 30 then x.extractLsb' (8*j) 8 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [truncLeaf, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow]
  by_cases low : j < 30
  · simp only [low, ite_true, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
      show 8*j+k < 240 by omega, show 8*j+k < 256 by omega, BitVec.testBit_toNat]
  · simp only [low, ite_false, show ¬ 8*j+k < 240 by omega, decide_false, Bool.false_and, Bool.and_false]
    simp

private theorem trunc_byte_read (s : MachineState) (source : s.getReg .x23=12288) (q : Word) :
    (truncState s true).getByte q = (s.setHalfword (BitVec.ofNat 64 (12288+30)) 0).getByte q := by
  have addr : s.getReg .x23+signExtend12 30=BitVec.ofNat 64 (12288+30) := by rw [source]; rfl
  change (execInstrBr s (.SH .x23 .x0 30)).getByte q=_
  simp only [execInstrBr,addr]
  rfl

private theorem trunc_low_byte (s : MachineState) (source : s.getReg .x23=12288) (q : Word)
    (away₀ : q≠BitVec.ofNat 64 (12288+30)) (away₁ : q≠BitVec.ofNat 64 (12288+31)) :
    (truncState s true).getByte q = s.getByte q := by
  rw [trunc_byte_read s source]
  exact mask_outside s 12288 0 q (by decide) away₀ away₁

theorem trunc_operand (s : MachineState) (leaf : Bool) (here : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*here))
    (code : leaf=true → (packedImage.code[here]?).bind decodeInstruction=some (.base (.SH .x23 .x0 30)))
    (bounded : here < 367) (source : s.getReg .x23=12288) :
    OperandFacts s (truncState s leaf) (truncCost leaf) (here+truncCost leaf) 1536 (own s leaf) := by
  cases leaf with
  | false =>
    refine ⟨?_,pc,fun _ _ => rfl,rfl,fun _ _ _ => rfl⟩
    intro fuel
    simp [truncCost,truncState,Execution.charge]
  | true =>
    have addr : s.getReg .x23+signExtend12 30=BitVec.ofNat 64 12318 := by rw [source]; rfl
    have apart (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (ne : a ≠ b) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
      intro eq
      have n := congrArg BitVec.toNat eq
      rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at n
      exact ne n
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro fuel
      have fetched := fetch_at s here _ bounded pc (code rfl)
      have step : ordinaryStep s (.base (.SH .x23 .x0 30)) = some (truncState s true) := by
        have valid : accessValid (s.getReg .x23+signExtend12 30) 2=true := by rw [addr]; decide
        simp only [ordinaryStep,memoryArgumentsValid,memAccess,valid,ite_true]
        rfl
      rw [show truncCost true+fuel=fuel+1 by simp [truncCost]; omega,
        execute_ordinary_step _ _ _ _ _ _ fetched step]
      rfl
    · change (execInstrBr s (.SH .x23 .x0 30)).pc=_
      simp only [execInstrBr,MachineState.setPC]
      rw [pc,show truncCost true=1 from rfl]
      change BitVec.ofNat 64 (4096+4*here)+BitVec.ofNat 64 4=_
      rw [←BitVec.ofNat_add]
      congr 1
    · intro r _
      rfl
    · change readBuffer (truncState s true) 12288 32=truncLeaf (readBuffer s 12288 32)
      have value := read_serialized_slice (truncState s true) (truncLeaf (readBuffer s 12288 32)) 12288 0 32 (by
        intro j inside
        rw [Nat.zero_add,trunc_leaf_byte _ j inside]
        by_cases top : j < 30
        · rw [trunc_low_byte s source _ (apart _ _ (by omega) (by omega) (by omega))
            (apart _ _ (by omega) (by omega) (by omega)),ite_eq_left top,read_buffer_byte _ _ _ _ inside]
        · rw [trunc_byte_read s source,masked_upper_byte s 12288 j 0 (by decide) (by omega) inside,
            ite_eq_right top]
          simp)
      simpa only [Nat.mul_zero,BitVec.extractLsb'_eq_self] using value
    · intro w hw outside
      apply word_eq_of_byte_frame
      intro i hi
      exact trunc_low_byte s source _ (apart _ _ (by omega) (by omega) (by omega))
        (apart _ _ (by omega) (by omega) (by omega))

end TwoPermutationPrototype.Packed.Checker
