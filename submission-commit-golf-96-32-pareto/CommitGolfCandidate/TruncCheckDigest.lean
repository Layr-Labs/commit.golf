import CommitGolfCandidate.TruncCheckLoop
import CommitGolfCandidate.PairPathValue
namespace CommitGolfCandidate.Trunc.Check
open CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap
set_option maxRecDepth 14000
set_option maxHeartbeats 1000000
structure GFrame (s : MachineState) (d r : Nat) : Prop where
  count : s.getReg .x29=BitVec.ofNat 64 r
  depth : s.getReg .x30=BitVec.ofNat 64 d
  slots : s.getReg .x19=0 ↔ d=24

theorem nextGuard (s : MachineState) (a : Digest) (d r : Nat) (f : GFrame s d (r+1)) : GFrame (rec_checkPathStepState s a) d r := by
  refine ⟨?_,(rec_path_step_preserves s a .x30 (by decide)).trans f.depth,?_⟩
  · rw [(rec_check_path_step_registers s a).2.2.1,f.count,BitVec.ofNat_add];exact BitVec.add_sub_cancel _ 1
  · rw [rec_path_step_preserves s a .x19 (by decide)];exact f.slots


theorem rec_check_path_loop_digest (oracle : Oracle) (state : MachineState)
    (address : Nat) (path : List (Bool × Digest)) (iLeaf : Index) (depth : Nat)
    (mode : depth=16 ∨ depth=24) (frame : GFrame state depth path.length) (limit : path.length≤depth)
    (scratch : state.getReg .x21 = 256)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 32 * path.length < 2^64)
    (data : ∀ i (hi : i < path.length), readBuffer state (address + 32*i) 32 = (path[i]'hi).2)
    (directions : ∀ i (hi : i < path.length), (state.getReg .x20).getLsbD i = (path[i]'hi).1) :
    readBuffer (Late.Check.Normal.checkEvaluation oracle (rec_checkPathLoop state path.length)).1 256 32 =
      Trunc.climb oracle.compression ((LENGTH+iLeaf.val)/2^(depth-path.length)) (readBuffer state 256 32) path := by
  induction path generalizing state address with
  | nil => simp [rec_checkPathLoop, Late.Check.Normal.check_evaluation_pure, Trunc.climb]
  | cons pair rest ih =>
    rcases pair with ⟨right, sibling⟩
    have input := rec_check_path_input state address scratch pointer aligned above (by simp only [List.length_cons] at bounded; omega)
    have headData := data 0 (by simp)
    have headDirection := directions 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at headData headDirection
    simp only [headData, rec_low_bit_zero, headDirection] at input
    let answer := if right then
      combine oracle.compression sibling (readBuffer state 256 32)
      else combine oracle.compression (readBuffer state 256 32) sibling
    let next := rec_checkPathStepState state answer
    have registers := rec_check_path_step_registers state answer
    have nextScratch : next.getReg .x21 = 256 := registers.2.2.2.trans scratch
    have nextPointer : next.getReg .x25 = BitVec.ofNat 64 (address + 32) := by
      rw [show next.getReg .x25 = state.getReg .x25 + 32 from registers.1, pointer, BitVec.ofNat_add]
      rfl
    have nextData (i : Nat) (hi : i < rest.length) :
        readBuffer next (address + 32 + 32*i) 32 = (rest[i]'hi).2 := by
      have memory : readBuffer next (address + 32 + 32*i) 32 =
          readBuffer state (address + 32 + 32*i) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro word hw
        apply rec_check_path_step_outside _ _ _ scratch
        intro j hj equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by simp only [List.length_cons] at bounded; omega : address + 32 + 32*i + 8*word < 2^64),
          Nat.mod_eq_of_lt (by omega : 256+8*j < 2^64)] at natural
        omega
      rw [memory, show address + 32 + 32*i = address + 32*(i+1) by omega]
      exact data (i+1) (by simp; omega)
    have nextDirections (i : Nat) (hi : i < rest.length) :
        (next.getReg .x20).getLsbD i = (rest[i]'hi).1 := by
      rw [show next.getReg .x20 = state.getReg .x20 >>> 1 from registers.2.1,
        BitVec.getLsbD_ushiftRight]
      rw [show 1 + i = i + 1 by omega]
      exact directions (i+1) (by simp; omega)
    have guard:=guardCorrect state depth (rest.length+1) mode (by omega) limit frame.count frame.depth frame.slots
    have sameReply : adjusted state answer=storeNode (((LENGTH+iLeaf.val)/2^(depth-(rest.length+1)))/2) answer := by
      apply Eq.trans _ (pathReplyEq depth (rest.length+1) mode (by omega) limit iLeaf answer)
      by_cases test : guardTest state
      · simp only [adjusted,pathReply,if_pos test,if_pos (guard.mp test)]
      · simp only [adjusted,pathReply,if_neg test,if_neg (fun h=>test (guard.mpr h))]
    have nextSlot : (LENGTH+iLeaf.val)/2^(depth-rest.length)=((LENGTH+iLeaf.val)/2^(depth-(rest.length+1)))/2 := by
      rw [Nat.div_div_eq_div_mul,show depth-rest.length=(depth-(rest.length+1))+1 by simp only [List.length_cons] at limit;omega,Nat.pow_succ]
    have induction := ih next (address+32) (nextGuard state answer depth rest.length frame) (by simp only [List.length_cons] at limit;omega) nextScratch nextPointer (by omega) (by omega)
      (by simp only [List.length_cons] at bounded; omega) nextData nextDirections
    rw [List.length_cons, rec_checkPathLoop, Late.Check.Normal.check_evaluation_public_bind]
    change readBuffer (Late.Check.Normal.checkEvaluation oracle (rec_checkPathLoop
      (rec_checkPathStepState state (oracle.compression (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))
      rest.length)).1 256 32 = _
    rw [input]
    cases right <;>
      change readBuffer (Late.Check.Normal.checkEvaluation oracle (rec_checkPathLoop next rest.length)).1 256 32 = _
    all_goals
      rw [induction, rec_check_path_step_digest]
      rw [sameReply,nextSlot]
      simp only [Trunc.climb,Trunc.pathInput,answer,combine,Bool.false_eq_true,ite_false,ite_true,List.length_cons] <;> split_ifs <;> rfl

end CommitGolfCandidate.Trunc.Check
