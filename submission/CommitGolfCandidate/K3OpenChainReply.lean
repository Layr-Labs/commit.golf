import CommitGolfCandidate.K3OpenChainPost

/-! Opener chain block (rows 777..795 and the link block 896..929), the reply: `chain_reply`. Owner: C3 (draft by S9-L2). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC pc_of_set mem_of_set
  mem_of_reg
attribute [local simp] chain_zero_reg

/-! ### The reply -/

/-- K1 generator input words of any group: word 0 is its counter, words 1..3 the key, the rest zero. -/
private theorem input_word_any (g : Fin Permutation.CounterSalt.groups) (key : BitVec 192) (j : Fin 25) :
    replyWords (Permutation.CounterSalt.input g key) j =
      (if j.val=0 then Permutation.CounterSalt.ctr g else keyBlock key j.val) := by
  unfold Permutation.CounterSalt.input replyWords
  have h := j.isLt
  by_cases zero : j.val=0
  · simp only [zero,ite_true,Nat.mul_zero]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0+64≤256),
      BitVec.extractLsb'_append_eq_right]
  · rw [if_neg zero]
    by_cases low : j.val<4
    · rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64*j.val+64≤256),
          BitVec.extractLsb'_append_eq_of_le (by omega : 64≤64*j.val)]
      unfold keyBlock;congr 1 <;> omega
    · rw [BitVec.extractLsb'_append_eq_of_le (by omega : 256≤64*j.val)]
      unfold keyBlock
      apply BitVec.eq_of_getLsbD_eq;intro k hk
      simp [hk,show 192≤64*(j.val-1)+k by omega]

private theorem keyed_input (h : MachineState) (i : Index) (ph : Nat) (e : ChainEntry h i ph) (k : BitVec 192)
    (key : KeyWords h k) :
    keyedQuery h=Permutation.CounterSalt.input (K6Chain.restart (coord i).1) k := by
  rw [keyedQuery,← reply_pack (Permutation.CounterSalt.input (K6Chain.restart (coord i).1) k)]
  apply congrArg packBuffer;funext j
  have jl := j.isLt
  change memoryView (chainBefore h) (128+j.val)=_
  rw [before_view h i ph e _ (by omega),input_word_any]
  by_cases zero : j.val=0
  · simp [writeWord,zero]
  · simp only [writeWord,show 128+j.val≠128 by omega,zero,if_false]
    exact key j.val (by omega) jl

private theorem window_query (s : MachineState) (R : BitVec 1600)
    (hw : ∀ m : Fin 25, memoryView s (192+m.val)=replyWords R m) : linkQuery s=R := by
  rw [linkQuery,← reply_pack R]
  apply congrArg packBuffer;funext m
  exact hw m

private theorem link_window (o : Oracle) (c : Nat) : ∀ (s : MachineState) (R : BitVec 1600),
    (∀ m : Fin 25, memoryView s (192+m.val)=replyWords R m) →
    ∀ m : Fin 25, memoryView (linkState o c s) (192+m.val)=replyWords ((⇑o.permutation)^[c] R) m := by
  induction c with
  | zero =>
    intro s R hw m
    rw [linkState_zero]
    exact hw m
  | succ c ih =>
    intro s R hw m
    have q : linkQuery s = R := window_query s R hw
    have hY : ∀ m' : Fin 25, memoryView (linkStep o s) (192+m'.val) = replyWords (o.permutation R) m' := by
      intro m'
      show memoryView (writeBits s (wordAddress 192) (o.permutation (linkQuery s))) (192+m'.val) = _
      exact (reply_inside s _ m').trans (congrArg (fun x : BitVec 1600 => replyWords (o.permutation x) m') q)
    rw [linkState_succ,
      show (⇑o.permutation)^[c+1] R = (⇑o.permutation)^[c] (o.permutation R) from Function.iterate_succ_apply _ _ _]
    exact ih _ _ hY m

theorem chain_reply (o : Oracle) (k : BitVec 192) (h : MachineState) (i : Index) (ph : Nat) (e : ChainEntry h i ph)
    (key : KeyWords h k) (j : Fin 25) :
    memoryView (chainState o h i ph) (192+j.val)=replyWords (chainReply o k i) j := by
  let R:=o.permutation (Permutation.CounterSalt.input (K6Chain.restart (coord i).1) k)
  let a:=writeBits (chainBefore h) (wordAddress 192) (o.permutation (keyedQuery h))
  have aw (m : Fin 25) : memoryView a (192+m.val)=replyWords R m := by
    show memoryView (writeBits _ _ _) _=_
    rw [reply_inside,keyed_input h i ph e k key]
  have final : chainReply o k i=(⇑o.permutation)^[chainLinks i] R := by
    have oc := K6Chain.opener_chain o.permutation k (coord i).1
    rw [K6Chain.restart_links i] at oc
    exact oc
  rw [final]
  unfold chainState
  rw [chain_view_of_mem (exit_rows_mem _)]
  apply link_window o (chainLinks i) _ R _ j
  intro m
  rw [chain_view_of_mem (enter_rows_mem _ ph)]
  exact aw m

end TwoPermutationPrototype.GroupedOpening
