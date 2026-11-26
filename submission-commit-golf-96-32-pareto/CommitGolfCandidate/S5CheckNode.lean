import CommitGolfCandidate.S5ChainCheckEnd
import CommitGolfCandidate.S5HonestTree
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Chained
open Late (Block Digest)
open Open (W)
def levelCalls (level : Nat) :=calls (S5.height level)
def parentFuel (level : Nat) :=if 1<levelCalls level then 9*levelCalls level+30 else 19
structure NodeResult (o : Oracle) (s t : MachineState) (level dst back steps : Nat) (row : Block) : Prop where
  run : Flow o s t steps (levelCalls level)
  pc : t.pc=pcAt back
  value : readBuffer t dst 32=S5.Auth.compressRow o.compression (level+1) row
  keep : ParentPreserves s t
  frame : ChainOutside s t dst

private theorem upper_node (H : Compression) (n : Nat) (a b c : Digest) (positive : n≠0) :
    nodeHash H n a b c=parentDigest H (S5.height n) a b := by cases n <;> first | contradiction | rfl

private theorem plain_value (H : Compression) (n : Nat) (d : Height) (a b c : Digest) (hd : d=S5.height n)
    (small : n<24) (one : calls d=1) (plain : ¬(8≤d.val ∧ d.val<16)) :
    storeReply d (H (S5.Auth.row n a b c))=S5.Auth.compressRow H (n+1) (S5.Auth.row n a b c) := by
  by_cases bottom : n=0
  · subst n;subst d
    exact full_projection (S5.height 0) _ (by decide)
  · have code : S5.Auth.row n a b c=Late.parentBlock a b:=by unfold S5.Auth.row;rw [if_neg bottom];rfl
    rw [S5.Auth.row_parent,upper_node H n a b c bottom,←hd]
    unfold parentDigest queries;rw [one];change storeReply d (H (S5.Auth.row n a b c))=storeReply d (H (pack (.inl (workClass d,b++a))))
    rw [code];apply congrArg (fun z=>storeReply d (H z))
    apply Eq.trans _ (parentBlock_plain d a b plain)
    change (0#256 ++ b) ++ a=(0#256 ++ (b++a))
    exact BitVec.append_assoc

theorem parent_node (o : Oracle) (s : MachineState) (level src dst back : Nat) (a b c : Digest) (small : level<24)
    (pc : s.pc=pcAt 173) (count : s.getReg .x30=W (levelCalls level)) (width : s.getReg .x31=W (S5.bits (level+1)))
    (label : s.getReg .x29=W (level+1)) (sp : s.getReg .x10=W src) (dp : s.getReg .x12=W dst) (sc : s.getReg .x26=W chainBuf)
    (ret : s.getReg .x1=pcAt back) (limit : back<2336) (ss : src+96≤MEMORY_BYTES) (sa : src%8=0) (ds : dst+32≤MEMORY_BYTES) (da : dst%8=0)
    (raw : readBuffer s src 96=S5.Auth.row level a b c)
    (work : 8≤level ∧ level<16 → src=rowBuf) :
    ∃ t steps,steps≤parentFuel level ∧ NodeResult o s t level dst back steps (S5.Auth.row level a b c) := by
  let d:=S5.height level
  have idx : d.val=level:=Nat.mod_eq_of_lt small
  by_cases cut : 8≤d.val ∧ d.val<16
  · obtain ⟨lower,upper⟩:=(by decide +kernel : ∀ k : Height,8≤k.val ∧ k.val<16 → 1<calls k ∧ calls k≤16) d cut
    have fixed:=work (idx ▸ cut)
    subst src
    have nonzero : level≠0:=by omega
    have lo : readBuffer s rowBuf 32=a:=by
      have sl:=read_buffer_slice s rowBuf 96 0 32 (by decide)
      rw [raw] at sl
      apply (show readBuffer s rowBuf 32=(S5.Auth.row level a b c).extractLsb' 0 256 from sl.symm).trans
      exact BitVec.extractLsb'_append_eq_right
    have hi : readBuffer s (rowBuf+32) 32=b:=by
      have sl:=read_buffer_slice s rowBuf 96 32 32 (by decide)
      rw [raw] at sl
      apply sl.symm.trans
      exact (BitVec.extractLsb'_append_eq_of_le (by decide : 256≤256)).trans BitVec.extractLsb'_append_eq_right
    obtain ⟨t,n,sz,node⟩:=chained_parent o s d dst back cut pc count width (idx ▸ label) sp dp sc ret limit da ds
    refine ⟨t,n,by change n ≤ (if 1<calls d then 9*calls d+30 else 19);rw [if_pos lower];exact sz,⟨node.run,node.pc,?_,node.keep,node.frame⟩⟩
    have value:=node.value;rw [lo,hi] at value
    rw [S5.Auth.row_parent,upper_node _ _ _ _ _ nonzero];exact value
  · have one : calls d=1:=(by decide +kernel : ∀ k : Height,¬(8≤k.val ∧ k.val<16) → calls k=1) d cut
    obtain ⟨t,n,sz,run,ep,keep,mem⟩:=plain_parent o s d src dst back pc (count.trans (congrArg W one)) width sp dp ret limit ss sa ds da
    have plain:=plain_value o.compression level d a b c rfl small one cut
    have act : levelCalls level=1:=one
    refine ⟨t,n,by simp only [parentFuel,act,show ¬1<1 by decide,ite_false];exact sz,⟨act.symm ▸ run,ep,?_,keep,?_⟩⟩
    · apply (read_buffer_memory_congr t _ mem _ _).trans
      apply (store_read _ _ _).trans;rw [raw];exact plain
    · apply ChainOutside.output;intro q h al sep;exact (congrFun mem _).trans (reply_outside _ _ _ ds da q h al sep)
end CommitGolfCandidate.S5Machine.Check
