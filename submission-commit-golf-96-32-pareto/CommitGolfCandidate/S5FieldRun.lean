import CommitGolfCandidate.S5WriterChunk
import CommitGolfCandidate.S5Operations
import CommitGolfCandidate.S5OpenMemory
namespace CommitGolfCandidate.S5Machine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)

def parts (n : Nat) := List.replicate (n/64) 64 ++ if n%64=0 then [] else [n%64]
def Proper : List Nat→Prop
  | []=>True
  | w::ws=>0<w ∧ w≤64 ∧ (ws≠[]→w=64) ∧ Proper ws

theorem parts_valid (n : Nat) : Proper (parts n) ∧ (parts n).sum=n := by
  have prepend (xs : List Nat) (good : Proper xs) (d : Nat) : Proper (List.replicate d 64++xs) := by
    induction d with
    | zero=>exact good
    | succ d ih=>rw [List.replicate_succ,List.cons_append];exact ⟨by decide,by decide,fun _=>rfl,ih⟩
  constructor
  · apply prepend;split
    · trivial
    · exact ⟨by omega,by omega,fun h=>False.elim (h rfl),True.intro⟩
  · simp only [parts,List.sum_append,List.sum_replicate,smul_eq_mul];split <;> simp <;> omega

def stream : List Nat→Nat→PathCode
  | [],_=>[]
  | w::ws,k=>chunkCode (w<64) (k+w)++stream ws ((k+w)%64)

private theorem chunk_length (n k : Nat) :
    (chunkCode (n<64) (k+n)).length = (push ⟨k,0⟩ n).cycles := by
  unfold chunkCode push
  by_cases small : k+n<64 <;> simp [small,List.length_append,Nat.add_assoc]

theorem stream_meter (ws : List Nat) (k c : Nat) :
    (ws.foldl push ⟨k,c⟩).cycles=c+(stream ws k).length := by
  induction ws generalizing k c with
  | nil=>simp [stream]
  | cons w ws ih=>
    change (ws.foldl push ⟨(k+w)%64,c+_+_⟩).cycles=_
    rw [ih];simp only [stream,List.length_append,chunk_length,push,Nat.zero_add,Nat.add_assoc]

private theorem keep_threshold (b : Bool) (used : Nat) (s : MachineState) :
    (pathEnd s (chunkCode b used)).getReg .x27=s.getReg .x27 := by
  apply path_keeps_reg
  simp only [chunkCode,List.all_append]
  have f : ∀ v : Bool,(fetchWord v).all (fun z=>keepsReg .x27 z.2) := by decide
  have m : mix.all (fun z=>keepsReg .x27 z.2) := by decide
  have g : ∀ v : Bool,(spill v).all (fun z=>keepsReg .x27 z.2) := by decide
  rw [f,m];split <;> first | rfl | simp [g]

theorem stream_run (s : MachineState) (ws : List Nat) (k a d : Nat) (proper : Proper ws) (small : ws.sum≤256) (hk : k<64)
    (pc : s.pc=pcAt 21) (remaining : s.getReg .x11=W ws.sum) (bits : s.getReg .x24=W k) (threshold : s.getReg .x27=64)
    (src : s.getReg .x10=W a) (dst : s.getReg .x19=W d) (aa : a%8=0) (da : d%8=0)
    (spaceA : a+8*ws.length≤MEMORY_BYTES) (spaceD : d+8*ws.length≤MEMORY_BYTES) :
    let code:=stream ws k
    let t:=pathEnd s code
    Open.Runs s t code.length code.length ∧ t.pc=pcAt 21 ∧ t.getReg .x11=0 ∧
      t.getReg .x24=W ((k+ws.sum)%64) ∧ t.getReg .x19=W (d+8*((k+ws.sum)/64)) := by
  induction ws generalizing s k a d with
  | nil=>
    refine ⟨Open.Runs.refl _,pc,remaining,?_,?_⟩ <;> simp only [List.sum_nil,Nat.add_zero,Nat.mod_eq_of_lt hk,
      Nat.div_eq_of_lt hk,Nat.mul_zero] <;> assumption
  | cons w ws ih=>
    obtain ⟨wpos,wle,full,rest⟩:=proper
    let n:=w+ws.sum
    have select : min n 64=w := by
      cases ws with
      | nil=>simp [n,min_eq_left wle]
      | cons v tail=>have h:=full (by simp);simp [n,h]
    have sameShort : (decide (n<64))=(decide (w<64)) := by rw [←select];by_cases h : n<64 <;> simp [h,min_eq_left,min_eq_right] <;> omega
    have rA : accessValid (s.getReg .x10) 8=true := by
      rw [src];apply access_ok _ _ (by simp only [List.length_cons] at spaceA;omega) (by change _≤2^36 at spaceA;omega) aa
    have rD : accessValid (s.getReg .x19) 8=true := by
      rw [dst];apply access_ok _ _ (by simp only [List.length_cons] at spaceD;omega) (by change _≤2^36 at spaceD;omega) da
    obtain ⟨_,one,progress⟩:=chunk_run s pc n k (by dsimp [n];omega) small hk remaining bits threshold rA rD
    obtain ⟨p,rem,pending,input,output⟩:=progress
    rw [select,sameShort] at one p rem pending input output
    let u:=pathEnd s (chunkCode (w<64) (k+w))
    let d':=if k+w<64 then d else d+8
    have a' : u.getReg .x10=W (a+8) := by rw [show u.getReg .x10=_ from input,src];exact (BitVec.ofNat_add a 8).symm
    have dest' : u.getReg .x19=W d' := by rw [show u.getReg .x19=_ from output,dst];unfold d';split <;> first | rfl | exact (BitVec.ofNat_add d 8).symm
    have align' : d'%8=0 := by dsimp [d'];split <;> omega
    have room' : d'+8*ws.length≤MEMORY_BYTES := by simp only [List.length_cons] at spaceD;dsimp [d'];split <;> omega
    have tail:=ih u ((k+w)%64) (a+8) d' rest (by change w+ws.sum≤256 at small;omega) (Nat.mod_lt _ (by decide))
      p (rem.trans (congrArg (BitVec.ofNat 64) (show n-w=ws.sum by dsimp [n];omega))) pending ((keep_threshold ..).trans threshold)
      a' dest' (by omega) align' (by simp only [List.length_cons] at spaceA;omega) room'
    obtain ⟨more,back,done_,held,ptr⟩:=tail
    simp only [stream,List.length_append,end_append,List.sum_cons]
    refine ⟨one.trans more,back,done_,held.trans (congrArg W (by omega)),ptr.trans (congrArg W ?_)⟩
    dsimp [d'];split <;> omega
end CommitGolfCandidate.S5Machine.Writer
