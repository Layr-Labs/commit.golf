import CommitGolfCandidate.CapBHandler
import CommitGolfCandidate.Layout2CapCodec
import CommitGolfCandidate.QuartetConcrete
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Layout2Helpers
open TwoPermutationPrototype.GroupedOpening.CapB (carryBits handlerLen flushBytes)
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

abbrev D := BitVec 256
def dw (x : D) (j : Nat) : Word := x.extractLsb' (64*j) 64
def wordBytes (w : Word) := List.ofFn (fun j : Fin 8=>extractByte w j.val)
def emittedWords (j : Nat) (carry : Word) (x : D) : List Word :=
  List.ofFn (fun i : Fin (width j)=>nextWord j carry (dw x) i.val)
structure Stream where
  count : Nat
  out : List Word
  carry : Word
def emptyStream (seed : Word) : Stream := ⟨0,[],seed⟩
def push (st : Stream) (x : D) : Stream :=
  ⟨st.count+1,st.out++emittedWords (st.count%32) st.carry x,nextCarry (st.count%32) st.carry (dw x 3)⟩
def stream (seed : Word) (xs : List D) := xs.foldl push (emptyStream seed)
def capBytes (seed : Word) (xs : List D) : List Byte :=
  let v:=stream seed xs
  v.out.flatMap wordBytes++(wordBytes v.carry).take (flushBytes (xs.length%32))
theorem stream_snoc (seed xs x) : stream seed (xs++[x])=push (stream seed xs) x := by simp [stream,List.foldl_append]
theorem stream_count (seed xs) : (stream seed xs).count=xs.length := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp only [stream_snoc,push,List.length_append,List.length_singleton,ih]

private theorem stepCount : ∀ i : Fin 32, Layout2.Cap.body (i.val+1) = Layout2.Cap.body i.val+8*width i.val := by decide +kernel

theorem body_step (n : Nat) : Layout2.Cap.body (n+1)=Layout2.Cap.body n+8*width (n%32) := by
  let j:=n%32;let g:=n/32
  have expr : n=32*g+j := by dsimp [g,j];omega
  have h:=stepCount ⟨j,by dsimp [j];omega⟩
  change 24*(j+1)+8*(46*(j+1)/64)=24*j+8*(46*j/64)+8*width j at h
  change 24*(n+1)+8*(46*(n+1)/64)=24*n+8*(46*n/64)+8*width j
  have a : 46*n/64=23*g+(46*j/64) := by omega
  have b : 46*(n+1)/64=23*g+(46*(j+1)/64) := by omega
  omega

theorem stream_size (seed xs) : 8*(stream seed xs).out.length=Layout2.Cap.body xs.length := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [stream_snoc,push,List.length_append,List.length_ofFn,emittedWords,List.length_singleton,stream_count,Nat.mul_add,ih,body_step]

theorem flush_range : ∀ j : Fin 32, flushBytes j.val≤8 ∧ Layout2.Cap.body j.val+flushBytes j.val=Layout2.Cap.size j.val := by decide +kernel
theorem byte_count (seed xs) : (capBytes seed xs).length=Layout2.Cap.size xs.length := by
  let n:=xs.length;let j:=n%32;let g:=n/32
  have pos : j<32 := by dsimp [j];omega
  have f:=flush_range ⟨j,pos⟩
  change flushBytes j≤8 ∧ Layout2.Cap.body j+flushBytes j=Layout2.Cap.size j at f
  have flat : ∀ ws : List Word,(ws.flatMap wordBytes).length=8*ws.length := by
    intro ws;induction ws with | nil=>rfl | cons w rest ih=>simp [wordBytes,List.flatMap_cons,ih,Nat.mul_add]
  simp only [capBytes,List.length_append,flat,stream_size,List.length_take,wordBytes,List.length_ofFn]
  change Layout2.Cap.body n+min (flushBytes j) 8=Layout2.Cap.size n
  rw [Nat.min_eq_left f.1,Layout2.Cap.split_size]
  have expr : n=32*g+j := by dsimp [g,j];omega
  have a : 46*n/64=23*g+46*j/64 := by omega
  have fj : 24*j+8*(46*j/64)+flushBytes j=Layout2.Cap.size j := f.2
  unfold Layout2.Cap.body;change _=952*g+Layout2.Cap.size j
  omega

structure Buffer (s t : MachineState) (base : Nat) (ws : List Word) : Prop where
  word : ∀ j,j<ws.length → gword t (base+8*j)=ws.getD j 0
  frame : ∀ w : Word,w.toNat<base ∨ base+8*ws.length≤w.toNat → t.getMem w=s.getMem w
theorem Buffer.empty (s base) : Buffer s s base [] := ⟨fun j hj=>by simp at hj,fun _ _=>rfl⟩
theorem Buffer.mem {s m t b ws} (a : Buffer s m b ws) (same : t.mem=m.mem) : Buffer s t b ws := by
  exact ⟨fun j hj=>by simpa only [gword,MachineState.getMem,same] using a.word j hj,fun w h=>by simpa only [MachineState.getMem,same] using a.frame w h⟩

theorem Buffer.append {s m t b xs ys} (a : Buffer s m b xs) (room : b+8*(xs.length+ys.length)≤MEMORY_BYTES)
    (words : ∀ j,j<ys.length → gword t (b+8*xs.length+8*j)=ys.getD j 0)
    (rest : ∀ w : Word,(∀ j,j<ys.length → w≠addr (b+8*xs.length+8*j)) → t.getMem w=m.getMem w) :
    Buffer s t b (xs++ys) := by
  have lim : MEMORY_BYTES<2^64 := by decide
  constructor
  · intro j hj;simp only [List.length_append] at hj
    by_cases old : j<xs.length
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left old]
      refine (rest (addr (b+8*j)) ?_).trans (a.word j old)
      intro k hk eq
      have h:=congrArg BitVec.toNat eq
      simp only [addr,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show b+8*j<2^64 by omega),
        Nat.mod_eq_of_lt (show b+8*xs.length+8*k<2^64 by omega)] at h;omega
    · rw [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
      simpa only [show b+8*xs.length+8*(j-xs.length)=b+8*j by omega,List.getD_eq_getElem?_getD] using words (j-xs.length) (by omega)
  · intro w hw;simp only [List.length_append] at hw
    refine (rest w ?_).trans (a.frame w (by omega))
    intro j hj eq;rw [eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hw;omega

end CommitGolfCandidate.CapB
