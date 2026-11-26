import CommitGolfCandidate.ReconstructedCheckParentPlan

namespace CommitGolfCandidate.Reconstruction.CheckParentCall
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary CheckParentImage CheckParentRun CheckParentPlan CheckOracleMemory CheckRecorded
open TwoPermutationPrototype.Sampling
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1200000
set_option maxRecDepth 15000
attribute [local irreducible] readBuffer

def key (o : Oracle) (seed : Key) (q : Nat) := lastKey (oracleCompression o) seed q
def result (o : Oracle) (seed : Key) (q : Nat) := o.compression (encodeKey (key o seed q))
def row (o : Oracle) (seed : Key) (q : Nat) := PublicRow.compression (encodeKey (key o seed q)) (result o seed q)

structure Params (o : Oracle) (env : Env) (d : Nat) (seed : Key) : Prop where
  inputWords : ∀ q<work d, ∀ i : Fin 8,
    (rowWord d q i).val env = (encodeKey (key o seed q)).extractLsb' (64*i.val) 64
  answers : ∀ q<work d, ∀ i<4, env.answer q i=(result o seed q).extractLsb' (64*i) 64
  addresses : ∀ q<work d,
    let src := (physical env (input q)).toNat
    let dst := (physical env (output d q)).toNat
    src+64≤MEMORY_BYTES ∧ dst+32≤MEMORY_BYTES ∧ src%8=0 ∧ dst%8=0 ∧
      (∀ i : Fin 8, table.allowed (atIndex (input q) i)=true) ∧ (∀ i : Fin 4, table.allowed (atIndex (output d q) i)=true)

private theorem word_read (s : MachineState) (a : Nat) (aligned : a%8=0) :
    readBuffer s a 8=s.getMem (BitVec.ofNat 64 a) := by
  have part := read_buffer_slice s a 32 0 8 (by decide)
  have word := read_digest_word s a 0 aligned (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using part.symm.trans word

theorem read_words_eq (s : MachineState) (src : Nat) (n : Nat) (b : BitVec (64*n))
    (aligned : src%8=0) (values : ∀ i<n, s.getMem (BitVec.ofNat 64 (src+8*i))=b.extractLsb' (64*i) 64) :
    (readBuffer s src (8*n)).cast (by omega) = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit limited
  let j:=bit/64
  have jlt : j<n := by dsimp [j];omega
  have slice := read_buffer_slice s src (8*n) (8*j) 8 (by omega)
  rw [word_read s _ (by omega),values j jlt] at slice
  have h := congrArg (fun x : BitVec 64=>x.getLsbD (bit%64)) slice
  simp only [BitVec.getLsbD_extractLsb',show bit%64<64 by omega,decide_true,Bool.true_and,
    show 8*(8*j)+bit%64=bit by dsimp [j];omega,show 64*j+bit%64=bit by dsimp [j];omega] at h
  simpa only [BitVec.getLsbD_cast] using h

private theorem read_eight (s : MachineState) (src : Nat) (b : BitVec 512) (aligned : src%8=0)
    (values : ∀ i<8, s.getMem (BitVec.ofNat 64 (src+8*i))=b.extractLsb' (64*i) 64) :
    readBuffer s src 64 = b := by
  have v := read_words_eq s src 8 b aligned values
  change (readBuffer s src 64).cast _ = b at v
  rw [BitVec.cast_eq] at v
  exact v

private theorem extract_site (a : Action) (checked : (match a with | .oracle _=>true | _=>false)=true) :
    ∃ site, a=Action.oracle site := by cases a <;> simp_all

private theorem registers (env : Env) (s : MachineState) (d q : Nat) (m : State) (h : Matches env m s)
    (h5 : m.get .x5=.lit 0) (h10 : m.get .x10=.ptr (input q)) (h11 : m.get .x11=.lit 64)
    (h12 : m.get .x12=.ptr (output d q)) (h13 : m.get .x13=.lit 0) :
    s.getReg .x5=0 ∧ s.getReg .x10=physical env (input q) ∧ s.getReg .x11=64 ∧
      s.getReg .x12=physical env (output d q) ∧ s.getReg .x13=0 := by
  rw [h.regs .x5,h.regs .x10,h.regs .x11,h.regs .x12,h.regs .x13,h5,h10,h11,h12,h13]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

private theorem read_operand (o : Oracle) (env : Env) (layout : Layout env table) (d q : Nat) (seed : Key)
    (params : Params o env d seed) (bound : q<work d) (m : State) (s : MachineState) (h : Matches env m s)
    (safe : Safe table m.writes) (src : Nat) (srcP : physical env (input q)=BitVec.ofNat 64 src)
    (srcA : src%8=0) (inOK : ∀ i : Fin 8, table.allowed (atIndex (input q) i)=true)
    (words : ∀ i : Fin 8, look table (atIndex (input q) i) m.writes=rowWord d q i) :
    readBuffer s src 64=encodeKey (key o seed q) := by
  apply read_eight s src (encodeKey (key o seed q)) srcA
  intro i hi
  have w := look_sound env table layout m.writes (atIndex (input q) i) (inOK ⟨i,hi⟩) safe
  rw [words ⟨i,hi⟩,params.inputWords q bound ⟨i,hi⟩,←h.mem,physical_index,srcP,←BitVec.ofNat_add] at w
  exact w.symm

private theorem after_matches (o : Oracle) (env : Env) (d q : Nat) (seed : Key)
    (params : Params o env d seed) (bound : q<work d) (m : State) (s : MachineState) (h : Matches env m s)
    (dst : Nat) (dstP : physical env (output d q)=BitVec.ofNat 64 dst) (dstA : dst%8=0) (room : dst+32≤2^64) :
    Matches env (modelWrite d q m) (CommitParents.callAfter s o dst (key o seed q)) :=
  reply env m s h _ q 4 (result o seed q) (params.answers q bound) dst dstP dstA room

theorem call_step (o : Oracle) (env : Env) (layout : Layout env table) (d q : Nat) (seed : Key)
    (params : Params o env d seed) (bound : q<work d) (hit : Hit) (s : MachineState) (h : Matches env hit.state s)
    (safe : Safe table hit.state.writes) (pc : s.pc=CommitBlocks.addr (674+hit.site.val))
    (fields : callFields d q hit=true) :
    ∃ t, Segment o 1 s t [row o seed q] ∧ Matches env (modelWrite d q hit.state) t ∧ Safe table (modelWrite d q hit.state).writes := by
  simp only [callFields,Bool.and_eq_true,decide_eq_true_eq] at fields
  obtain ⟨evt,h5,h10,h11,h12,h13,words⟩ := fields
  obtain ⟨site,isSite⟩ := extract_site _ evt
  have actual := oracle_site hit.site site isSite
  let src := (physical env (input q)).toNat
  let dst := (physical env (output d q)).toNat
  have srcP : physical env (input q)=BitVec.ofNat 64 src := by simp [src,dst]
  have dstP : physical env (output d q)=BitVec.ofNat 64 dst := by simp [src,dst]
  obtain ⟨srcRoom,dstRoom,srcA,dstA,inOK,outOK⟩ := params.addresses q bound
  have regs := registers env s d q hit.state h h5 h10 h11 h12 h13
  rw [srcP,dstP] at regs
  have read := read_operand o env layout d q seed params bound hit.state s h safe src srcP srcA inOK words
  rw [actual] at pc
  have sg := (compress o site s src dst (key o seed q) pc srcRoom dstRoom srcA dstA read regs).1
  have destRoom : dst+32 ≤ 2^64 := by change dst+32≤MEMORY_BYTES at dstRoom;unfold MEMORY_BYTES at dstRoom;omega
  exact ⟨_,sg,after_matches o env d q seed params bound _ s h dst dstP dstA destRoom,
    safe_install table (output d q) q hit.state.writes safe 4 (fun i hi=>outOK ⟨i,hi⟩)⟩

end CommitGolfCandidate.Reconstruction.CheckParentCall
