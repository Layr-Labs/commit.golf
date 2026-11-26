import CommitGolfCandidate.ReconstructedCapPayload

namespace CommitGolfCandidate.Reconstruction.CapWriter
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype OpeningPut Wire Encoding
open OpeningCursor (W)
open TwoPermutationPrototype.RV64
set_option maxRecDepth 11000

def lowMemory (m : Memory) (c d : Nat) (r : Nat→Word) :=
  put (put (put (put m c 64 (r 0)) (c+64) 64 (r 1)) (c+128) 64 (r 2))
    (c+192) (lows d-192) (r 3 &&& CapPayload.mask (lows d-192))

theorem snoc (m : Memory) (fs : List Field) (f : Field) (v : Word) (valid : Serialized m (pack fs))
    (value : v.toNat=clipped f) (width : f.width≤64) (room : bits fs/64<capacity) :
    Serialized (put m (bits fs) f.width v) (pack (fs++[f])) := by
  have bound : v.toNat<2^f.width := value ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have h := serial_put m (pack fs) (bits fs) f.width v valid (pack_bound fs) bound width room
  rwa [value,append_field] at h

theorem low_width (m : Memory) (fs : List Field) (d : Nat) (node : Binding.Digest) (r : Nat→Word)
    (vals : CapPayload.Values r d node) (valid : Serialized m (pack fs))
    (room : (bits fs+192)/64<capacity) (topWidth : lows d-192≤64) :
    Serialized (lowMemory m (bits fs) d r) (pack (fs++lowFields node (lows d))) := by
  let a : Field := ⟨node.1.toNat,64⟩
  let b : Field := ⟨node.1.toNat >>> 64,64⟩
  let e : Field := ⟨node.1.toNat >>> 128,64⟩
  let f : Field := ⟨node.2.toNat,lows d-192⟩
  let c := bits fs
  have width : f.width≤64 := topWidth
  have first := snoc m fs a (r 0) valid vals.first (Nat.le_refl 64) (by omega)
  have one : bits (fs++[a])=c+64 := by rw [bits_append];rfl
  have two : bits (fs++[a,b])=c+128 := by rw [bits_append];rfl
  have three : bits (fs++[a,b,e])=c+192 := by rw [bits_append];rfl
  have second := snoc _ (fs++[a]) b (r 1) first vals.second (Nat.le_refl 64) (by rw [one];dsimp [c];omega)
  rw [one,List.append_assoc] at second
  have third := snoc _ (fs++[a,b]) e (r 2) second vals.third (Nat.le_refl 64) (by rw [two];dsimp [c];omega)
  rw [two,List.append_assoc] at third
  have final := snoc _ (fs++[a,b,e]) f (r 3 &&& CapPayload.mask f.width) third vals.top width (by rw [three];exact room)
  rw [three,List.append_assoc] at final
  exact final

theorem low (m : Memory) (fs : List Field) (d : Fin 10) (node : Binding.Digest) (r : Nat→Word)
    (vals : CapPayload.Values r d.val node) (valid : Serialized m (pack fs))
    (room : (bits fs+192)/64<capacity) :
    Serialized (lowMemory m (bits fs) d.val r) (pack (fs++lowFields node (lows d.val))) :=
  low_width m fs d.val node r vals valid room ((by decide : ∀ j : Fin 10, lows j.val-192≤64) d)

theorem low_all (m : Memory) (fs : List Field) (d : Fin 25) (node : Binding.Digest) (r : Nat→Word)
    (vals : CapPayload.Values r d.val node) (valid : Serialized m (pack fs))
    (room : (bits fs+192)/64<capacity) :
    Serialized (lowMemory m (bits fs) d.val r) (pack (fs++lowFields node (lows d.val))) :=
  low_width m fs d.val node r vals valid room ((by decide : ∀ j : Fin 25, lows j.val-192≤64) d)

theorem reverse_stores (m : Memory) (c : Nat) (v : Word) (nz : c%64≠0) :
    writeWord (writeWord m (cell c+1) (v >>> (64-c%64))) (cell c)
      (m (cell c) ||| (v <<< (c%64))) = put m c 64 v := by
  rw [put,ite_eq_left (show c%64+64>64 by omega),first,ite_eq_right nz]
  funext j
  by_cases eq : j=cell c
  · subst j;simp only [writeWord,ite_true,show cell c≠cell c+1 by omega,ite_false]
  · simp only [writeWord,eq,ite_false]

theorem aligned_store (m : Memory) (c w : Nat) (v : Word) (al : c%64=0) (small : w≤64) :
    writeWord m (cell c) v=put m c w v := by
  simp [put,first,al,show ¬w>64 by omega]

theorem byte_at_boundary (c : Nat) (bound : c<2^64) (al : c%64=0) :
    (W c >>> (3:Nat))+wordAddress base=wordAddress (cell c) := by
  have sh : W c >>> (3:Nat)=W (c/8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,Nat.shiftRight_eq_div_pow]
    change c/8=(c/8)%2^64;omega
  rw [sh]
  unfold wordAddress
  rw [←BitVec.ofNat_add];apply congrArg W;unfold cell;omega

end CommitGolfCandidate.Reconstruction.CapWriter
