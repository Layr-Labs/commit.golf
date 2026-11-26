import CommitGolfCandidate.ProofCodecBits

/-! Generic interior-tail packing: concatenate low parts, then concatenate high parts. -/
namespace CommitGolfCandidate.Chained.SplitCodec
open CommitGolf

abbrev Spec := List (Nat × Nat)

inductive Payload : Spec → Type where
  | nil : Payload []
  | cons {low high : Nat} {spec : Spec} (value : BitVec (low+high))
      (rest : Payload spec) : Payload ((low,high)::spec)

def lowCount (spec : Spec) : Nat := (spec.map Prod.fst).sum
def highCount (spec : Spec) : Nat := (spec.map Prod.snd).sum

def lows : {spec : Spec} → Payload spec → List Bool
  | [],.nil => []
  | (low,_)::_,.cons value rest => (List.ofFn fun b : Fin low => value.getLsbD b.val) ++ lows rest

def highs : {spec : Spec} → Payload spec → List Bool
  | [],.nil => []
  | (low,high)::_,.cons value rest =>
    (List.ofFn fun b : Fin high => value.getLsbD (low+b.val)) ++ highs rest

@[simp] theorem lows_length {spec : Spec} (payload : Payload spec) : (lows payload).length = lowCount spec := by
  induction payload <;> simp_all [lows,lowCount]

@[simp] theorem highs_length {spec : Spec} (payload : Payload spec) : (highs payload).length = highCount spec := by
  induction payload <;> simp_all [highs,highCount]

def word (low high : Nat) (front tail : List Bool) : BitVec (low+high) :=
  BitVec.ofFnLE fun b => if b.val < low then front.getD b.val false else tail.getD (b.val-low) false

theorem word_prefix (low high : Nat) (value : BitVec (low+high)) (front tail : List Bool) :
    word low high ((List.ofFn fun b : Fin low => value.getLsbD b.val) ++ front)
      ((List.ofFn fun b : Fin high => value.getLsbD (low+b.val)) ++ tail) = value := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [word,BitVec.getLsbD_ofFnLE,dite_eq_left inside]
  by_cases before : bit < low
  · rw [ite_eq_left before]
    have index : bit < (List.ofFn fun b : Fin low => value.getLsbD b.val).length := by simpa using before
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_left index]
    simp only [List.getElem?_ofFn,before,↓reduceDIte,Option.getD_some]
  · have after : bit-low < high := by omega
    rw [ite_eq_right before]
    have index : bit-low < (List.ofFn fun b : Fin high => value.getLsbD (low+b.val)).length := by simpa using after
    rw [List.getD_eq_getElem?_getD,List.getElem?_append_left index]
    simp only [List.getElem?_ofFn,after,↓reduceDIte,Option.getD_some]
    exact congrArg value.getLsbD (by omega)

def fields : (spec : Spec) → List Bool → List Bool → Payload spec
  | [],_,_ => .nil
  | (low,high)::spec,front,tail =>
    .cons (word low high front tail) (fields spec (front.drop low) (tail.drop high))

theorem fields_parts {spec : Spec} (payload : Payload spec) : fields spec (lows payload) (highs payload) = payload := by
  induction payload with
  | nil => rfl
  | @cons low high spec value rest ih =>
    simp only [lows,highs,fields,word_prefix]
    rw [List.drop_left' (show (List.ofFn fun b : Fin low => value.getLsbD b.val).length = low by simp),
      List.drop_left' (show (List.ofFn fun b : Fin high => value.getLsbD (low+b.val)).length = high by simp),ih]

def packBits (count : Nat) (bits : Nat → Bool) : Proof :=
  List.ofFn fun p : Fin ((count+7)/8) =>
    BitVec.ofFnLE fun b : Fin 8 => if 8*p.val+b.val < count then bits (8*p.val+b.val) else false

def readBit (proof : Proof) (bit : Nat) : Bool := (proof.getD (bit/8) 0).getLsbD (bit%8)

@[simp] theorem pack_bits_length (count : Nat) (bits : Nat → Bool) :
    (packBits count bits).length = (count+7)/8 := by simp [packBits]

theorem read_pack_bits (count : Nat) (bits : Nat → Bool) (bit : Nat) (inside : bit < count) :
    readBit (packBits count bits) bit = bits bit := by
  have index : bit/8 < (count+7)/8 := by omega
  simp only [readBit,packBits,List.getD_eq_getElem?_getD,List.getElem?_ofFn,index,
    ↓reduceDIte,Option.getD_some,BitVec.getLsbD_ofFnLE]
  rw [dite_eq_left (Nat.mod_lt _ (by decide))]
  simp only [show 8*(bit/8)+bit%8 = bit by omega,ite_eq_left inside]

def unpackBits (count : Nat) (proof : Proof) : List Bool :=
  List.ofFn fun b : Fin count => readBit proof b.val

theorem unpack_pack_bits (bits : List Bool) :
    unpackBits bits.length (packBits bits.length (fun bit => bits.getD bit false)) = bits := by
  apply List.ext_getElem
  · simp [unpackBits]
  intro bit left right
  simp only [unpackBits,List.getElem_ofFn]
  rw [read_pack_bits _ _ bit right]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem right,Option.getD_some]

def encode {spec : Spec} (payload : Payload spec) : Proof :=
  let bits := lows payload ++ highs payload
  packBits bits.length (fun bit => bits.getD bit false)

def decode (spec : Spec) (proof : Proof) : Payload spec :=
  let bits := unpackBits (lowCount spec+highCount spec) proof
  fields spec (bits.take (lowCount spec)) (bits.drop (lowCount spec))

theorem encode_length {spec : Spec} (payload : Payload spec) :
    (encode payload).length = (lowCount spec+highCount spec+7)/8 := by
  simp [encode]

theorem decode_encode {spec : Spec} (payload : Payload spec) : decode spec (encode payload) = payload := by
  have total : (lows payload ++ highs payload).length = lowCount spec+highCount spec := by simp
  unfold decode encode
  rw [←total,unpack_pack_bits]
  dsimp only
  rw [←lows_length payload,List.take_left,List.drop_left]
  exact fields_parts payload

def unpack (spec : Spec) (proof : Proof) : Option (Payload spec) :=
  if proof.length = (lowCount spec+highCount spec+7)/8 then
    if encode (decode spec proof) = proof then some (decode spec proof) else none
  else none

theorem unpack_encode {spec : Spec} (payload : Payload spec) : unpack spec (encode payload) = some payload := by
  simp [unpack,encode_length,decode_encode]

theorem unpack_bad_length (spec : Spec) (proof : Proof)
    (bad : proof.length ≠ (lowCount spec+highCount spec+7)/8) : unpack spec proof = none := by
  simp [unpack,bad]

theorem unpack_noncanonical (spec : Spec) (proof : Proof)
    (bad : encode (decode spec proof) ≠ proof) : unpack spec proof = none := by
  simp [unpack,bad]

theorem accepted_encode {spec : Spec} (proof : Proof) (payload : Payload spec)
    (accepted : unpack spec proof = some payload) : encode payload = proof := by
  unfold unpack at accepted
  split at accepted
  · split at accepted
    · rename_i canonical
      have same : decode spec proof = payload := Option.some.inj accepted
      exact same ▸ canonical
    · cases accepted
  · cases accepted

theorem encode_injective {spec : Spec} : Function.Injective (@encode spec) := by
  intro first second same
  have decoded := congrArg (decode spec) same
  simpa only [decode_encode] using decoded

theorem unpack_empty : unpack [] [] = some .nil := rfl

theorem reject_padding : (unpack [(1,0)] [2#8]).isNone = true := by decide +kernel

end CommitGolfCandidate.Chained.SplitCodec
