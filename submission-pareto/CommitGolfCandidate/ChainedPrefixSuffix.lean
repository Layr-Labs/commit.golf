import CommitGolfCandidate.ChainedPrefixControl
import CommitGolfCandidate.ChainedPrefixTransport

/-! The existing opener's postpass cannot return to the cached-prefix boundary. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.PackedOpening (openingImage)
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def targetsAbove (cut : Nat) (pc : Word) (word : BitVec 32) : Bool :=
  match decodeInstruction word with
  | none => true
  | some instruction => match directTargets pc instruction with
    | none => false
    | some targets => targets.all (fun target => decide (cut<target.toNat))

private theorem suffix_checked : ∀ i : Fin 342,
    targetsAbove 9836 (BitVec.ofNat 64 (9836+4*i.val)) (openingImage.code[1435+i.val]!)=true := by
  decide +kernel

def notEcall (instruction : Option Instruction) : Bool :=
  match instruction with
  | some (.base .ECALL) => false
  | _ => true

private theorem prefix_checked : ∀ i : Fin 1436,
    notEcall ((openingImage.code[i.val]?).bind decodeInstruction)=true := by
  decide +kernel

theorem fetched_index (image : Image) (s : MachineState) (instruction : Instruction)
    (fetched : fetch image s=some instruction) :
    ∃ index : Nat, index < image.code.length ∧ s.pc.toNat=4096+4*index ∧
      (image.code[index]?).bind decodeInstruction=some instruction := by
  unfold fetch at fetched
  split at fetched
  · rename_i aligned
    split at fetched
    · rename_i word found
      obtain ⟨inside,_⟩ := List.getElem?_eq_some_iff.mp found
      refine ⟨(s.pc.toNat-4096)/4,inside,?_,?_⟩
      · omega
      · simp only [found,Option.bind_some]
        exact fetched
    · contradiction
  · contradiction

theorem cached_suffix_step (s next : MachineState) (instruction : Instruction)
    (above : 9836≤s.pc.toNat) (fetched : fetch openingImage s=some instruction)
    (stepped : ordinaryStep s instruction=some next) : 9836<next.pc.toNat := by
  obtain ⟨index,inside,pc,decoded⟩ := fetched_index openingImage s instruction fetched
  change index<1777 at inside
  have lower : 1435 ≤ index := by omega
  have checked := suffix_checked ⟨index-1435,by omega⟩
  have pcWord : s.pc=BitVec.ofNat 64 (9836+4*(index-1435)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  have indexEq : 1435+(index-1435)=index := by omega
  rw [indexEq] at checked
  obtain ⟨word,found⟩ : ∃ word, openingImage.code[index]?=some word := by
    exact ⟨openingImage.code[index],List.getElem?_eq_getElem inside⟩
  have value : openingImage.code[index]! = word := List.getElem!_of_getElem? found
  rw [targetsAbove,value,show decodeInstruction word=some instruction from by simpa [found] using decoded] at checked
  cases targets : directTargets (BitVec.ofNat 64 (9836+4*(index-1435))) instruction with
  | none => simp [targets] at checked
  | some options =>
    simp only [targets] at checked
    have member := ordinary_step_target s next instruction options (by simpa only [pcWord] using targets) stepped
    have := List.all_eq_true.mp checked next.pc member
    simpa using this

private theorem cached_fetch_next_pc (s : MachineState) (instruction : Instruction)
    (above : 9836<s.pc.toNat) (fetched : fetch openingImage s=some instruction) :
    9836<(s.pc+4).toNat := by
  obtain ⟨index,inside,pc,_⟩ := fetched_index openingImage s instruction fetched
  change index<1777 at inside
  rw [BitVec.toNat_add,show (4 : Word).toNat=4 from rfl,Nat.mod_eq_of_lt (by omega)]
  omega

theorem cached_suffix_invariant : ExecutionInvariant openingImage (fun s => 9836<s.pc.toNat) := by
  constructor
  · intro s instruction next above fetched stepped
    exact cached_suffix_step s next instruction (by omega) fetched stepped
  · intro s input answer above fetched
    have advanced := cached_fetch_next_pc s _ above fetched
    cases input with
    | inl input => exact advanced
    | inr input => cases input <;> exact advanced
  · intro s bytes answer above fetched
    exact cached_fetch_next_pc s _ above fetched

theorem cached_prefix_ordinary (s : MachineState) (instruction : Instruction)
    (below : s.pc.toNat≤9836) (fetched : fetch openingImage s=some instruction) :
    instruction≠.base .ECALL := by
  obtain ⟨index,inside,pc,decoded⟩ := fetched_index openingImage s instruction fetched
  have bound : index<1436 := by omega
  intro call
  have checked := prefix_checked ⟨index,bound⟩
  rw [decoded,call] at checked
  contradiction

theorem cached_prefix_replay (target : Image)
    (codePrefix : target.code.take 1435=openingImage.code.take 1435)
    (steps : Nat) (s : MachineState) (coins : Bool) (result : Execution)
    (reached : result∈support (execute openingImage steps s coins))
    (unfinished : result.exit=.unfinished) (below : result.state.pc.toNat≤9836) :
    execute target steps s coins=pure result := by
  exact transport_unfinished_prefix openingImage target 9836 cached_suffix_invariant
    (fun s instruction next pc fetched stepped => cached_suffix_step s next instruction (by omega) fetched stepped)
    cached_prefix_ordinary (fun s small => fetch_eq_of_prefix openingImage target 1435 codePrefix s small)
    steps s coins result reached unfinished below

end CommitGolfCandidate.Chained.Native
