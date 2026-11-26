import CommitGolfCandidate.ReconstructedBindingReplay
import CommitGolfCandidate.TwoPermutationCheckerPaths

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf OracleComp TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64

theorem history_mono {early late : List PublicRow} (more : early ⊆ late) :
    history early ⊆ history late := by
  rintro ⟨k,v⟩ h
  exact (mem_history _ _ _).2 (more ((mem_history _ _ _).1 h))

theorem Path.mono {early late : History} (more : early ⊆ late)
    {C h dir root leaf} (p : Path early C h dir root leaf) : Path late C h dir root leaf := by
  induction p with
  | root => exact .root _
  | step _ l r side cl cr seen ok ih => exact .step ih l r side cl cr (fun j hj => more (seen j hj)) ok

theorem ReplayWitness.mono {early late : List PublicRow} (more : early ⊆ late)
    (hit : ReplayWitness early) : ReplayWitness late := by
  have keep := history_mono more
  rcases hit with ⟨a,b,v,ne,ha,hb⟩ | ⟨C,d,l,r,l',r',cl,cr,cl',cr',ha,hb,ne,eq⟩ |
    ⟨p,i,n,m,x,y,a,b,c,d,h,ne⟩
  · exact Or.inl ⟨a,b,v,ne,keep ha,keep hb⟩
  · exact Or.inr (Or.inl ⟨C,d,l,r,l',r',cl,cr,cl',cr',fun j hj => keep (ha j hj),
      fun j hj => keep (hb j hj),ne,eq⟩)
  · exact Or.inr (Or.inr ⟨p,i,n,m,x,y,more a,more b,more c,more d,h,ne⟩)

def oracleCompression (oracle : Oracle) : Compress :=
  fun k => unpack (oracle.compression (encodeKey k))

def route (index : Index) := (List.range 24).map (fun bit => index.val.testBit bit)

structure Opening (oracle : Oracle) (index : Index) (value : Entry) (root : Commitment)
    (rows : List PublicRow) where
  nonce : TwoPermutationPrototype.Words 2
  first : let a := pinnedFirstRow oracle.permutation (entryWords value)
    PublicRow.permutation a.1 a.2 ∈ rows
  second : let a := pinnedFirstRow oracle.permutation (entryWords value)
    let b := pinnedSecondRow oracle.permutation index nonce a.2 (entryWords value)
    PublicRow.permutation b.1 b.2 ∈ rows
  path : let a := pinnedFirstRow oracle.permutation (entryWords value)
    let b := pinnedSecondRow oracle.permutation index nonce a.2 (entryWords value)
    Path (history rows) (oracleCompression oracle) 24 (route index) (unpack root) (unpack (leafDigestW 240 b.2))

theorem opening_conflict (oracle : Oracle) (index : Index) (root : Commitment) (a b : Entry)
    (different : a ≠ b) (rows₀ rows₁ : List PublicRow)
    (l : Opening oracle index a root rows₀) (r : Opening oracle index b root rows₁) :
    ReplayWitness (rows₀ ++ rows₁) := by
  classical
  let all := rows₀ ++ rows₁
  by_cases full : FullCollision (history all)
  · exact Or.inl full
  by_cases paid : ∃ (c : Compress) (d : Fin 24), PaidCollision (history all) c d
  · exact Or.inr (Or.inl paid)
  have inl : rows₀ ⊆ all := fun _ h => List.mem_append_left _ h
  have inr : rows₁ ⊆ all := fun _ h => List.mem_append_right _ h
  have eq := path_leaf_unique (by decide) full (fun d hd hit => paid ⟨_,⟨d,hd⟩,hit⟩)
    (l.path.mono (history_mono inl)) (r.path.mono (history_mono inr))
  exact Or.inr (Or.inr ⟨oracle.permutation,index,l.nonce,r.nonce,entryWords a,entryWords b,
    inl l.first,inr r.first,inl l.second,inr r.second,by simpa using congrArg pack eq,
    fun e => different (entry_words_injective e)⟩)

end CommitGolfCandidate.Reconstruction.Binding
