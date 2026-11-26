import CommitGolfCandidate.ReconstructedBindingWork

namespace CommitGolfCandidate.Reconstruction.Binding

abbrev Table := Key → Option Digest

def put (m : Table) (key : Key) (answer : Digest) : Table :=
  fun k => if k = key then some answer else m k

/-- Compute the last query from prior rows only. The lookup of the last answer
is deliberately outside this definition, so a ready but unpaid key is visible. -/
def probe (m : Table) (seed : Key) : Nat → Option Key
  | 0 => some seed
  | i+1 => do
    let prev ← probe m seed i
    let answer ← m prev
    return unary answer

def finish (m : Table) (s : Seed) : Option Digest := do
  let k ← probe m s.key (work s.depth - 1)
  m k

def DistinctAnswers (m : Table) : Prop :=
  ∀ a b v, m a = some v → m b = some v → a = b

private theorem probe_succ_iff {m seed i k} :
    probe m seed (i+1) = some k ↔
    ∃ prev answer, probe m seed i = some prev ∧ m prev = some answer ∧ unary answer = k := by
  simp [probe, Option.bind_eq_some_iff]

/-- The deterministic predecessor of a ready continuation is unique. Thus a
fresh key can complete at most one chain across all paid depths. -/
theorem ready_unique (m : Table) (safe : DistinctAnswers m) (s t : Seed)
    (i j : Nat) {k : Key} (hs : probe m s.key i = some k) (ht : probe m t.key j = some k) :
    s = t ∧ i = j := by
  induction i generalizing j k with
  | zero =>
    have ks := Option.some.inj hs
    cases j with
    | zero => exact ⟨Seed.ext_key _ _ (ks.trans (Option.some.inj ht).symm),rfl⟩
    | succ j =>
      obtain ⟨_,y,_,_,hy⟩ := probe_succ_iff.1 ht
      exact False.elim (s.not_unary _ (ks.trans hy.symm))
  | succ i ih =>
    obtain ⟨prev,y,hp,hy,eq⟩ := probe_succ_iff.1 hs
    cases j with
    | zero => exact False.elim (t.not_unary _ ((Option.some.inj ht).trans eq.symm))
    | succ j =>
      obtain ⟨prev',y',hp',hy',eq'⟩ := probe_succ_iff.1 ht
      have same : y = y' := congrArg Prod.fst (eq.trans eq'.symm)
      have keys := safe prev prev' y hy (same ▸ hy')
      have old := ih j hp (keys ▸ hp')
      exact ⟨old.1,congrArg Nat.succ old.2⟩

/-- A fresh compression reply only extends a known chain from its ready key.
If its unary continuation was queried before it, that reply is charged to
the separate 256-bit random-link event. -/
theorem probe_after_put (m : Table) (k : Key) (y : Digest)
    (newUnary : m (unary y) = none) (noSelf : unary y ≠ k)
    (seed : Key) (n : Nat) {out : Key} (after : probe (put m k y) seed n = some out) :
    probe m seed n = some out ∨ (out = unary y ∧ put m k y out = none) := by
  induction n generalizing out with
  | zero => exact Or.inl after
  | succ n ih =>
    obtain ⟨prev,v,hp,seen,eq⟩ := probe_succ_iff.1 after
    cases ih hp with
    | inr dead => simp [dead.2] at seen
    | inl before =>
      by_cases same : prev = k
      · have ans : y = v := Option.some.inj (by simpa [put,same] using seen)
        have endKey := eq.symm.trans (congrArg unary ans.symm)
        exact Or.inr ⟨endKey,by simp [endKey,put,noSelf,newUnary]⟩
      · exact Or.inl <| probe_succ_iff.2 ⟨prev,v,before,by simpa [put,same] using seen,eq⟩

theorem finish_after_put (m : Table) (k : Key) (y : Digest)
    (newUnary : m (unary y) = none) (noSelf : unary y ≠ k)
    (s : Seed) (v : Digest) (after : finish (put m k y) s = some v) :
    finish m s = some v ∨ (probe m s.key (work s.depth-1) = some k ∧ y = v) := by
  obtain ⟨prev,hp,seen⟩ := Option.bind_eq_some_iff.1 after
  cases probe_after_put m k y newUnary noSelf _ _ hp with
  | inr dead => simp [dead.2] at seen
  | inl before =>
    by_cases eq : prev = k
    · exact Or.inr ⟨eq ▸ before,Option.some.inj (by simpa [put,eq] using seen)⟩
    · exact Or.inl <| Option.bind_eq_some_iff.2 ⟨prev,before,by simpa [put,eq] using seen⟩


def EndpointCollision (m : Table) : Prop :=
  ∃ (a b : Seed) (u v : Digest), a ≠ b ∧ a.depth = b.depth ∧
    finish m a = some u ∧ finish m b = some v ∧ project a.depth u = project a.depth v

def Ready (m : Table) (k : Key) (s : Seed) : Prop :=
  probe m s.key (work s.depth - 1) = some k

theorem endpoint_collision_after_put (m : Table) (k : Key) (y : Digest)
    (safe : DistinctAnswers m) (before : ¬ EndpointCollision m)
    (newUnary : m (unary y) = none) (noSelf : unary y ≠ k)
    (hit : EndpointCollision (put m k y)) :
    ∃ (s t : Seed) (v : Digest), Ready m k s ∧ s.depth = t.depth ∧
      finish m t = some v ∧ project s.depth y = project s.depth v := by
  obtain ⟨a,b,u,v,ne,d,la,lb,eq⟩ := hit
  rcases finish_after_put m k y newUnary noSelf a u la with ha | ⟨ra, rfl⟩
  · rcases finish_after_put m k y newUnary noSelf b v lb with hb | ⟨rb, rfl⟩
    · exact False.elim (before ⟨a,b,u,v,ne,d,ha,hb,eq⟩)
    · exact ⟨b,a,u,rb,d.symm,ha,d ▸ eq.symm⟩
  · rcases finish_after_put m k y newUnary noSelf b v lb with hb | ⟨rb, _⟩
    · exact ⟨a,b,v,ra,d,hb,eq⟩
    · exact False.elim (ne (ready_unique m safe _ _ _ _ ra rb).1)

theorem probe_mono (m m' : Table) (ext : ∀ k v, m k = some v → m' k = some v)
    (seed : Key) (n : Nat) (k : Key) (old : probe m seed n = some k) :
    probe m' seed n = some k := by
  induction n generalizing k with
  | zero => exact old
  | succ n ih =>
    obtain ⟨j,v,probe_j,read,eq⟩ := probe_succ_iff.1 old
    exact probe_succ_iff.2 ⟨j,v,ih j probe_j,ext j v read,eq⟩

theorem finish_mono (m m' : Table) (ext : ∀ k v, m k = some v → m' k = some v)
    (s : Seed) (v : Digest) (old : finish m s = some v) : finish m' s = some v := by
  obtain ⟨k,p,read⟩ := Option.bind_eq_some_iff.1 old
  exact Option.bind_eq_some_iff.2 ⟨k,probe_mono _ _ ext _ _ _ p,ext k _ read⟩

theorem table_ext_put (m : Table) (k : Key) (y : Digest) (fresh : m k = none) :
    ∀ j v, m j = some v → put m k y j = some v := by
  intro j v read
  by_cases same : j = k
  · subst j; simp [fresh] at read
  · simpa [put,same] using read


def extendTable (m : Table) (k : Key) : Digest := (m k).getD zeroDigest

theorem trace_of_probe (m : Table) (k seed : Key) (n : Nat) (ran : probe m seed n = some k) :
    lastKey (extendTable m) seed n = k ∧ ∀ i < n,
      let ki := lastKey (extendTable m) seed i
      m ki = some (extendTable m ki) := by
  induction n generalizing k with
  | zero => exact ⟨Option.some.inj ran,by omega⟩
  | succ n ih =>
    obtain ⟨prev,y,hp,seen,hk⟩ := probe_succ_iff.1 ran
    obtain ⟨key,before⟩ := ih prev hp
    have ans : extendTable m prev = y := by simp [extendTable,seen]
    constructor
    · simpa [lastKey,key,ans] using hk
    · intro i hi
      by_cases eq : i = n
      · simpa [eq,key,ans] using seen
      · exact before i (by omega)

theorem trace_of_finish (m : Table) (s : Seed) (v : Digest) (ran : finish m s = some v) :
    ∀ j, j ≤ work s.depth-1 →
      let k := lastKey (extendTable m) s.key j
      m k = some (extendTable m k) := by
  obtain ⟨k,hp,seen⟩ := Option.bind_eq_some_iff.1 ran
  obtain ⟨key,before⟩ := trace_of_probe m k s.key _ hp
  intro j hj
  by_cases eq : j = work s.depth-1
  · simp [eq,key,extendTable,seen]
  · exact before j (by omega)

end CommitGolfCandidate.Reconstruction.Binding
