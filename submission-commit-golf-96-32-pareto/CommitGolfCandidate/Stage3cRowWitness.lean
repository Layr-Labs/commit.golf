import CommitGolfCandidate.Stage3cReplayBound
namespace CommitGolfCandidate.Chained.Replay
open CommitGolf

def rowReads (rows : List PublicRow) (H : Compression) (inputs : List Input) : Prop :=
  ∀ x∈inputs, .compression x (H x)∈rows

def rowPath (rows : List PublicRow) (H : Compression) (v : Output) : List LayerStep→Prop
  | []=>True
  | s::rest=>let c:=children s.right v s.sibling
             (∀ j<calls s.height, let x:=stageInput H s.height c.1 c.2 j; .compression x (H x)∈rows) ∧
               rowPath rows H (nextNode H v s) rest

theorem path_stored (t : Trace) (rows : List PublicRow) (H : Compression) (v : Output) (path : List LayerStep)
    (stored : ∀ row∈rows, Stored t row) (present : rowPath rows H v path) : pathRecorded t H v path := by
  induction path generalizing v with
  | nil => trivial
  | cons s ps ih =>
    constructor
    · intro j inside;exact stored _ (present.1 j inside)
    · exact ih _ present.2

theorem witness_of_paths (rows : List PublicRow) (H : Compression) (odd : Bool)
    (s u : Late.Salt) (v w : Entry) (left right : List LayerStep) (diff : v≠w)
    (shape : left.map (fun z=>(z.height,z.right))=right.map (fun z=>(z.height,z.right)))
    (l : rowReads rows H (Late.inputs H odd s v)) (r : rowReads rows H (Late.inputs H odd u w))
    (lp : rowPath rows H (Late.leaf H odd s v) left) (rp : rowPath rows H (Late.leaf H odd u w) right)
    (root : walk H (Late.leaf H odd s v) left=walk H (Late.leaf H odd u w) right) : Witness rows := by
  intro t stored
  exact opening_witness t H odd s u v w left right diff shape (fun x hx=>stored _ (l x hx))
    (fun x hx=>stored _ (r x hx)) (path_stored t rows H _ left stored lp)
    (path_stored t rows H _ right stored rp) root
end CommitGolfCandidate.Chained.Replay
