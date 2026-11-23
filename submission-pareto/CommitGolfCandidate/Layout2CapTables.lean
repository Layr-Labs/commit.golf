import CommitGolfCandidate.Layout2Codec
namespace CommitGolfCandidate.Layout2.Cap

def size (m : Nat) := 238*(m/8)+30*(m%8)
def body (j : Nat) := 24*j+8*(46*j/64)
def tailBit (m s : Nat) :=
  let d:=s/64
  if d<46*m/64 then 8*(body ((64*(d+1)-1)/46)+24)+s%64
  else 8*body m+s-64*(46*m/64)

def dec : Tables := fun m i =>
  let g:=i/1904
  let j:=(i%1904)/240
  let b:=(i%1904)%240
  let node:=8*g+j
  if b<192 then 8*body node+b
  else if b<238 then tailBit m (46*node+(b-192))
  else if g<m/8 then tailBit m (46*(8*g+7)+32+2*j+(b-238))
  else 8*body m+(46*m)%64+2*j+(b-238)

def oldTailBit (m s : Nat) :=
  let j:=s/46
  let b:=s%46
  if 46*m≤s then 1904*(m/8)+240*((s-46*m)/2)+238+(s-46*m)%2
  else if j%8=7 ∧ 32≤b then 1904*(j/8)+240*((b-32)/2)+238+(b-32)%2
  else 1904*(j/8)+240*(j%8)+192+b

def enc : Tables := fun m i =>
  if 8*body m ≤ i then oldTailBit m (64*(46*m/64)+(i-8*body m))
  else
    let j:=(32*(i/64+1)-1)/119
    let b:=i-8*body j
    if b<192 then 1904*(j/8)+240*(j%8)+b
    else oldTailBit m (64*(46*j/64)+(b-192))

def offset : Nat → Nat
  | 0 => 0
  | 1 => 100928
  | 2 => 101408
  | 3 => 102368
  | 4 => 103808
  | 5 => 105728
  | 6 => 108128
  | 7 => 111008
  | 8 => 114368
  | 9 => 118176
  | 10 => 122464
  | 11 => 127232
  | 12 => 132480
  | 13 => 138208
  | 14 => 144416
  | 15 => 151104
  | 16 => 158272
  | 17 => 165888
  | 18 => 173984
  | 19 => 182560
  | 20 => 191616
  | 21 => 201152
  | 22 => 211168
  | 23 => 221664
  | 24 => 232640
  | 25 => 244064
  | 26 => 255968
  | 27 => 268352
  | 28 => 281216
  | 29 => 294560
  | 30 => 308384
  | 31 => 322688
  | 32 => 85696
  | _ => 0

end CommitGolfCandidate.Layout2.Cap
