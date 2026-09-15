import Std

namespace R44

structure V3 where
  x : Int
  y : Int
  z : Int
deriving BEq, DecidableEq, Hashable, Repr

structure N3 where
  x : Nat
  y : Nat
  z : Nat
deriving BEq, DecidableEq, Hashable, Repr

structure Frame where
  perm : N3
  sign : V3
deriving BEq, DecidableEq, Hashable, Repr

structure Pose where
  frame : Frame
  shift : V3
deriving BEq, DecidableEq, Hashable, Repr

structure Panel where
  axis : Nat
  outward : Int
  center2 : V3
  coefficients : List Int
deriving BEq, DecidableEq, Repr

structure SignEquation where
  left : Nat
  right : Nat
  sign : Int
deriving BEq, DecidableEq, Hashable, Repr

structure CentralRecord where
  shellId : Nat
  requiredMask : Nat
  existingMask : Nat
  viable : List Nat
deriving BEq, DecidableEq, Repr

structure RejectionWitness where
  rejected : Pose
  owner : Nat
  role : Nat
  optionCount : Nat
deriving BEq, DecidableEq, Repr

structure MateRecord where
  pose : Pose
  roles : List Nat
deriving BEq, DecidableEq, Repr

structure Face where
  axis : Nat
  center2 : V3
  outward : Int
deriving BEq, DecidableEq, Repr

structure Feature where
  role : Nat
  center8 : V3
  normal : V3
  coefficient : Int
deriving BEq, DecidableEq, Repr

structure Box where
  lo : V3
  hi : V3
deriving BEq, DecidableEq, Repr

structure EdgeGeometry where
  a : V3
  b : V3
  normal : V3
  opposite : V3
deriving BEq, DecidableEq, Hashable, Repr

def v (x y z : Int) : V3 := ⟨x, y, z⟩
def n3 (x y z : Nat) : N3 := ⟨x, y, z⟩
def fr (p0 p1 p2 : Nat) (s0 s1 s2 : Int) : Frame := ⟨n3 p0 p1 p2, v s0 s1 s2⟩
def po (g : Frame) (t : V3) : Pose := ⟨g, t⟩

def V3.get (a : V3) : Nat → Int
  | 0 => a.x
  | 1 => a.y
  | _ => a.z

def N3.get (a : N3) : Nat → Nat
  | 0 => a.x
  | 1 => a.y
  | _ => a.z

def V3.add (a b : V3) : V3 := v (a.x + b.x) (a.y + b.y) (a.z + b.z)
def V3.sub (a b : V3) : V3 := v (a.x - b.x) (a.y - b.y) (a.z - b.z)
def V3.smul (k : Int) (a : V3) : V3 := v (k * a.x) (k * a.y) (k * a.z)
def V3.neg (a : V3) : V3 := a.smul (-1)

def Frame.act (g : Frame) (a : V3) : V3 :=
  v (g.sign.x * a.get g.perm.x)
    (g.sign.y * a.get g.perm.y)
    (g.sign.z * a.get g.perm.z)

def Frame.mul (g h : Frame) : Frame :=
  fr (h.perm.get g.perm.x) (h.perm.get g.perm.y) (h.perm.get g.perm.z)
    (g.sign.x * h.sign.get g.perm.x)
    (g.sign.y * h.sign.get g.perm.y)
    (g.sign.z * h.sign.get g.perm.z)

def Frame.transpose (g : Frame) : Frame :=
  let inverseIndex (j : Nat) := if g.perm.x == j then 0 else if g.perm.y == j then 1 else 2
  let p := n3 (inverseIndex 0) (inverseIndex 1) (inverseIndex 2)
  fr p.x p.y p.z (g.sign.get p.x) (g.sign.get p.y) (g.sign.get p.z)

def Pose.transform (a b : Pose) : Pose :=
  po (a.frame.mul b.frame) (a.shift.add (a.frame.act b.shift))

def Pose.inverse (a : Pose) : Pose :=
  let g := a.frame.transpose
  po g (g.act a.shift |>.neg)

def Pose.relative (a b : Pose) : Pose := a.inverse.transform b

def identityFrame : Frame := fr 0 1 2 1 1 1
def rootPose : Pose := po identityFrame (v 0 0 0)

def parseInt (s : String) : Int :=
  match s.toInt? with
  | some n => n
  | none => 0

def parseNat (s : String) : Nat := (parseInt s).toNat

def parseIntegerLine (line : String) : List Int :=
  line.splitOn "," |>.map parseInt

def decodePoseNumbers (xs : List Int) : Pose :=
  fr (getD xs 0 0).toNat (getD xs 1 0).toNat (getD xs 2 0).toNat
      (getD xs 3 0) (getD xs 4 0) (getD xs 5 0)
  |> fun g => po g (v (getD xs 6 0) (getD xs 7 0) (getD xs 8 0))
where
  getD (a : List Int) (i : Nat) (fallback : Int) : Int :=
    match a[i]? with | some x => x | none => fallback

def decodePoses (text : String) : List Pose :=
  text.splitOn "\n" |>.filterMap fun line =>
    if line.isEmpty then none else some (decodePoseNumbers (parseIntegerLine line))

def decodeMateRecords (text : String) : List MateRecord :=
  text.splitOn "\n" |>.filterMap fun line =>
    if line.isEmpty then none
    else
      let xs := parseIntegerLine line
      some { pose := decodePoseNumbers xs, roles := (xs.drop 9).map Int.toNat }

def decodeRejectionWitnesses (text : String) : List RejectionWitness :=
  text.splitOn "\n" |>.filterMap fun line =>
    if line.isEmpty then none
    else
      let xs := parseIntegerLine line
      let pick (i : Nat) : Int := match xs[i]? with | some x => x | none => 0
      some {
        rejected := decodePoseNumbers xs
        owner := (pick 9).toNat
        role := (pick 10).toNat
        optionCount := (pick 11).toNat
      }

def decodeV3s (text : String) : List V3 :=
  text.splitOn "\n" |>.filterMap fun line =>
    if line.isEmpty then none
    else
      let xs := parseIntegerLine line
      let pick (i : Nat) : Int := match xs[i]? with | some x => x | none => 0
      some (v (pick 0) (pick 1) (pick 2))

def decodeN3s (text : String) : List N3 :=
  text.splitOn "\n" |>.filterMap fun line =>
    if line.isEmpty then none
    else
      let xs := parseIntegerLine line
      let pick (i : Nat) : Nat :=
        match xs[i]? with | some x => x.toNat | none => 0
      some (n3 (pick 0) (pick 1) (pick 2))

end R44
