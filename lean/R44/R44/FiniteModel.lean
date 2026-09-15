import R44.Generated.CoreData
import R44.Generated.MateData

namespace R44

open Generated

set_option maxRecDepth 1000000

/- Small finite-set operations. Lists carry the literal data; these functions
   deliberately interpret them extensionally. -/

def subset [BEq α] (a b : List α) : Bool := a.all fun x => b.contains x
def setEq [BEq α] (a b : List α) : Bool := subset a b && subset b a
def union [BEq α] (a b : List α) : List α := (a ++ b).eraseDups
def unions [BEq α] (a : List (List α)) : List α := (a.flatten).eraseDups
def inter [BEq α] (a b : List α) : List α := a.filter fun x => b.contains x
def diff [BEq α] (a b : List α) : List α := a.filter fun x => !b.contains x
def noDuplicates [BEq α] (a : List α) : Bool := a.eraseDups.length == a.length

def hashSetEq [BEq α] [Hashable α] (a b : List α) : Bool :=
  let ha := Std.HashSet.ofList a
  let hb := Std.HashSet.ofList b
  ha.size == hb.size && a.all hb.contains

def hashNoDuplicates [BEq α] [Hashable α] (a : List α) : Bool :=
  (Std.HashSet.ofList a).size == a.length

def hashDedup [BEq α] [Hashable α] (a : List α) : List α :=
  (Std.HashSet.ofList a).toList

def hashDiff [BEq α] [Hashable α] (a b : List α) : List α :=
  let unwanted := Std.HashSet.ofList b
  a.filter fun x => !unwanted.contains x

def setFamilyEq [BEq α] (a b : List (List α)) : Bool :=
  a.all (fun x => b.any fun y => setEq x y) &&
  b.all (fun x => a.any fun y => setEq x y)

def getD (a : List α) (i : Nat) (fallback : α) : α :=
  match a[i]? with
  | some x => x
  | none => fallback

def allPairs (a : List α) : List (α × α) :=
  a.flatMap fun x => a.map fun y => (x, y)

def unorderedPairs (a : List α) : List (α × α) :=
  match a with
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

def coordinatePermutations : List N3 :=
  [n3 0 1 2, n3 0 2 1, n3 1 0 2, n3 1 2 0, n3 2 0 1, n3 2 1 0]

def signTriples : List V3 :=
  [v (-1) (-1) (-1), v (-1) (-1) 1, v (-1) 1 (-1), v (-1) 1 1,
   v 1 (-1) (-1), v 1 (-1) 1, v 1 1 (-1), v 1 1 1]

def allFrames : List Frame :=
  coordinatePermutations.flatMap fun p =>
    signTriples.map fun s => fr p.x p.y p.z s.x s.y s.z

def validPermutation (p : N3) : Bool :=
  [p.x, p.y, p.z].all fun i =>
    decide (i < 3) && (([p.x, p.y, p.z].filter fun j => j == i).length == 1)

def validFrame (g : Frame) : Bool :=
  validPermutation g.perm &&
    [g.sign.x, g.sign.y, g.sign.z].all fun s => s == 1 || s == -1

def permutationParity (p : N3) : Int :=
  if p == n3 0 1 2 || p == n3 1 2 0 || p == n3 2 0 1 then 1 else -1

def Frame.det (g : Frame) : Int :=
  permutationParity g.perm * g.sign.x * g.sign.y * g.sign.z

def properFrame (g : Frame) : Bool := validFrame g && g.det == 1

def bits : List V3 :=
  [v 0 0 0, v 0 0 1, v 0 1 0, v 0 1 1,
   v 1 0 0, v 1 0 1, v 1 1 0, v 1 1 1]

def chairCells : List V3 := bits.filter fun x => x != v 1 1 1

def unitAxis (axis : Nat) (sgn : Int) : V3 :=
  if axis == 0 then v sgn 0 0 else if axis == 1 then v 0 sgn 0 else v 0 0 sgn

def cellLower (g : Frame) (t c : V3) : V3 :=
  let component (i : Nat) : Int :=
    let a := c.get (g.perm.get i)
    let s := g.sign.get i
    (if s == 1 then a else -a - 1) + t.get i
  v (component 0) (component 1) (component 2)

def body (p : Pose) : List V3 :=
  chairCells.map (cellLower p.frame p.shift) |>.eraseDups

def doubledChairCells : List V3 :=
  chairCells.flatMap fun x => bits.map fun b => (x.smul 2).add b

def faces (p : Pose) : List Face :=
  let cells := body p
  cells.flatMap fun x =>
    [(0, -1), (0, 1), (1, -1), (1, 1), (2, -1), (2, 1)].filterMap fun (axis, sgn) =>
      let normal := unitAxis axis sgn
      if cells.contains (x.add normal) then none
      else some {
        axis := axis
        center2 := (x.smul 2).add (v 1 1 1) |>.add normal
        outward := sgn
      }

def oppositeFaces (a b : Face) : Bool :=
  a.axis == b.axis && a.center2 == b.center2 && a.outward == -b.outward

def touch (a b : Pose) : Bool :=
  (faces a).any fun x => (faces b).any fun y => oppositeFaces x y

def bodiesOverlap (a b : Pose) : Bool :=
  (body a).any fun x => (body b).contains x

def compatible (legal : List Pose) (a b : Pose) : Bool :=
  if a == b then true
  else if bodiesOverlap a b then false
  else !touch a b || legal.contains (a.relative b)

def refine (p : Pose) : List Pose :=
  children.map fun c =>
    po (p.frame.mul c.frame) ((p.shift.smul 2).add (p.frame.act c.shift))

def internalContacts : List Pose :=
  ((allPairs children).filterMap fun (a, b) =>
    if a != b && touch a b then some (a.relative b) else none
  ).eraseDups

def closureStep (states : List Pose) : List Pose :=
  let offspring := states.flatMap fun e =>
    children.flatMap fun p =>
      (refine e).filterMap fun q =>
        if touch p q then some (p.relative q) else none
  union states offspring

def closedContacts : List Pose := closureStep internalContacts

def offsets8 : List V3 :=
  [v (-1) (-2) 0, v (-1) 2 0, v 1 (-2) 0, v 1 2 0,
   v (-2) (-1) 0, v (-2) 1 0, v 2 (-1) 0, v 2 1 0]

def tangentOffset (axis : Nat) (o : V3) : V3 :=
  if axis == 0 then v 0 o.x o.y
  else if axis == 1 then v o.x 0 o.y
  else v o.x o.y 0

def panelFeatures (panelId : Nat) (p : Panel) : List Feature :=
  (List.range 8).map fun slot =>
    let o := getD offsets8 slot (v 0 0 0)
    let coefficient := getD p.coefficients slot 0
    {
      role := 8 * panelId + slot
      center8 := (p.center2.smul 4).add (tangentOffset p.axis o)
      normal := unitAxis p.axis p.outward
      coefficient := coefficient
    }

def fallbackFeature : Feature where
  role := 0
  center8 := v 0 0 0
  normal := v 1 0 0
  coefficient := 1

def nativeFeatures : List Feature :=
  (List.range panels.length).flatMap fun i =>
    panelFeatures i (getD panels i { axis := 0, outward := 0, center2 := v 0 0 0, coefficients := [] })

/-- The native coordinate normal to a feature's panel.  This data-only
    definition is shared by the finite table checks and the geometric model. -/
def featureAxisOf (f : Feature) : Nat :=
  if f.normal.x != 0 then 0 else if f.normal.y != 0 then 1 else 2

def movedFeatures (p : Pose) (translationScale : Int) : List Feature :=
  nativeFeatures.map fun f => {
    f with
    center8 := (p.frame.act f.center8).add (p.shift.smul translationScale)
    normal := p.frame.act f.normal
  }

def sameAxis (a b : V3) : Bool :=
  ((a.x != 0) && (b.x != 0)) || ((a.y != 0) && (b.y != 0)) || ((a.z != 0) && (b.z != 0))

def coincidentPort (a b : Feature) : Bool :=
  a.center8 == b.center8 && sameAxis a.normal b.normal

def matchingProfile (profile : List Int) (p : Pose) : Bool :=
  let moved := movedFeatures p 8
  nativeFeatures.all fun a =>
    moved.all fun b =>
      if coincidentPort a b then
        getD profile a.role 0 == -getD profile b.role 0
      else true

def equationsFromContacts (states : List Pose) : List SignEquation :=
  (states.flatMap fun p =>
    let moved := movedFeatures p 8
    nativeFeatures.flatMap fun a =>
      moved.filterMap fun b =>
        if coincidentPort a b then
          let lo := min a.role b.role
          let hi := max a.role b.role
          some { left := lo, right := hi, sign := -1 }
        else none).eraseDups

def neighborShell : List V3 :=
  let candidates := chairCells.flatMap fun x =>
    [(0, -1), (0, 1), (1, -1), (1, 1), (2, -1), (2, 1)].map fun (axis, sgn) =>
      x.add (unitAxis axis sgn)
  diff candidates.eraseDups chairCells

def translationsForFrame (g : Frame) : List V3 :=
  let zeroBody := body (po g (v 0 0 0))
  (neighborShell.flatMap fun c => zeroBody.map fun b => c.sub b).eraseDups

def computedRawContacts : List Pose :=
  (allFrames.flatMap fun g =>
    (translationsForFrame g).filterMap fun t =>
      let p := po g t
      if !bodiesOverlap rootPose p && touch rootPose p then some p else none).eraseDups

def computedLegalContacts : List Pose :=
  computedRawContacts.filter (matchingProfile certificateProfile)

def relationHolds (profile : List Int) (e : SignEquation) : Bool :=
  getD profile e.left 0 == e.sign * getD profile e.right 0

def componentRoleList (c : List (Nat × Int)) : List Nat := c.map Prod.fst

def reachableStep (rows : List SignEquation) (seen : List Nat) : List Nat :=
  let next := rows.flatMap fun e =>
    if seen.contains e.left || seen.contains e.right then [e.left, e.right] else []
  union seen next

def iterateN (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateN f n (f x)

def reachable (rows : List SignEquation) (root : Nat) : List Nat :=
  iterateN (reachableStep rows) 192 [root]

def componentValid (rows : List SignEquation) (c : List (Nat × Int)) : Bool :=
  let roles := componentRoleList c
  noDuplicates roles && c.length == 16 &&
  c.all (fun (_, s) => s == 1 || s == -1) &&
  (c.foldl (fun total x => total + x.2) 0 == 0) &&
  match c with
  | [] => false
  | (root, rootSign) :: _ =>
      rootSign == 1 && roles.all (root <= ·) && setEq (reachable rows root) roles

def componentRoot (c : List (Nat × Int)) : Nat :=
  match c with
  | [] => 192
  | (root, _) :: _ => root

def strictlyIncreasing : List Nat → Bool
  | [] | [_] => true
  | x :: y :: xs => x < y && strictlyIncreasing (y :: xs)

def componentIndex (components : List (List (Nat × Int))) (role : Nat) : Nat :=
  let found := components.findIdx? fun c => (componentRoleList c).contains role
  match found with | some i => i | none => components.length

def componentSign (components : List (List (Nat × Int))) (role : Nat) : Int :=
  let pairs := components.flatten
  match pairs.find? fun x => x.1 == role with
  | some x => x.2
  | none => 0

def canonicalProfile (components : List (List (Nat × Int))) : List Int :=
  (List.range 192).map fun role =>
    Int.ofNat (componentIndex components role + 1) * componentSign components role

def componentsDescribeGraph (rows : List SignEquation) (components : List (List (Nat × Int))) : Bool :=
  let roles := components.flatMap componentRoleList
  components.length == 12 && setEq roles (List.range 192) && noDuplicates roles &&
  components.all (componentValid rows) && strictlyIncreasing (components.map componentRoot) &&
  rows.all fun e =>
    componentIndex components e.left == componentIndex components e.right &&
    componentSign components e.left == e.sign * componentSign components e.right

/- First-shell covers and parent recognition. -/

def poseAt (i : Nat) : Pose := getD legalContacts i rootPose
def coverAt (i : Nat) : List V3 := inter (body (poseAt i)) shellCells

def badIndices (i : Nat) : List Nat :=
  (List.range legalContacts.length).filter fun j =>
    j == i || !compatible legalContacts (poseAt i) (poseAt j)

def computedWholeBodyConflicts : List Nat :=
  (List.range legalContacts.length).map fun i =>
    (badIndices i).foldl (fun mask j => mask + 2 ^ j) 0

def candidatesForCell (available : List Nat) (cell : V3) : List Nat :=
  available.filter fun i => (coverAt i).contains cell

def betterCell (available : List Nat) (a b : V3) : V3 :=
  if (candidatesForCell available a).length <= (candidatesForCell available b).length then a else b

def chooseConstrainedCell (available : List Nat) (todo : List V3) : V3 :=
  match todo with
  | [] => v 0 0 0
  | x :: xs => xs.foldl (betterCell available) x

def enumerateShells : Nat → List V3 → List Nat → List Nat → List (List Nat)
  | 0, _, _, _ => []
  | _ + 1, [], _, chosen => [chosen.reverse]
  | fuel + 1, todo, available, chosen =>
      let x := chooseConstrainedCell available todo
      (candidatesForCell available x).flatMap fun i =>
        enumerateShells fuel (diff todo (coverAt i)) (diff available (badIndices i)) (i :: chosen)

def computedShells : List (List Nat) :=
  enumerateShells 23 shellCells (List.range legalContacts.length) [] |>.eraseDups

def parentThroughRoot (child : Pose) : List Pose :=
  let undo := child.inverse
  children.map (undo.transform ·)

def computedParents : List (List Pose) := children.map parentThroughRoot

def neededSignature (parent : List Pose) : List Nat :=
  (List.range legalContacts.length).filter fun i => parent.contains (poseAt i)

def computedRoleOptions : List (List Nat) :=
  shellSolutions.map fun solution =>
    (List.range computedParents.length).filter fun role =>
      subset (neededSignature (getD computedParents role [])) solution

def computedRoles : List Nat := computedRoleOptions.map fun xs => getD xs 0 99

def parentsConflict (a b : List Pose) : Bool :=
  unorderedPairs (union a b) |>.any fun (p, q) => !compatible legalContacts p q

def computedParentConflictCount : Nat :=
  (unorderedPairs computedParents |>.filter fun (a, b) => parentsConflict a b).length

def shellPoseSet (solution : List Nat) : List Pose := solution.map poseAt

def centralViable (shellId role : Nat) : List Nat :=
  let center := (getD children role rootPose).inverse.transform (getD children 7 rootPose)
  let existing := rootPose :: shellPoseSet (getD shellSolutions shellId [])
  let required := existing.filterMap fun p =>
    if p != center && touch center p then some (center.relative p) else none
  (List.range shellSolutions.length).filter fun j =>
    let neighbors := shellPoseSet (getD shellSolutions j [])
    let world := neighbors.map (center.transform ·)
    subset required neighbors &&
    world.all fun p => existing.all fun q => compatible legalContacts p q

def computedCentralCases : List (Nat × List Nat) :=
  (List.range shellSolutions.length).filterMap fun sid =>
    let role := getD computedRoles sid 99
    if role == 7 then none else some (sid, centralViable sid role)

def centralPassedComputed : List Nat :=
  computedCentralCases.filterMap fun (sid, viable) => if viable.isEmpty then none else some sid

def centralDeadComputed : List Nat :=
  computedCentralCases.filterMap fun (sid, viable) => if viable.isEmpty then some sid else none

def mistypedCentralCount : Nat :=
  computedCentralCases.foldl (fun total (_, viable) =>
    total + (viable.filter fun j => getD computedRoles j 99 != 7).length) 0

/- Parent atlas at scale two. -/

def macroChildren (p : Pose) : List Pose := children.map (p.transform ·)
def rootMacroBody : List V3 := unions (children.map body)

def computedMacroCandidates : List Pose :=
  let xs := children.flatMap fun p =>
    legalContacts.flatMap fun e =>
      let q := p.transform e
      children.map fun h =>
        let g := q.frame.mul h.frame.transpose
        po g (q.shift.sub (g.act h.shift))
  diff xs.eraseDups [rootPose]

def macroBody (p : Pose) : List V3 := unions ((macroChildren p).map body)

def macroNonoverlap : List Pose :=
  computedMacroCandidates.filter fun p => (inter rootMacroBody (macroBody p)).isEmpty

def crossContacts (p : Pose) : List Pose :=
  let other := macroChildren p
  (children.flatMap fun a =>
    other.filterMap fun b => if touch a b then some (a.relative b) else none
  ).eraseDups

def computedMacroLegal : List Pose :=
  macroNonoverlap.filter fun p =>
    let cross := crossContacts p
    !cross.isEmpty && subset cross legalContacts

def evenPose (p : Pose) : Bool :=
  p.shift.x % 2 == 0 && p.shift.y % 2 == 0 && p.shift.z % 2 == 0

def halvePose (p : Pose) : Pose :=
  po p.frame (v (p.shift.x / 2) (p.shift.y / 2) (p.shift.z / 2))

/- Eighth-grid complete-feature mates and retained-core witnesses. -/

def generatedMatePairs : List (Pose × Nat) :=
  hashDedup (allFrames.flatMap fun g =>
    nativeFeatures.flatMap fun a =>
      nativeFeatures.filterMap fun b =>
        if g.act b.normal == a.normal.neg && b.coefficient == -a.coefficient then
          some (po g (a.center8.sub (g.act b.center8)), a.role)
        else none)

def literalMatePairs : List (Pose × Nat) :=
  mateRecords.flatMap fun r => r.roles.map fun role => (r.pose, role)

def boxes8 (p : Pose) : List V3 :=
  (body (po p.frame (v 0 0 0))).map fun x => (x.smul 8).add p.shift

def intervalsOverlap (a b : Int) : Bool := a < b + 8 && b < a + 8

def boxesOverlap (a b : V3) : Bool :=
  intervalsOverlap a.x b.x && intervalsOverlap a.y b.y && intervalsOverlap a.z b.z

def baselineOverlap8 (a b : Pose) : Bool :=
  (boxes8 a).any fun x => (boxes8 b).any fun y => boxesOverlap x y

def rootEighth : Pose := po identityFrame (v 0 0 0)

def isolatedMates : List Pose :=
  matePoses.filter fun p => !baselineOverlap8 rootEighth p

def isolatedMateSet : Std.HashSet Pose := Std.HashSet.ofList isolatedMates

def partnerTable : List (List Pose) :=
  (List.range 192).map fun role =>
    mateRecords.filterMap fun r =>
      if isolatedMateSet.contains r.pose && r.roles.contains role then some r.pose else none

def partnerOptions (role : Nat) : List Pose := getD partnerTable role []

def normalizedOther (w : RejectionWitness) : Pose :=
  if w.owner == 0 then w.rejected else w.rejected.inverse

def maxInt (a b : Int) : Int := if a < b then b else a
def minInt (a b : Int) : Int := if a < b then a else b

def overlapBox (a b : V3) : Option Box :=
  let lo := v (maxInt a.x b.x) (maxInt a.y b.y) (maxInt a.z b.z)
  let hi := v (minInt (a.x + 8) (b.x + 8))
              (minInt (a.y + 8) (b.y + 8))
              (minInt (a.z + 8) (b.z + 8))
  if lo.x < hi.x && lo.y < hi.y && lo.z < hi.z then some ⟨lo, hi⟩ else none

def firstOverlapBox (a b : Pose) : Option Box :=
  let candidates := (boxes8 a).flatMap fun x =>
    (boxes8 b).filterMap fun y => overlapBox x y
  candidates.head?

def coreSide400 (lo hi : Int) : Int := 50 * (hi - lo) - 8

def retainedCoreBox (box : Box) : Bool :=
  coreSide400 box.lo.x box.hi.x >= 42 &&
  coreSide400 box.lo.y box.hi.y >= 42 &&
  coreSide400 box.lo.z box.hi.z >= 42

def collisionOptionValid (other option : Pose) : Bool :=
  match firstOverlapBox other option with
  | none => false
  | some box => retainedCoreBox box

def rejectionValid (w : RejectionWitness) : Bool :=
  let p := normalizedOther w
  let options := partnerOptions w.role
  (w.owner == 0 || w.owner == 1) && w.role < 192 &&
  isolatedMates.contains p && !options.isEmpty && options.length == w.optionCount &&
  !options.contains p && options.all (collisionOptionValid p)

def fineAtlas8 : List Pose :=
  legalContacts.map fun p => po p.frame (p.shift.smul 8)

def rejectedPoses : List Pose := rejectionWitnesses.map RejectionWitness.rejected

/- Signed coordinate permutations acting on the native feature table. -/

def positivePermutationFrame (p : N3) : Frame := fr p.x p.y p.z 1 1 1

def preservesFeatureTable (p : N3) : Bool :=
  let moved := movedFeatures (po (positivePermutationFrame p) (v 0 0 0)) 8
  nativeFeatures.all fun a =>
    match moved.find? fun b => coincidentPort a b with
    | none => false
    | some b => a.coefficient == b.coefficient

def sameFeatureDatum (a b : Feature) : Bool :=
  a.center8 == b.center8 && a.normal == b.normal && a.coefficient == b.coefficient

def featureTablesEqual (a b : List Feature) : Bool :=
  a.all (fun x => b.any (sameFeatureDatum x)) &&
  b.all (fun x => a.any (sameFeatureDatum x))

def preservesFeatureTableFrame (g : Frame) : Bool :=
  featureTablesEqual nativeFeatures (movedFeatures (po g (v 0 0 0)) 8)

/- The Boolean propositions evaluated by the named theorems.  Each conjunct is
   intentionally visible here so the statements are auditable without opening
   generated data. -/

def childrenPartitionCheck : Bool :=
  children == solidChildren && children.length == 8 &&
  children.all (properFrame ·.frame) &&
  (children.map body).all (fun cells => cells.length == 7) &&
  (children.flatMap body).length == 56 &&
  noDuplicates (children.flatMap body) &&
  setEq (children.flatMap body) doubledChairCells

def contactClosureCheck : Bool :=
  internalContacts.length == 21 && closedContacts.length == 30 &&
  setEq closedContacts contactStates && setEq (closureStep closedContacts) closedContacts &&
  closureCounts == [21, 30]

def profileCanonicalCheckWith (profile : List Int) : Bool :=
  let derivedRows := equationsFromContacts closedContacts
  setEq derivedRows signedRows && derivedRows.length == 372 &&
  signedRows.length == 372 && noDuplicates signedRows &&
  componentsDescribeGraph signedRows balancedComponents &&
  canonicalProfile balancedComponents == profile &&
  profile == panelProfile && profile == solidProfile

def profileCanonicalCheck : Bool := profileCanonicalCheckWith certificateProfile

def atlasCheck : Bool :=
  setEq neighborShell shellCells && shellCells.length == 22 &&
  setEq computedRawContacts rawContacts && computedRawContacts.length == 2388 &&
  setEq computedLegalContacts legalContacts && computedLegalContacts.length == 44 &&
  subset closedContacts computedLegalContacts && computedLegalContacts.all (properFrame ·.frame)

def parentLiteralsAgree : Bool :=
  (List.range computedParents.length).all fun i =>
    setEq (getD computedParents i []) (getD parents i [])

def firstShellsCheck : Bool :=
  setFamilyEq computedShells shellSolutions && computedShells.length == 33 &&
  computedWholeBodyConflicts == wholeBodyConflicts &&
  parentLiteralsAgree && computedRoleOptions == roleOptions &&
  computedRoleOptions.all (fun x => x.length == 1) &&
  (computedRoles.filter fun x => x == 7).length == 1

def expectedCentralCases : List (Nat × List Nat) :=
  centralCompletion.map fun r => (r.shellId, r.viable)

def centralCompletionCheck : Bool :=
  computedCentralCases == expectedCentralCases &&
  centralPassedComputed == centralPassed && centralDeadComputed == centralDead &&
  centralPassedComputed.length == 14 && centralDeadComputed.length == 18 &&
  mistypedCentralCount == 0 && centralWrong.isEmpty

def parentConflictsCheck : Bool :=
  computedParents.length == 8 && (unorderedPairs computedParents).length == 28 &&
  computedParentConflictCount == 28

def parentAtlasCheck : Bool :=
  setEq computedMacroCandidates macroCandidates && computedMacroCandidates.length == 697 &&
  macroNonoverlap.length == Generated.macroNonoverlap &&
  setEq computedMacroLegal macroLegal && computedMacroLegal.length == 44 &&
  computedMacroLegal.all evenPose &&
  setEq (computedMacroLegal.map halvePose) legalContacts

def mateLiteralCheck : Bool :=
  matePoses.length == 6862 && hashNoDuplicates matePoses &&
  mateRecords.length == 6862 && mateRecords.map MateRecord.pose == matePoses &&
  hashSetEq generatedMatePairs literalMatePairs

def witnessRejectedSetWith (witnesses : List RejectionWitness) : List Pose :=
  witnesses.map RejectionWitness.rejected

def witnessRejectedSet : List Pose := witnessRejectedSetWith rejectionWitnesses

def matesCensusCheckWith (witnesses : List RejectionWitness) : Bool :=
  let rejected := witnessRejectedSetWith witnesses
  mateLiteralCheck && isolatedMates.length == 5317 &&
  (isolatedMates.filter fun p => p.shift.x % 8 != 0 || p.shift.y % 8 != 0 || p.shift.z % 8 != 0).length == 5234 &&
  witnesses.length == 5273 && hashNoDuplicates rejected &&
  hashSetEq rejected (hashDiff isolatedMates fineAtlas8) &&
  hashSetEq (hashDiff isolatedMates rejected) fineAtlas8 &&
  fineAtlas8.length == 44 && fineAtlas8.all (properFrame ·.frame) &&
  witnesses.all rejectionValid &&
  (witnesses.foldl (fun total w => total + w.optionCount) 0 == 299975)

def matesCensusCheck : Bool := matesCensusCheckWith rejectionWitnesses

def deviationsDistinctCheck : Bool :=
  let indices := (List.range 12).map (fun i => i + 1)
  (allPairs indices).all fun (i, j) =>
    10000 * i^2 != 20000 * j^2 + j^4

def lipschitzBoundsCheck : Bool :=
  8 * 3^2 < 25^2 && 63 * 3^2 < 25^2

def noNativeSymmetryCheck : Bool :=
  let preservingCoordinates := coordinatePermutations.filter preservesFeatureTable
  let preservingFrames := allFrames.filter preservesFeatureTableFrame
  allFrames.length == 48 && noDuplicates allFrames &&
  preservingCoordinates == [n3 0 1 2] && preservingCoordinates == nativeSymmetries &&
  preservingFrames == [identityFrame]

/- Remaining finite receipts in verify/replay.py: the explicit surface mesh,
   finite substitution controls, and the generated proper rotation group. -/

def v3Less (a b : V3) : Bool :=
  a.x < b.x || (a.x == b.x &&
    (a.y < b.y || (a.y == b.y && a.z < b.z)))

def triangleKey (a b c : V3) : V3 × V3 × V3 :=
  if v3Less b a && v3Less b c then (b, c, a)
  else if v3Less c a && v3Less c b then (c, a, b)
  else (a, b, c)

def meshPoint (i : Nat) : V3 := getD solidVertices10000 i (v 0 0 0)

def actualMeshTriangles : List (V3 × V3 × V3) :=
  solidTriangles.map fun t => triangleKey (meshPoint t.x) (meshPoint t.y) (meshPoint t.z)

def directedMeshEdges : List (Nat × Nat) :=
  solidTriangles.flatMap fun t => [(t.x, t.y), (t.y, t.z), (t.z, t.x)]

def reverseEdges (edges : List (Nat × Nat)) : List (Nat × Nat) :=
  edges.map fun e => (e.2, e.1)

/-! The boundary-sphere audit is separate from `solidMeshCheck`: it checks the
four combinatorial surface obligations directly on the generated indexed
triangle list. -/

def orderedIndexEdge (a b : Nat) : Nat × Nat :=
  if a < b then (a, b) else (b, a)

def triangleIndexEdges (t : N3) : List (Nat × Nat) :=
  [orderedIndexEdge t.x t.y, orderedIndexEdge t.y t.z, orderedIndexEdge t.z t.x]

def edgeTriangleIncidences : Std.HashMap (Nat × Nat) (List Nat) :=
  (List.range solidTriangles.length).foldl (fun incidences face =>
    let triangle := getD solidTriangles face (n3 0 0 0)
    (triangleIndexEdges triangle).foldl (fun current e =>
      current.insert e (face :: (current[e]?).getD [])) incidences)
    Std.HashMap.emptyWithCapacity

def meshUndirectedEdges : List (Nat × Nat) :=
  edgeTriangleIncidences.toList.map Prod.fst

def boundaryEdgeIncidenceCheck : Bool :=
  edgeTriangleIncidences.toList.all fun incidence => incidence.2.length == 2

def triangleNeighborMap : Std.HashMap Nat (List Nat) :=
  edgeTriangleIncidences.toList.foldl (fun neighbors incidence =>
    (unorderedPairs incidence.2).foldl (fun current pair =>
      let withFirst := current.insert pair.1 (pair.2 :: (current[pair.1]?).getD [])
      withFirst.insert pair.2 (pair.1 :: (withFirst[pair.2]?).getD [])) neighbors)
    Std.HashMap.emptyWithCapacity

def reachableTriangles : Std.HashSet Nat :=
  let rec loop : Nat → List Nat → Std.HashSet Nat → Std.HashSet Nat
    | 0, _, seen => seen
    | _ + 1, [], seen => seen
    | fuel + 1, current :: queue, seen =>
        let fresh := ((triangleNeighborMap[current]?).getD []).filter fun candidate =>
          !seen.contains candidate
        let seen' := fresh.foldl (fun s candidate => s.insert candidate) seen
        loop fuel (queue ++ fresh) seen'
  if solidTriangles.isEmpty then Std.HashSet.emptyWithCapacity
  else loop solidTriangles.length [0] ((Std.HashSet.emptyWithCapacity).insert 0)

def triangleAdjacencyConnectedCheck : Bool :=
  !solidTriangles.isEmpty && reachableTriangles.size == solidTriangles.length

def vertexLinkEdgeMap : Std.HashMap Nat (List (Nat × Nat)) :=
  solidTriangles.foldl (fun links t =>
    let atX := links.insert t.x (orderedIndexEdge t.y t.z :: (links[t.x]?).getD [])
    let atY := atX.insert t.y (orderedIndexEdge t.z t.x :: (atX[t.y]?).getD [])
    atY.insert t.z (orderedIndexEdge t.x t.y :: (atY[t.z]?).getD []))
    Std.HashMap.emptyWithCapacity

def vertexLinkEdges (vertex : Nat) : List (Nat × Nat) :=
  (vertexLinkEdgeMap[vertex]?).getD []

def linkVertices (links : List (Nat × Nat)) : List Nat :=
  hashDedup (links.flatMap fun e => [e.1, e.2])

def linkVertexDegree (links : List (Nat × Nat)) (vertex : Nat) : Nat :=
  (links.filter fun e => e.1 == vertex || e.2 == vertex).length

def reachableLinkVertices (links : List (Nat × Nat)) (start : Nat) : Std.HashSet Nat :=
  let rec loop : Nat → List Nat → Std.HashSet Nat → Std.HashSet Nat
    | 0, _, seen => seen
    | _ + 1, [], seen => seen
    | fuel + 1, current :: queue, seen =>
        let neighbors := links.filterMap fun e =>
          if e.1 == current then some e.2 else if e.2 == current then some e.1 else none
        let fresh := hashDedup neighbors |>.filter fun candidate => !seen.contains candidate
        let seen' := fresh.foldl (fun s candidate => s.insert candidate) seen
        loop fuel (queue ++ fresh) seen'
  loop links.length [start] ((Std.HashSet.emptyWithCapacity).insert start)

def vertexLinkSingleCycle (vertex : Nat) : Bool :=
  let links := vertexLinkEdges vertex
  let vertices := linkVertices links
  !links.isEmpty && hashNoDuplicates links && vertices.length >= 3 &&
    links.all (fun e => e.1 != e.2) &&
    vertices.all (fun vtx => linkVertexDegree links vtx == 2) &&
    match vertices with
    | [] => false
    | start :: _ => (reachableLinkVertices links start).size == vertices.length

def vertexLinksSingleCyclesCheck : Bool :=
  (List.range solidVertices10000.length).all vertexLinkSingleCycle

def adjacentPairs : List α → List (α × α)
  | a :: b :: xs => (a, b) :: adjacentPairs (b :: xs)
  | _ => []

def panelCuts10000 : List Int :=
  [-5000, -2600, -2400, -1350, -1150, 1150, 1350, 2400, 2600, 5000]

def panelPoint10000 (p : Panel) (a b : Int) : V3 :=
  let center := p.center2.smul 5000
  center.add (tangentOffset p.axis (v a b 0))

def slotAtRectangle (x0 x1 y0 y1 : Int) : Option Nat :=
  (List.range 8).find? fun slot =>
    let o := getD offsets8 slot (v 0 0 0)
    x0 == o.x * 1250 - 100 && x1 == o.x * 1250 + 100 &&
    y0 == o.y * 1250 - 100 && y1 == o.y * 1250 + 100

def orientPanelCorners (p : Panel) (q : List V3) : List V3 :=
  let nativeSign : Int := if p.axis % 2 == 0 then 1 else -1
  if nativeSign == p.outward then q else q.reverse

def expectedRectangleTriangles (panelId : Nat) (p : Panel)
    (x0 x1 y0 y1 : Int) : List (V3 × V3 × V3) :=
  let q := orientPanelCorners p
    [panelPoint10000 p x0 y0, panelPoint10000 p x1 y0,
     panelPoint10000 p x1 y1, panelPoint10000 p x0 y1]
  let q0 := getD q 0 (v 0 0 0)
  let q1 := getD q 1 (v 0 0 0)
  let q2 := getD q 2 (v 0 0 0)
  let q3 := getD q 3 (v 0 0 0)
  match slotAtRectangle x0 x1 y0 y1 with
  | none => [triangleKey q0 q1 q2, triangleKey q0 q2 q3]
  | some slot =>
      let role := 8 * panelId + slot
      let fallback : Feature := {
        role := 0
        center8 := v 0 0 0
        normal := v 0 0 0
        coefficient := 0
      }
      let f := getD nativeFeatures role fallback
      let apex := (f.center8.smul 1250).add (f.normal.smul f.coefficient)
      [triangleKey q0 q1 apex, triangleKey q1 q2 apex,
       triangleKey q2 q3 apex, triangleKey q3 q0 apex]

def expectedPanelTriangles (panelId : Nat) (p : Panel) : List (V3 × V3 × V3) :=
  (adjacentPairs panelCuts10000).flatMap fun (x0, x1) =>
    (adjacentPairs panelCuts10000).flatMap fun (y0, y1) =>
      expectedRectangleTriangles panelId p x0 x1 y0 y1

def expectedMeshTriangles : List (V3 × V3 × V3) :=
  (List.range panels.length).flatMap fun panelId =>
    expectedPanelTriangles panelId
      (getD panels panelId { axis := 0, outward := 0, center2 := v 0 0 0, coefficients := [] })

def det3 (a b c : V3) : Int :=
  a.x * (b.y * c.z - b.z * c.y) -
  a.y * (b.x * c.z - b.z * c.x) +
  a.z * (b.x * c.y - b.y * c.x)

def meshVolumeNumerator : Int :=
  solidTriangles.foldl (fun total t =>
    total + det3 (meshPoint t.x) (meshPoint t.y) (meshPoint t.z)) 0

def reachableVertices : Std.HashSet Nat :=
  let rec loop : Nat → List Nat → Std.HashSet Nat → Std.HashSet Nat
    | 0, _, seen => seen
    | _ + 1, [], seen => seen
    | fuel + 1, x :: queue, seen =>
        let neighbors := directedMeshEdges.filterMap fun e =>
          if e.1 == x && !seen.contains e.2 then some e.2 else none
        let fresh := hashDedup neighbors
        let seen' := fresh.foldl (fun s y => s.insert y) seen
        loop fuel (queue ++ fresh) seen'
  loop solidVertexCount [0] ((Std.HashSet.emptyWithCapacity).insert 0)

def solidMeshCheck : Bool :=
  solidVertices10000.length == solidVertexCount && solidVertexCount == 2138 &&
  solidTriangles.length == solidTriangleCount && solidTriangleCount == 4272 &&
  solidTriangles.all (fun t =>
    t.x < solidVertexCount && t.y < solidVertexCount && t.z < solidVertexCount &&
    t.x != t.y && t.y != t.z && t.z != t.x) &&
  hashNoDuplicates directedMeshEdges && hashSetEq directedMeshEdges (reverseEdges directedMeshEdges) &&
  directedMeshEdges.length / 2 == solidEdgeCount && solidEdgeCount == 6408 &&
  solidVertexCount + solidTriangleCount == solidEdgeCount + 2 &&
  reachableVertices.size == solidVertexCount &&
  hashNoDuplicates actualMeshTriangles && hashNoDuplicates expectedMeshTriangles &&
  hashSetEq actualMeshTriangles expectedMeshTriangles &&
  meshVolumeNumerator == 42 * 10000^3 && solidExactVolume == "7"

def V3.dot (a b : V3) : Int := a.x * b.x + a.y * b.y + a.z * b.z

def V3.cross (a b : V3) : V3 :=
  v (a.y * b.z - a.z * b.y)
    (a.z * b.x - a.x * b.z)
    (a.x * b.y - a.y * b.x)

def triangleNormal (a b c : V3) : V3 := (b.sub a).cross (c.sub a)

def orderedEdge (a b : V3) : V3 × V3 := if v3Less b a then (b, a) else (a, b)

def triangleEdgeGeometry (a b c : V3) : List EdgeGeometry :=
  let normal := triangleNormal a b c
  let make (x y opposite : V3) :=
    let key := orderedEdge x y
    { a := key.1, b := key.2, normal := normal, opposite := opposite }
  [make a b c, make b c a, make c a b]

def meshEdgeGeometry : List EdgeGeometry :=
  solidTriangles.flatMap fun t =>
    triangleEdgeGeometry (meshPoint t.x) (meshPoint t.y) (meshPoint t.z)

def meshGeometricEdgeKeys : List (V3 × V3) :=
  hashDedup (meshEdgeGeometry.map fun e => (e.a, e.b))

def nonzeroCoordinates (a : V3) : Nat :=
  (if a.x == 0 then 0 else 1) + (if a.y == 0 then 0 else 1) +
  (if a.z == 0 then 0 else 1)

def normSquared (a : V3) : Int := a.dot a

def signOf (x : Int) : Int := if x < 0 then -1 else if x == 0 then 0 else 1

def squaredLength (a b : V3) : Int := normSquared (b.sub a)

def featureAngleHeight (kind : Nat) (n m : V3) : Option Nat :=
  let d2 := (n.dot m)^2
  let nm := normSquared n * normSquared m
  ((List.range 12).map fun i => i + 1).find? fun j =>
    let jz := Int.ofNat j
    if kind == 0 then d2 * (10000 + jz^2) == nm * 10000
    else d2 * (10000 + jz^2)^2 == nm * 100000000

def classifyMeshEdge (key : V3 × V3) : Option (Nat × Nat × Int) :=
  let records := meshEdgeGeometry.filter fun e => e.a == key.1 && e.b == key.2
  if records.length != 2 then none else
  let fallback : EdgeGeometry := {
    a := v 0 0 0
    b := v 0 0 0
    normal := v 0 0 0
    opposite := v 0 0 0
  }
  let x := getD records 0 fallback
  let y := getD records 1 fallback
  let n := x.normal
  let m := y.normal
  let side := signOf (n.dot (y.opposite.sub key.1))
  let axisCount := (if nonzeroCoordinates n == 1 then 1 else 0) +
    (if nonzeroCoordinates m == 1 then 1 else 0)
  if axisCount == 1 then
    match featureAngleHeight 0 n m with
    | some j =>
        if n.dot m > 0 && squaredLength key.1 key.2 == 40000 then some (0, j, side) else none
    | none => none
  else if axisCount == 0 then
    match featureAngleHeight 1 n m with
    | some j =>
        if n.dot m > 0 && squaredLength key.1 key.2 == 20000 + (Int.ofNat j)^2
        then some (1, j, side) else none
    | none => none
  else if (n.dot m)^2 == normSquared n * normSquared m then
    if n.dot m > 0 && side == 0 then some (2, 0, 0) else none
  else if n.dot m == 0 && (side == -1 || side == 1) then some (3, 0, side)
  else none

def meshAngleClasses : List (Nat × Nat × Int) :=
  meshGeometricEdgeKeys.filterMap classifyMeshEdge

def meshAngleAuditCheck : Bool :=
  meshGeometricEdgeKeys.length == 6408 && meshAngleClasses.length == 6408 &&
  (meshAngleClasses.filter fun k => k.1 == 0 || k.1 == 1).length == 1536 &&
  ((List.range 12).map fun i => i + 1).all fun j =>
    [0, 1].all fun kind =>
      [-1, 1].all fun side =>
        (meshAngleClasses.filter fun k => k.1 == kind && k.2.1 == j && k.2.2 == side).length == 32

def twoRefinements (poses : List Pose) : List Pose :=
  hashDedup (poses.flatMap refine |>.flatMap refine)

def translatedPatch (amount : Int) (poses : List Pose) : List Pose :=
  poses.map fun p => po p.frame (p.shift.sub (v amount amount amount))

def nestedPatchOne : List Pose := translatedPatch 2 (twoRefinements [rootPose])
def nestedPatchTwo : List Pose := translatedPatch 10 (twoRefinements (twoRefinements [rootPose]))

def nestedPatchControlsCheck : Bool :=
  (twoRefinements [rootPose]).contains (po identityFrame (v 2 2 2)) &&
  nestedPatchOne.length == 64 && nestedPatchTwo.length == 4096 &&
  hashSetEq [rootPose] (inter nestedPatchOne [rootPose]) &&
  subset nestedPatchOne nestedPatchTwo &&
  hashNoDuplicates (nestedPatchOne.flatMap body) &&
  (nestedPatchOne.flatMap body).length == 448 &&
  hashNoDuplicates (nestedPatchTwo.flatMap body) &&
  (nestedPatchTwo.flatMap body).length == 28672

/-! Finite controls used by the all-level R§9 support induction.  A signed
permutation acts on lower corners by `cellLower`, including the `-1`
correction on a reversed coordinate. -/

def twoRefinementCells (p : Pose) : List V3 :=
  (refine p).flatMap fun q => (refine q).flatMap body

def fourBlockOffsets : List V3 :=
  bits.flatMap fun b₀ => bits.map fun b₁ => (b₀.smul 2).add b₁

def fourBlockCells : List V3 :=
  chairCells.flatMap fun a =>
    fourBlockOffsets.map fun b => (a.smul 4).add b

def hierarchyBlockCoverCheck : Bool :=
  subset fourBlockCells (twoRefinementCells rootPose)

def blockOffsetActionCheck : Bool :=
  allFrames.all fun g => fourBlockOffsets.all fun b =>
    fourBlockOffsets.any fun c =>
      cellLower g (v 0 0 0) c ==
        ((cellLower g (v 0 0 0) (v 0 0 0)).smul 4 |>.add b)

def hierarchyCellControlsCheck : Bool :=
  hierarchyBlockCoverCheck && blockOffsetActionCheck

/-! Finite panel facts used to pass from a complete feature mate to ownership
of the unit cell immediately beyond the corresponding exposed root panel. -/

def featureFarCell (f : Feature) : V3 :=
  v (f.center8.x / 8 - if f.normal.x == -1 then 1 else 0)
    (f.center8.y / 8 - if f.normal.y == -1 then 1 else 0)
    (f.center8.z / 8 - if f.normal.z == -1 then 1 else 0)

def roleFarCells : List V3 :=
  (List.range 192).map fun r => featureFarCell (getD nativeFeatures r fallbackFeature)

def legalMateOwnsFarCellCheck : Bool :=
  legalContacts.all fun p => nativeFeatures.all fun a => nativeFeatures.all fun b =>
    let movedCenter := (p.frame.act b.center8).add (p.shift.smul 8)
    let movedNormal := p.frame.act b.normal
    if movedCenter == a.center8 && movedNormal == a.normal.neg &&
        b.coefficient == -a.coefficient then
      (body p).contains (featureFarCell a)
    else true

/-- For two literal legal neighbours which touch by a lattice face, the
    second body owns a far-side feature cell in coordinates rooted at the
    first.  This is the finite panel-table input for pairwise shell legality. -/
def touchingLegalOwnsFarCellCheck : Bool :=
  legalContacts.all fun p => legalContacts.all fun q =>
    if touch p q then
      nativeFeatures.any fun a =>
        (body (p.relative q)).contains (featureFarCell a)
    else true

def registeredShellCellControlsCheck : Bool :=
  legalContacts.length == 44 && noDuplicates legalContacts &&
    setEq roleFarCells shellCells &&
    legalContacts.all (fun p => !(inter (body p) shellCells).isEmpty) &&
    legalContacts.all (fun p => allFrames.contains p.frame) &&
    legalMateOwnsFarCellCheck && touchingLegalOwnsFarCellCheck

def contactGenerators : List Frame := hashDedup (legalContacts.map Pose.frame)

def rotationClosureStep (group : List Frame) : List Frame :=
  hashDedup (group ++ group.flatMap fun g => contactGenerators.map (g.mul ·))

def computedRotationGroup : List Frame :=
  iterateN rotationClosureStep 24 [identityFrame]

def orientationGroupCheck : Bool :=
  contactGenerators.length == 19 && computedRotationGroup.length == 24 &&
  computedRotationGroup.all properFrame && hashSetEq computedRotationGroup orientationGroup

/-! ## The 168-label lattice substitution

The label of a lattice cell is its registered proper frame together with its
one of seven local chair cells.  The map below is derived from the generated
24-frame group and the generated eight child poses: for a source label and a
binary address, it locates the unique transformed child chair containing the
corresponding doubled lattice cell.  No substitution table is stored.
-/

structure SubstitutionLabel where
  frame : Frame
  cell : V3
deriving BEq, DecidableEq, Hashable, Repr

def substitutionLabels : List SubstitutionLabel :=
  orientationGroup.flatMap fun frame =>
    chairCells.map fun cell => { frame := frame, cell := cell }

def substitutionLabelAt (frameIndex cellIndex : Nat) : SubstitutionLabel :=
  { frame := getD orientationGroup frameIndex identityFrame
    cell := getD chairCells cellIndex (v 0 0 0) }

def substitutionChildPoses (frame : Frame) : List Pose :=
  children.map fun child =>
    po (frame.mul child.frame) (frame.act child.shift)

def substitutionSourceCell (label : SubstitutionLabel) : V3 :=
  cellLower label.frame (v 0 0 0) label.cell

def substitutionTargetCell (label : SubstitutionLabel) (address : V3) : V3 :=
  (substitutionSourceCell label).smul 2 |>.add address

/-- All child labels whose cells occupy the requested doubled-cell address.
The totality check below proves that this list is always a singleton. -/
def substitutionTargetLabels (label : SubstitutionLabel) (address : V3) :
    List SubstitutionLabel :=
  (substitutionChildPoses label.frame).flatMap fun child =>
    chairCells.filterMap fun cell =>
      if cellLower child.frame child.shift cell ==
          substitutionTargetCell label address then
        some { frame := child.frame, cell := cell }
      else none

def rawSubstitutionMap (label : SubstitutionLabel) (address : V3) :
    Option SubstitutionLabel :=
  match substitutionTargetLabels label address with
  | [target] => some target
  | _ => none

/-- The derived transition table, stored only as computed label indices.  Its
168 columns are in `substitutionLabels` order and its eight entries are in
`bits` order. -/
def substitutionIndexColumns : List (List Nat) :=
  substitutionLabels.map fun label => bits.filterMap fun address =>
    (rawSubstitutionMap label address).map substitutionLabels.idxOf

def substitutionMap (label : SubstitutionLabel) (address : V3) :
    Option SubstitutionLabel :=
  let column := getD substitutionIndexColumns
    (substitutionLabels.idxOf label) []
  substitutionLabels[(getD column (bits.idxOf address)
    substitutionLabels.length)]?

/-- In one registered frame the eight generated children cover exactly once
the 56 cells obtained by doubling all seven source cells at all eight binary
addresses. -/
def substitutionFrameCoverCheck (frame : Frame) : Bool :=
  let childCells := (substitutionChildPoses frame).flatMap body
  let doubledCells := chairCells.flatMap fun cell =>
    bits.map fun address =>
      (cellLower frame (v 0 0 0) cell).smul 2 |>.add address
  childCells.length == 56 && doubledCells.length == 56 &&
    noDuplicates childCells && noDuplicates doubledCells &&
    setEq childCells doubledCells

/-- Cell-level rereading of `children_partition_2P`, simultaneously for all
24 registered frames and all 168×8 label/address inputs. -/
def substitutionTotalWellDefinedCheck : Bool :=
  let columns := substitutionIndexColumns
  orientationGroup.length == 24 && noDuplicates orientationGroup &&
    chairCells.length == 7 && noDuplicates chairCells &&
    substitutionLabels.length == 168 && noDuplicates substitutionLabels &&
    orientationGroup.all substitutionFrameCoverCheck &&
    columns.length == 168 &&
    (columns.all fun column =>
      column.length == 8 && column.all fun index => index < 168) &&
    substitutionLabels.all fun label => bits.all fun address =>
      match substitutionTargetLabels label address with
      | [target] => substitutionLabels.contains target
      | _ => false

/-- `S i j` is the number of binary addresses taking source label `j` to
target label `i`. -/
def substitutionMatrixEntry (i j : SubstitutionLabel) : Nat :=
  let column := getD substitutionIndexColumns (substitutionLabels.idxOf j) []
  (column.filter fun index => index == substitutionLabels.idxOf i).length

def substitutionMatrix : List (List Nat) :=
  let columns := substitutionIndexColumns
  (List.range 168).map fun i =>
    columns.map fun column => (column.filter fun index => index == i).length

def substitutionMatrixDimensionsCheck : Bool :=
  substitutionMatrix.length == 168 &&
    substitutionMatrix.all fun row => row.length == 168

def substitutionColumnSum (j : SubstitutionLabel) : Nat :=
  let column := getD substitutionIndexColumns (substitutionLabels.idxOf j) []
  (List.range 168).foldl
    (fun total i => total + (column.filter fun index => index == i).length) 0

def substitutionConstantColumnSumCheck : Bool :=
  let columns := substitutionIndexColumns
  columns.length == 168 && columns.all fun column =>
    (List.range 168).foldl
      (fun total i => total + (column.filter fun index => index == i).length) 0 == 8

def substitutionIndexSuccessorsIn (columns : List (List Nat))
    (labelIndex : Nat) : List Nat :=
  (getD columns labelIndex []).eraseDups

def substitutionReachableStepIn (columns : List (List Nat))
    (labelIndices : List Nat) : List Nat :=
  (labelIndices.flatMap (substitutionIndexSuccessorsIn columns)).eraseDups

def substitutionPowerLabelsIn (columns : List (List Nat))
    (power labelIndex : Nat) : List Nat :=
  iterateN (substitutionReachableStepIn columns) power [labelIndex]

/-- Labels reached by paths of exactly `power` substitution steps.  Thus this
is the support of the corresponding column of `S^power`. -/
def substitutionPowerLabels (power labelIndex : Nat) : List Nat :=
  substitutionPowerLabelsIn substitutionIndexColumns power labelIndex

def substitutionPowerPositive (power : Nat) : Bool :=
  let columns := substitutionIndexColumns
  (List.range 168).all fun labelIndex =>
    setEq (substitutionPowerLabelsIn columns power labelIndex) (List.range 168)

/-- Search includes 0 and stops at 6.  A returned value is automatically the
least exponent because `List.find?` scans in increasing order. -/
def leastPrimitiveExponent : Option Nat :=
  (List.range 7).find? substitutionPowerPositive

structure ModularAddressState where
  address : V3
  labelIndices : List Nat
deriving BEq, Repr

def initialModularAddressState : ModularAddressState :=
  { address := v 0 0 0, labelIndices := List.range 168 }

def modularAddressStepIn (columns : List (List Nat))
    (states : List ModularAddressState) :
    List ModularAddressState :=
  states.flatMap fun state => bits.map fun digit =>
    { address := state.address.smul 2 |>.add digit
      labelIndices := (state.labelIndices.filterMap fun labelIndex =>
        (getD columns labelIndex [])[bits.idxOf digit]?).eraseDups }

def modularAddressStep (states : List ModularAddressState) :
    List ModularAddressState :=
  modularAddressStepIn substitutionIndexColumns states

def modularAddressStates (depth : Nat) : List ModularAddressState :=
  let columns := substitutionIndexColumns
  iterateN (modularAddressStepIn columns) depth [initialModularAddressState]

def hasModularCoincidence (depth : Nat) : Bool :=
  (modularAddressStates depth).any fun state => state.labelIndices.length == 1

/-- As above, the increasing search through depths 0,…,6 makes the reported
coincidence depth least. -/
def leastModularCoincidenceDepth : Option Nat :=
  (List.range 7).find? hasModularCoincidence

def modularCoincidenceWitness (depth : Nat) :
    Option (V3 × SubstitutionLabel) :=
  match (modularAddressStates depth).find? fun state =>
      state.labelIndices.length == 1 with
  | some state =>
      match state.labelIndices with
      | [labelIndex] =>
          (substitutionLabels[labelIndex]?).map fun label => (state.address, label)
      | _ => none
  | none => none

/-! ## Closure of the legal 2x2x2 block language and fixed seeds

A legal block is ordered by `bits`.  Substituting such a block gives a 4x4x4
block; its 27 binary windows have lower corners in `{0,1,2}³`.  Adjoining all
of those windows is the language-closure operator.  The finite theorem below
checks its successive cardinalities and an actual fixed point of this
operator, rather than searching patches to a prescribed depth.
-/

abbrev SubstitutionBlock := List Nat

def substitutionBlockWindowOrigins : List V3 :=
  (List.range 3).flatMap fun x =>
    (List.range 3).flatMap fun y =>
      (List.range 3).map fun z => v (Int.ofNat x) (Int.ofNat y) (Int.ofNat z)

def substitutionIndexAtIn (columns : List (List Nat)) (labelIndex : Nat)
    (address : V3) : Nat :=
  getD (getD columns labelIndex []) (bits.idxOf address) substitutionLabels.length

def substitutionBlockWindowIn (columns : List (List Nat))
    (block : SubstitutionBlock) (origin : V3) : SubstitutionBlock :=
  bits.map fun offset =>
    let point := origin.add offset
    let parent := v (point.x / 2) (point.y / 2) (point.z / 2)
    let residue := v (point.x % 2) (point.y % 2) (point.z % 2)
    let labelIndex := getD block (bits.idxOf parent) substitutionLabels.length
    substitutionIndexAtIn columns labelIndex residue

def substitutionBlockLanguageStepIn (columns : List (List Nat))
    (language : List SubstitutionBlock) : List SubstitutionBlock :=
  hashDedup (language ++ language.flatMap fun block =>
    substitutionBlockWindowOrigins.map (substitutionBlockWindowIn columns block))

def substitutionBlockLanguageRoundsIn (columns : List (List Nat)) :
    List (List SubstitutionBlock) :=
  let round0 := hashDedup columns
  let round1 := substitutionBlockLanguageStepIn columns round0
  let round2 := substitutionBlockLanguageStepIn columns round1
  let round3 := substitutionBlockLanguageStepIn columns round2
  let round4 := substitutionBlockLanguageStepIn columns round3
  [round0, round1, round2, round3, round4]

/-- The five distinct stages, starting with the 168 first-level blocks. -/
def substitutionBlockLanguageRounds : List (List SubstitutionBlock) :=
  substitutionBlockLanguageRoundsIn substitutionIndexColumns

def substitutionBlockLanguageClosure : List SubstitutionBlock :=
  getD substitutionBlockLanguageRounds 4 []

def substitutionBlockLanguageClosureSizes : List Nat :=
  substitutionBlockLanguageRounds.map List.length

def substitutionBlockLanguageStable : Bool :=
  let columns := substitutionIndexColumns
  let language := substitutionBlockLanguageClosure
  hashNoDuplicates language &&
    hashSetEq (substitutionBlockLanguageStepIn columns language) language

/-- The eight sites of the seed cube `{-1,0}³`, in the order matching the
binary block order after translation by `(1,1,1)`. -/
def substitutionSeedPositions : List V3 :=
  [v (-1) (-1) (-1), v (-1) (-1) 0, v (-1) 0 (-1), v (-1) 0 0,
   v 0 (-1) (-1), v 0 (-1) 0, v 0 0 (-1), v 0 0 0]

/-- A site `-d` has itself as parent and has binary residue `d`. -/
def substitutionSeedResidues : List V3 :=
  [v 1 1 1, v 1 1 0, v 1 0 1, v 1 0 0,
   v 0 1 1, v 0 1 0, v 0 0 1, v 0 0 0]

def substitutionFixedSeedIn (columns : List (List Nat))
    (block : SubstitutionBlock) : Bool :=
  block.length == 8 && (List.range 8).all fun i =>
    let labelIndex := getD block i substitutionLabels.length
    let residue := getD substitutionSeedResidues i (v 0 0 0)
    substitutionIndexAtIn columns labelIndex residue == labelIndex

def substitutionFixedSeeds : List SubstitutionBlock :=
  let columns := substitutionIndexColumns
  substitutionBlockLanguageClosure.filter (substitutionFixedSeedIn columns)

/-- One-step in-place reproduction implies the same containment at every
iteration, because substitution preserves labelled subconfigurations. -/
def substitutionSeedReproducesInPlaceIn (columns : List (List Nat))
    (block : SubstitutionBlock) : Bool :=
  substitutionSeedPositions.length == 8 &&
    substitutionSeedPositions.length == substitutionSeedResidues.length &&
    (List.range substitutionSeedPositions.length).all fun i =>
      let labelIndex := getD block i substitutionLabels.length
      let residue := getD substitutionSeedResidues i (v 0 0 0)
      substitutionIndexAtIn columns labelIndex residue == labelIndex

def frameActSubstitutionLabel (frame : Frame) (label : SubstitutionLabel) :
    SubstitutionLabel :=
  { frame := frame.mul label.frame, cell := label.cell }

def frameActSubstitutionLabelIndexIn (labels : List SubstitutionLabel)
    (frame : Frame) (labelIndex : Nat) : Nat :=
  match labels[labelIndex]? with
  | some label => labels.idxOf (frameActSubstitutionLabel frame label)
  | none => labels.length

def substitutionSeedConfiguration (block : SubstitutionBlock) : List (V3 × Nat) :=
  substitutionSeedPositions.zip block

def frameActSubstitutionSeedIn (labelAction : List Nat) (frame : Frame)
    (block : SubstitutionBlock) : SubstitutionBlock :=
  let moved := (substitutionSeedConfiguration block).map fun entry =>
    (cellLower frame (v 0 0 0) entry.1,
      getD labelAction entry.2 substitutionLabels.length)
  substitutionSeedPositions.map fun position =>
    match moved.find? fun entry => entry.1 == position with
    | some entry => entry.2
    | none => substitutionLabels.length

def substitutionFrameLabelActions : List (Frame × List Nat) :=
  let labels := substitutionLabels
  orientationGroup.map fun frame =>
    (frame, (List.range labels.length).map fun labelIndex =>
      frameActSubstitutionLabelIndexIn labels frame labelIndex)

def substitutionSeedOrbitIn (frameActions : List (Frame × List Nat))
    (block : SubstitutionBlock) : List SubstitutionBlock :=
  hashDedup (frameActions.map fun action =>
    frameActSubstitutionSeedIn action.2 action.1 block)

def substitutionSeedOrbitsWithFuelIn (frameActions : List (Frame × List Nat)) :
    Nat → List SubstitutionBlock →
    List (List SubstitutionBlock)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, block :: rest =>
      let orbit := substitutionSeedOrbitIn frameActions block
      orbit :: substitutionSeedOrbitsWithFuelIn frameActions fuel
        (rest.filter fun other => !orbit.contains other)

def substitutionSeedOrbits : List (List SubstitutionBlock) :=
  substitutionSeedOrbitsWithFuelIn substitutionFrameLabelActions
    substitutionFixedSeeds.length
    substitutionFixedSeeds

def substitutionSeedStabilizerOrderIn (frameActions : List (Frame × List Nat))
    (block : SubstitutionBlock) : Nat :=
  (frameActions.filter fun action =>
    frameActSubstitutionSeedIn action.2 action.1 block == block).length

def substitutionSeedStabilizerHistogram : List (Nat × Nat) :=
  let frameActions := substitutionFrameLabelActions
  [1, 8].map fun order =>
    (order, (substitutionFixedSeeds.filter fun block =>
      substitutionSeedStabilizerOrderIn frameActions block == order).length)

/-- Binary addresses transform affinely under a signed-permutation action on
unit cells.  The correction by twice the image of the zero cell accounts for
the lower-corner `-1` on reversed coordinates. -/
def frameActSubstitutionAddress (frame : Frame) (address : V3) : V3 :=
  (cellLower frame (v 0 0 0) address).sub
    ((cellLower frame (v 0 0 0) (v 0 0 0)).smul 2)

def substitutionFrameCommutationCheckIn (columns : List (List Nat))
    (frameActions : List (Frame × List Nat)) : Bool :=
  frameActions.all fun action => (List.range substitutionLabels.length).all fun labelIndex =>
    bits.all fun address =>
      let movedAddress := frameActSubstitutionAddress action.1 address
      let movedLabel := getD action.2 labelIndex substitutionLabels.length
      let left := substitutionIndexAtIn columns movedLabel movedAddress
      let target := substitutionIndexAtIn columns labelIndex address
      let right := getD action.2 target substitutionLabels.length
      bits.contains movedAddress && left == right

structure SeedLanguageSummary where
  closureSizes : List Nat
  stable : Bool
  fixedSeedCount : Nat
  orbitCount : Nat
  orbitSizes : List Nat
  stabilizerHistogram : List (Nat × Nat)
  inPlaceReproduction : Bool
  frameCommutation : Bool
deriving BEq, Repr

/-- All theorem outputs are computed in one scope so the derived transition
table and the block-language closure are shared rather than reconstructed for
each reported field. -/
def substitutionSeedLanguageSummary : SeedLanguageSummary :=
  let columns := substitutionIndexColumns
  let rounds := substitutionBlockLanguageRoundsIn columns
  let language := getD rounds 4 []
  let stable := hashNoDuplicates language &&
    hashSetEq (substitutionBlockLanguageStepIn columns language) language
  let seeds := language.filter (substitutionFixedSeedIn columns)
  let frameActions := substitutionFrameLabelActions
  let orbits := substitutionSeedOrbitsWithFuelIn frameActions seeds.length seeds
  let histogram := [1, 8].map fun order =>
    (order, (seeds.filter fun block =>
      substitutionSeedStabilizerOrderIn frameActions block == order).length)
  { closureSizes := rounds.map List.length
    stable := stable
    fixedSeedCount := seeds.length
    orbitCount := orbits.length
    orbitSizes := orbits.map List.length
    stabilizerHistogram := histogram
    inPlaceReproduction := seeds.all (substitutionSeedReproducesInPlaceIn columns)
    frameCommutation := substitutionFrameCommutationCheckIn columns frameActions }

end R44
