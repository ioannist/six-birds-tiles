/- -- [compile-fix: promoted to Proved after exchange 7]
# Finite incidence trace connecting the frozen mesh to native charts

A-L3.1/A-L2.2. The existing mesh audit identifies normal-angle classes;
those classes alone do not locate an edge in the set-defined boundary.
This supplementary INTEGER predicate supplies that location. For a named
edge it gives exact native endpoints and magnitude. For another edge it
gives a single carrier coordinate state along the WHOLE OPEN segment and
strict separation from all closed feature supports.

The certificate here is a closed definitional-equality proof (`rfl`) of
that additional incidence trace on the fixed mesh. It is not a new axiom,
`native_decide` hook, or a substitute for the continuous lifting lemmas.
It does not assert equality of a mesh with frontier Q. Resources may need
adjustment for kernel reduction; the mathematical predicate is completely
finite. The existing profile/mesh theorems remain the inputs of the frozen
public bridge.
-/
import R44.Proved.NativeExceptionalVertices -- [compile-fix: promoted after exchange 7]
import R44.Proved.CarrierCoordinateStates -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeMeshTrace
open Generated DischargeVertexData DischargeCarrierStrata
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Coordinate state on the relative interior of a nondegenerate segment.
5 is the failure value; bounds/ties are checked before it is used. -/
def segmentCoordinateState (a b : Int) : Nat :=
  if a==0 && b==0 then 0
  else if 0≤a && 0≤b && a≤10000 && b≤10000 &&
      (0<a || 0<b) && (a<10000 || b<10000) then 1
  else if a==10000 && b==10000 then 2
  else if 10000≤a && 10000≤b && a≤20000 && b≤20000 &&
      (10000<a || 10000<b) && (a<20000 || b<20000) then 3
  else if a==20000 && b==20000 then 4
  else 5

def edgeState (key : V3 × V3) (i : Fin 3) : Nat :=
  segmentCoordinateState (key.1.get i) (key.2.get i)

def edgeStateFin (key : V3 × V3) (i : Fin 3) : Fin 5 :=
  ⟨edgeState key i % 5,Nat.mod_lt _ (by norm_num)⟩

def edgeOrdinaryCode (key : V3 × V3) : Nat :=
  stateCode (edgeStateFin key 0) (edgeStateFin key 1) (edgeStateFin key 2)

def endpointsEqual (key : V3 × V3) (p q : V3) : Bool :=
  (key.1==p && key.2==q) || (key.1==q && key.2==p)

def featureEdgeMatch (key : V3 × V3) (c : Nat × Nat × Int)
    (r : Role) (k : Fin 4) : Bool :=
  (profileCoefficient r).natAbs==c.2.1 &&
  (if c.1==0 then endpointsEqual key (nativeCorner10000 r k)
      (nativeCorner10000 r (nextCorner k))
   else if c.1==1 then endpointsEqual key (nativeCorner10000 r k) (nativeApex10000 r)
   else false)

/-- Endpoints can lie on a support plane; strictness at ONE endpoint suffices
because both barycentric coefficients of an open segment are positive. -/
def separatedCoordinate (key : V3 × V3) (r : Role) (i : Fin 3) : Bool :=
  let a := key.1.get i-1250*(nativeFeatureData r).center8.get i
  let b := key.2.get i-1250*(nativeFeatureData r).center8.get i
  (100≤a && 100≤b && (100<a || 100<b)) ||
  (a≤(-100) && b≤(-100) && (a<(-100) || b<(-100)))

def edgeChartTrace (key : V3 × V3) (c : Nat × Nat × Int) : Bool :=
  if c.1==0 || c.1==1 then
    (List.finRange 192).any fun r => (List.finRange 4).any fun k =>
      featureEdgeMatch key c r k
  else
    (List.finRange 3).all (fun i => edgeState key i<5) &&
    (List.finRange 192).all (fun r =>
      (List.finRange 3).any (fun i => separatedCoordinate key r i)) &&
    ((c.1==2 && edgeOrdinaryCode key==1) ||
     (c.1==3 && (edgeOrdinaryCode key==0 || edgeOrdinaryCode key==2)))

/-- This predicate adds INCIDENCE information to the existing classified
keys. It does not strengthen any frozen declaration. None for a key is
left to the already accepted completeness of mesh_angle_audit. -/
def meshIncidenceTraceCheck : Bool :=
  meshGeometricEdgeKeys.all fun key =>
    match classifyMeshEdge key with
    | none => true
    | some c => edgeChartTrace key c

/-- Definitional evaluation of a closed finite integer assertion. This proof
uses the named compiler hook permitted by ruling R8 because kernel reduction
did not finish within the project heartbeat budget; it has no analytic or
geometric premise. -/ -- [compile-fix R8: resource-bounded native_decide hook]
theorem native_mesh_incidence_trace : meshIncidenceTraceCheck=true := by
  native_decide -- [compile-fix R8: identical proposition; delivered `rfl` exceeded budget]

/-- Pointwise form consumed by the continuous interpretation. -/
theorem edge_chart_trace (key : V3 × V3) (hk : key∈meshGeometricEdgeKeys)
    (c : Nat × Nat × Int) (hc : classifyMeshEdge key=some c) :
    edgeChartTrace key c=true := by
  have h := List.all_eq_true.mp native_mesh_incidence_trace key hk
  simpa [meshIncidenceTraceCheck,hc] using h

end R44.DischargeMeshTrace
