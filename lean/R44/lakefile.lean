import Lake
open Lake DSL

package «R44» where
  version := v!"0.1.0"
  moreLeanArgs := #["-j", "4"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

@[default_target]
lean_lib R44

lean_lib R44Discharge where
  roots := #[
    `R44.Proved.BaselineComponentCoversGrid,
    `R44.Proved.ConcreteCompanions,
    `R44.Proved.GenericBoundaryLabels,
    `R44.Proved.GenericFeaturePartner,
    `R44.Proved.MeshSemantics,
    `R44.Proved.NativeDihedralSectors,
    `R44.Proved.FiniteEdgeExceptions,
    `R44.Proved.NativeBoundaryStrata,
    `R44.Proved.PlanarSectorArea,
    `R44.Proved.TangentIsometry,
    `R44.Proved.TentMeridianReduction,
    `R44.Proved.PolyhedralConeMeasure,
    `R44.Proved.SectorArithmetic,
    `R44.Proved.TentTangentCharts,
    `R44.Proved.UnrestrictedAlignment,
    `R44.Proved.WedgeVolume,
    `R44.Proved.CompleteDihedralList
  ]
