# Revision 2 — 16 September 2026

This revision improves the explanation of the existing Chair44 construction. The
solid, panel numbering, signed feature patterns, visual notation, certificates
and Lean development are unchanged.

- Section 2 now gives a reading guide to the existing panel diagrams: coordinate
  axes, panel placement, the three inset notch faces, and the relation between
  coordinate diagrams and exterior views of a physical model.
- A worked example reconstructs the base centre and apex of panel 13's −9 dent.
  The text distinguishes an annotated paper model from the actual geometric tile.
- The original height-table derivation, mesh/topology argument, asymmetry proof,
  feature-angle details, tube construction and open parameter family are retained
  in Appendix E. References from the existence and registration arguments point
  to the corresponding appendix subsections.
- The paper labels the existing Zenodo DOI as the published version 1. This local
  revision does not alter that record or assert a new DOI.
- The arXiv packaging script uses a fresh staging directory and refuses to
  overwrite an existing named package, preserving earlier release artifacts.

Validation includes exact reconstruction of all 192 feature apexes and 768 base
vertices from the written recipe, checking all six exterior-view conventions,
checking preservation of the original geometric argument blocks and panel figure,
and PDF/reference/citation/ledger checks. These checks validate this expository
revision; they are not a fresh Lean build or a new verification of the full theorem.

The published paper-v1 and v1.0.0 tags continue to identify the original release.
