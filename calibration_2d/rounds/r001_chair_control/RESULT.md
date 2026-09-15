# R001 — a self-subdividing shape can retain a periodic bare tiling

The scale2 chair has an exact partition into four congruent chairs. The search
found one such cell partition. A separate verifier checked its congruence,
coverage and absence of overlapping unit-cell interiors. Conversely, a 3-by-2
rectangle has two exhibited partitions into two chairs. Repeating either
rectangle gives a full-plane bare tiling with periods (3,0) and (0,2).

The candidate is connected, unmarked, nonempty and recursively realizable,
but it is not an Einstein. This is a constructive negative result with an
infinite periodic witness, not a finite failure to find aperiodicity.

SBT split: any geometry-determined equivariant observation on the exhibited
tiling must retain its periods. Externally choosing nested parent origins with
unbounded separation violates that requirement. Hence a separated-marker
hierarchy for every bare chair tiling does not descend through this interface.
The present proof does not assert a particular arbitrary dyadic decoration
is geometrically a valid chair hierarchy; it establishes that no such lawful
unbounded separated-marker decoder can exist on the whole bare hull.

Lesson: even successful exact self-subdivision and a nonempty tiling hull leave
the all-tilings recognition bridge missing. Preserve this periodic witness
as an ablation control for any future forcing repair. Three-dimensional
transfer: replace the planar rectangle by a repeating box; the same missing
bridge survives extrusion.

Next: attempt a geometric boundary repair, and check whether retaining the
four exact similarity maps already freezes the shape.
