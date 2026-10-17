#!/usr/bin/env python3
"""chair44_rigidity.py - are the smooth Chair44 variants rigid against NON-lattice contacts?

chair44_family.py shows that a decoration built by orbit projection has exactly the
published 44-contact atlas for contacts across whole unit faces.  A tiling is not obliged to
use such contacts: a neighbour may be slid, rotated about the face normal, mirrored or
slightly tilted.  This module tests those placements.

THE COVERING ARGUMENT (what the test is for)
  Let h_A be the height field on a panel of tile A (along A's outward normal).  Suppose
  (H1) the field vanishes in a margin along the panel edge, and (H3) it is not zero.
  In a tiling every point of A's surface is covered by neighbours, and no void may remain
  (a void is a pocket no macroscopic tile can fill).  At a non-flat point of A's surface a
  covering tile B must therefore have a panel whose surface coincides with A's there.  B's
  panel is flat in its own edge margin (H1), so a feature of A cannot be split between two
  tiles (the seam would lie where h_A != 0, but B's surface is flat at its seam): every
  connected feature of A is covered whole by one panel of one tile, and B's field must be
  the exact complement of A's on the overlap.  So non-lattice neighbours are possible only
  if some slide / rotation / small tilt makes two panel fields complementary on their overlap.
  (H2) is the numerical statement that this does not happen.  Then each panel of A is covered
  by one lattice-aligned neighbour whose footprint is the panel itself, nothing else can touch
  that panel, and the tiling is lattice-aligned, so the published combinatorial argument
  (which depends only on the 44-contact atlas) applies.

  Vacuous contacts (overlap contains no feature at all) cannot be excluded pairwise; the
  argument above excludes them: the aligned neighbour already occupies the footprint.

WHAT IS VERIFIED NUMERICALLY
  Stage 1 (FFT, exhaustive over slides, rotation about the normal every 3 degrees, mirror,
  sign, and an optional best-fit tilt plane): the overlap-restricted mismatch
        mu = int_Omega (h_A + h_B')^2 / int_Omega (h_A^2 + h_B'^2)
  of every non-lattice pose whose overlap contains features.  mu = 0 means exact complement.
  Stage 2 (coarse grid): each pose is classified penetrating / sealed void / open void /
  exact complement, because a pose with m <= 0 and only voids open to the outside would be
  a (weaker) candidate that mu alone does not exclude.

RESULT (as recorded in the Spectre fork, G=64, 3-degree steps; lattice basin +-10 deg / +-0.15 excluded)
  The only exact complements are the lattice contacts, and only between panels of the same
  class.  The best non-lattice candidates (mirrored half-panel slide) stay at mu ~ 0.076
  (R44-like fields), 0.10 (two-magnitude) and 0.006 (random smooth Gaussians) after continuous
  polishing: isolated local minima, never zero.  Smoother fields are SOFTER (smaller mu), so
  the margin shrinks with smoothness; mu is not a physical gap size.

WHAT IS NOT COVERED
  edge / vertex contacts, tilts too large for the field amplitude, body-body interference of
  the non-convex chair away from the panels, and a rigorous (rather than grid) treatment.
  A passing result is evidence for the smooth variants, not a proof.

    python3 chair44_rigidity.py                 # compare the standard fields
    python3 chair44_rigidity.py --quick
    python3 chair44_rigidity.py --phi-json best.json
"""
import argparse
import json
import math
import time

import numpy as np

import chair44 as C
import chair44_family as F

try:
    from scipy import ndimage as _ndi
except ImportError:                                  # fallback flood fill below
    _ndi = None


def rot(th):
    return np.array([[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]])


## ------------------------------------------------------------------ the scan domain
class Domain:
    """Cell-centred grid on [-pad, 1+pad]^2 (the panel is [0,1]^2), G cells per unit."""

    def __init__(self, G, pad=1.5):
        assert (pad * G) == int(pad * G)
        self.G, self.N = G, int(round((1 + 2 * pad) * G))
        k = (np.arange(self.N) + 0.5) / G - pad
        self.X, self.Y = np.meshgrid(k, k, indexing="ij")
        self.mA = self.inside(self.X, self.Y)
        self.mono = {(0, 0): np.ones_like(self.X), (1, 0): self.X, (0, 1): self.Y,
                     (2, 0): self.X ** 2, (1, 1): self.X * self.Y, (0, 2): self.Y ** 2}
        n = np.arange(self.N)
        shift = np.where(n < self.N // 2, n, n - self.N) / G
        self.sel = np.flatnonzero(np.abs(shift) <= 1.0 + 1e-9)       # shifts with |s|,|t| <= 1
        self.S = shift[self.sel]

    @staticmethod
    def inside(u, v):
        return ((u > 0) & (u < 1) & (v > 0) & (v < 1)).astype(float)

    def corr(self, Ff, Fg):
        """r[s,t] = sum_x f(x) g(x - (s,t)), restricted to |s|,|t| <= 1."""
        r = np.real(np.fft.ifft2(Ff * np.conj(Fg)))
        return r[np.ix_(self.sel, self.sel)]


def panel_field(field, panel, U, V):
    return field.eval(panel, U, V) * Domain.inside(U, V)


## --------------------------------------------------------------------- stage 1
def scan(field, ident, G=64, theta_step=3.0, eps=0.02, rs=0.15, rtheta=1.0, tilt=True,
         verbose=False, basin_theta=10.0):
    """Exhaustive FFT scan of planar rigid motions of a neighbouring panel (see module doc)."""
    D = Domain(G)
    reps = ident.reps
    nc = len(reps)
    fA = [panel_field(field, r, D.X, D.Y) for r in reps]
    EA = [float((f ** 2).sum()) / G ** 2 for f in fA]
    FfA = [np.fft.fft2(f) for f in fA]
    FfA2 = [np.fft.fft2(f ** 2) for f in fA]
    FfAmono = [{ab: np.fft.fft2(f * D.mono[ab]) for ab in ((1, 0), (0, 1))} for f in fA]
    FmAmono = {ab: np.fft.fft2(D.mA * m) for ab, m in D.mono.items()}
    K = len(D.sel)
    SS, TT = np.meshgrid(D.S, D.S, indexing="ij")
    near0 = (np.abs(SS) < rs) & (np.abs(TT) < rs)
    res = {"G": G, "classes": nc, "energies": EA, "poses_scanned": 0, "vacuous": 0,
           "min_slide": (np.inf,), "min_tilt": (np.inf,), "lattice_zero": {}, "profiles": {},
           "heat": None}
    thetas = np.arange(0.0, 360.0, theta_step)
    nonlat_total = 0
    for mirror in (0, 1):
        Fm = np.diag([1.0, -1.0 if mirror else 1.0])
        for th_deg in thetas:
            Lm = rot(math.radians(th_deg)) @ Fm
            dx, dy = D.X - 0.5, D.Y - 0.5
            Q1 = 0.5 + Lm[0, 0] * dx + Lm[1, 0] * dy
            Q2 = 0.5 + Lm[0, 1] * dx + Lm[1, 1] * dy
            mB0 = Domain.inside(Q1, Q2)
            FmB = np.fft.fft2(mB0)
            fB = [field.eval(r, Q1, Q2) * mB0 for r in reps]
            EB = [float((f ** 2).sum()) / G ** 2 for f in fB]
            FfB = [np.fft.fft2(f) for f in fB]
            FfB2 = [np.fft.fft2(f ** 2) for f in fB]
            FmA = FmAmono[(0, 0)]
            # Gram matrix of {1,X,Y} on the overlap and its inverse
            Gm = {ab: D.corr(FmAmono[ab], FmB) / G ** 2 for ab in D.mono}
            Gmat = np.stack([np.stack([Gm[(0, 0)], Gm[(1, 0)], Gm[(0, 1)]], -1),
                             np.stack([Gm[(1, 0)], Gm[(2, 0)], Gm[(1, 1)]], -1),
                             np.stack([Gm[(0, 1)], Gm[(1, 1)], Gm[(0, 2)]], -1)], -2)
            area = Gm[(0, 0)]
            ok_area = area > 0.03
            Gs = np.where(ok_area[..., None, None], Gmat, np.eye(3))
            Ginv = np.linalg.inv(Gs + 1e-12 * np.eye(3))
            is90 = abs(((th_deg + 45) % 90) - 45) < rtheta
            inbasin = abs(((th_deg + 45) % 90) - 45) <= basin_theta
            lattice = near0 if inbasin else np.zeros_like(near0)
            for a in range(nc):
                EAin = D.corr(FfA2[a], FmB) / G ** 2
                MA = np.stack([D.corr(FfA[a], FmB), D.corr(FfAmono[a][(1, 0)], FmB),
                               D.corr(FfAmono[a][(0, 1)], FmB)], -1) / G ** 2
                for b in range(nc):
                    EBin = D.corr(FmA, FfB2[b]) / G ** 2
                    Cr = D.corr(FfA[a], FfB[b]) / G ** 2
                    MB = np.stack([D.corr(FmAmono[(0, 0)], FfB[b]), D.corr(FmAmono[(1, 0)], FfB[b]),
                                   D.corr(FmAmono[(0, 1)], FfB[b])], -1) / G ** 2
                    Ein = EAin + EBin
                    nonvac = Ein >= eps * (EA[a] + EB[b])
                    for sg in (1, -1):
                        m2 = np.maximum(Ein + 2 * sg * Cr, 0.0)
                        mu = np.where(nonvac, m2 / np.maximum(Ein, 1e-300), np.inf)
                        key = (a, b, sg, mirror, int(round(th_deg)))
                        # lattice pose = zero shift, theta a multiple of 90
                        if is90:
                            i0 = int(np.argmin(np.abs(D.S)))
                            z = float(mu[i0, i0])
                            if z < 1e-6:
                                res["lattice_zero"][key] = z
                                res["profiles"][key] = {
                                    "mu_vs_s": mu[:, i0].tolist(), "mu_vs_t": mu[i0, :].tolist(),
                                    "S": D.S.tolist()}
                                if res["heat"] is None:
                                    res["heat"] = mu.copy()
                        nl = ~lattice
                        nonlat_total += int(nl.sum())
                        res["vacuous"] += int((nl & ~nonvac).sum())
                        cand = np.where(nl, mu, np.inf)
                        k = int(np.argmin(cand))
                        if cand.flat[k] < res["min_slide"][0]:
                            i, j = divmod(k, K)
                            res["min_slide"] = (float(cand.flat[k]), key, float(D.S[i]), float(D.S[j]),
                                                float(Ein[i, j] / (EA[a] + EB[b])))
                        if tilt:
                            Mv = MA + sg * MB
                            quad = np.einsum("...i,...ij,...j->...", Mv, Ginv, Mv)
                            rt = np.maximum(m2 - quad, 0.0)
                            mut = np.where(nonvac & ok_area, rt / np.maximum(Ein, 1e-300), np.inf)
                            cand = np.where(nl, mut, np.inf)
                            k = int(np.argmin(cand))
                            if cand.flat[k] < res["min_tilt"][0]:
                                i, j = divmod(k, K)
                                res["min_tilt"] = (float(cand.flat[k]), key, float(D.S[i]), float(D.S[j]),
                                                   float(Ein[i, j] / (EA[a] + EB[b])))
            res["poses_scanned"] += 1
        if verbose:
            print("  mirror", mirror, "done")
    res["nonlattice_poses"] = nonlat_total * 1
    res["vacuous_fraction"] = res["vacuous"] / max(nonlat_total, 1)
    return res


## ------------------------------------------------------------------- stage 2
def _label(mask):
    if _ndi is not None:
        return _ndi.label(mask)
    lab = np.zeros(mask.shape, int)
    n = 0
    for i, j in zip(*np.nonzero(mask)):
        if lab[i, j]:
            continue
        n += 1
        stack = [(i, j)]
        lab[i, j] = n
        while stack:
            a, b = stack.pop()
            for c, d in ((a + 1, b), (a - 1, b), (a, b + 1), (a, b - 1)):
                if 0 <= c < mask.shape[0] and 0 <= d < mask.shape[1] and mask[c, d] and not lab[c, d]:
                    lab[c, d] = n
                    stack.append((c, d))
    return lab, n


def classify(field, ident, G=24, theta_step=15.0, eps=0.02, tol_pen=0.03, tol_void=0.03, rs=0.05):
    """Coarse void-aware classification of every non-lattice pose (slides in whole cells)."""
    pad = 2
    N = (1 + 2 * pad) * G
    k = (np.arange(N) + 0.5) / G - pad
    X, Y = np.meshgrid(k, k, indexing="ij")
    reps = ident.reps
    mA = Domain.inside(X, Y)
    fA = [panel_field(field, r, X, Y) for r in reps]
    EA = [float((f ** 2).sum()) / G ** 2 for f in fA]
    counts = {"vacuous": 0, "penetrating": 0, "sealed_void": 0, "open_void": 0, "complement": 0}
    examples = {"open_void": [], "complement": []}
    sl = slice(pad * G, (pad + 1) * G)
    for mirror in (0, 1):
        Fm = np.diag([1.0, -1.0 if mirror else 1.0])
        for th_deg in np.arange(0.0, 360.0, theta_step):
            Lm = rot(math.radians(th_deg)) @ Fm
            dx, dy = X - 0.5, Y - 0.5
            Q1 = 0.5 + Lm[0, 0] * dx + Lm[1, 0] * dy
            Q2 = 0.5 + Lm[0, 1] * dx + Lm[1, 1] * dy
            mB0 = Domain.inside(Q1, Q2)
            fB = [field.eval(r, Q1, Q2) * mB0 for r in reps]
            EB = [float((f ** 2).sum()) / G ** 2 for f in fB]
            is90 = abs(((th_deg + 45) % 90) - 45) < 1e-6
            for ds in range(-G, G + 1):
                for dt in range(-G, G + 1):
                    lattice = is90 and ds == 0 and dt == 0
                    if lattice:
                        continue
                    mBs = np.roll(mB0, (ds, dt), axis=(0, 1))[sl, sl]
                    om = mA[sl, sl] * mBs
                    if om.sum() == 0:
                        counts["vacuous"] += 8
                        continue
                    for b in range(len(reps)):
                        fBs = np.roll(fB[b], (ds, dt), axis=(0, 1))[sl, sl]
                        for a in range(len(reps)):
                            fa = fA[a][sl, sl]
                            for sg in (1, -1):
                                m = (fa + sg * fBs) * om
                                Ein = float(((fa * om) ** 2 + (fBs * om) ** 2).sum()) / G ** 2
                                if Ein < eps * (EA[a] + EB[b]):
                                    counts["vacuous"] += 1
                                    continue
                                if m.max() > tol_pen:
                                    counts["penetrating"] += 1
                                    continue
                                voids = (m < -tol_void) & (om > 0)
                                if not voids.any():
                                    counts["complement"] += 1
                                    if len(examples["complement"]) < 5:
                                        examples["complement"].append((a, b, sg, mirror, float(th_deg), ds / G, dt / G))
                                    continue
                                lab, n = _label(voids)
                                outside = np.pad(om, 1, constant_values=0) == 0
                                touch = set()
                                for ii, jj in zip(*np.nonzero(voids)):
                                    if (outside[ii, jj + 1] or outside[ii + 2, jj + 1] or
                                            outside[ii + 1, jj] or outside[ii + 1, jj + 2]):
                                        touch.add(lab[ii, jj])
                                if len(touch) < n:
                                    counts["sealed_void"] += 1
                                else:
                                    counts["open_void"] += 1
                                    if len(examples["open_void"]) < 5:
                                        examples["open_void"].append((a, b, sg, mirror, float(th_deg), ds / G, dt / G))
    return counts, examples


## ---------------------------------------------------------------- field zoo
def standard_fields(ident, phi_json=None, seed=11):
    zoo = {}
    zoo["R44-like pyramids (rho=0.05)"] = F.SiteField(ident, None, 0.05, "pyramid")
    zoo["R44-like cosine bumps (rho=0.11)"] = F.SiteField(ident, None, 0.11, "cosine")
    mags = [__import__("fractions").Fraction(1 if abs(int(x)) not in (8, 12) else 2) * (1 if x > 0 else -1)
            for x in ident.deco.profile]
    zoo["two-magnitude cosine bumps"] = F.SiteField(ident, mags, 0.11, "cosine")
    rng = np.random.default_rng(seed)
    zoo["random projected Gaussians"] = F.normalize(
        ident.project([F.gaussian_phi(F.random_atoms(rng, 4)) for _ in ident.classes]))
    if phi_json:
        atoms = json.load(open(phi_json))["atoms"]
        zoo["searched smooth field"] = F.normalize(ident.project([F.gaussian_phi(a) for a in atoms]))
    return zoo


def report(name, r):
    lz = r["lattice_zero"]
    same = sorted({(k[0], k[1]) for k in lz})
    print("  %s" % name)
    print("    lattice exact complements at (a,b) class pairs %s ; cross-class (0,1)/(1,0): %s" % (
        same, "none" if not any(k[0] != k[1] for k in lz) else "PRESENT"))
    ms = r["min_slide"]
    print("    non-lattice, features overlapped: min mu (no tilt) = %.4f at class pair %s sign %+d mirror %d theta %d,"
          " shift (%.3f, %.3f), feature energy in overlap %.0f%%" % (
              ms[0], ms[1][:2], ms[1][2], ms[1][3], ms[1][4], ms[2], ms[3], 100 * ms[4]))
    mt = r["min_tilt"]
    if mt[0] < np.inf:
        print("    with best-fit tilt plane:                       min mu = %.4f at theta %d, shift (%.3f, %.3f)" % (
            mt[0], mt[1][4], mt[2], mt[3]))
    print("    vacuous (no feature in overlap) share of non-lattice poses: %.1f%%" % (100 * r["vacuous_fraction"]))
    if lz:
        k = next(iter(lz))
        pr = r["profiles"][k]
        S = np.array(pr["S"])
        mu = np.array(pr["mu_vs_s"])
        pick = [float(mu[int(np.argmin(np.abs(S - d)))]) for d in (0.05, 0.1, 0.25, 0.5)]
        print("    stiffness: mu along a slide from a lattice contact at s = 0.05/0.1/0.25/0.5: %s" % (
            ["%.3f" % x if np.isfinite(x) else "vac" for x in pick]))


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--phi-json")
    ap.add_argument("--G", type=int, default=64)
    ap.add_argument("--no-tilt", action="store_true")
    ap.add_argument("--stage2", action="store_true", help="also run the coarse void-aware classification")
    ap.add_argument("--json")
    a = ap.parse_args(argv)
    ident = F.Identification()
    zoo = standard_fields(ident, a.phi_json)
    out = {}
    for name, fld in zoo.items():
        t0 = time.time()
        r = scan(fld, ident, G=32 if a.quick else a.G, theta_step=6.0 if a.quick else 3.0, tilt=not a.no_tilt)
        report(name, r)
        ms = r["min_slide"]
        rf = refine(fld, ident, ms[1], (ms[2], ms[3]))
        r["refined"] = rf
        print("    continuous refinement of that candidate: mu = %.5f at theta %.2f, shift (%.3f, %.3f)"
              "  -> %s" % (rf + ("isolated local minimum, NOT a contact" if rf[0] > 1e-3 else "NEAR-ZERO: inspect",)))
        print("    (stage 1: %.0fs)" % (time.time() - t0))
        out[name] = {k: v for k, v in r.items() if k not in ("heat", "profiles")}
        if a.stage2:
            t0 = time.time()
            counts, ex = classify(fld, ident, G=16 if a.quick else 24, theta_step=30.0 if a.quick else 15.0)
            print("    stage 2 classes of non-lattice poses: %s   (%.0fs)" % (counts, time.time() - t0))
            out[name]["stage2"] = counts
            out[name]["stage2_examples"] = ex
    if a.json:
        json.dump(out, open(a.json, "w"), default=float, indent=1)
        print("wrote", a.json)



## ------------------------------------------------------------ continuous refinement
def mu_pose(field, reps, a, b, sg, mirror, th_deg, s, t, G=96, tilt=False):
    """Overlap-restricted mismatch of panel a (fixed) against panel b moved by (mirror, theta, slide)."""
    k = (np.arange(int(3 * G)) + 0.5) / G - 1.0
    X, Y = np.meshgrid(k, k, indexing="ij")
    Lm = rot(math.radians(th_deg)) @ np.diag([1.0, -1.0 if mirror else 1.0])
    dx, dy = X - s - 0.5, Y - t - 0.5
    Q1 = 0.5 + Lm[0, 0] * dx + Lm[1, 0] * dy
    Q2 = 0.5 + Lm[0, 1] * dx + Lm[1, 1] * dy
    om = Domain.inside(X, Y) * Domain.inside(Q1, Q2)
    if om.sum() == 0:
        return np.inf
    fa = field.eval(reps[a], X, Y)
    fb = field.eval(reps[b], Q1, Q2)
    m = (fa + sg * fb) * om
    if tilt:
        A = np.stack([om.ravel(), (X * om).ravel(), (Y * om).ravel()], 1)
        c, *_ = np.linalg.lstsq(A, m.ravel(), rcond=None)
        m = (m.ravel() - A @ c).reshape(m.shape)
    den = ((fa * om) ** 2 + (fb * om) ** 2).sum()
    return float((m ** 2).sum() / max(den, 1e-300))


def refine(field, ident, key, shift, G=96, tilt=False):
    """Nelder-Mead polish of (theta, s, t) from a stage-1 candidate; returns (mu, theta, s, t)."""
    from scipy.optimize import minimize
    a, b, sg, mirror, th = key
    reps = ident.reps
    f = lambda x: mu_pose(field, reps, a, b, sg, mirror, x[0], x[1], x[2], G, tilt)
    best = None
    for dth in (-1.5, 0.0, 1.5):
        r = minimize(f, [th + dth, shift[0], shift[1]], method="Nelder-Mead",
                     options={"xatol": 1e-5, "fatol": 1e-12, "maxiter": 600})
        if best is None or r.fun < best.fun:
            best = r
    return (float(best.fun), float(best.x[0]), float(best.x[1]), float(best.x[2]))

if __name__ == "__main__":
    main()
