# Discovery-script provenance

These six files are copied verbatim from packet
`verify/packets/einstein_macrostate/src/`. They are historical discovery and
construction programs, not independent verification and not evidence for the
R44 theorem. Their paths and SHA-256 digests are:

| File | Source packet path | SHA-256 |
|---|---|---|
| `build_candidate.py` | `verify/packets/einstein_macrostate/src/build_candidate.py` | `ba30d1e172222b52e90ab1497391feb757eabe62feaf17cd4cebafedb49be61c` |
| `build_solid.py` | `verify/packets/einstein_macrostate/src/build_solid.py` | `7f6da9e8ae5440fe811080f8ed3d59ebfdf6f98106c0ad1606c2f29ed3d0c3dc` |
| `chair_core.py` | `verify/packets/einstein_macrostate/src/chair_core.py` | `241bef2f5a69ff400a81c26cb987ee3a2b1d50a0aa6dd9aabcb32e78c65ac645` |
| `framed_chair.py` | `verify/packets/einstein_macrostate/src/framed_chair.py` | `20ecb3c14433ab65a302d206cb80fd9d341781b9f17822c7a0fa5283756c7260` |
| `explore_frames.py` | `verify/packets/einstein_macrostate/src/explore_frames.py` | `b9c1da57c2bac521be39dbd1e985a1f926814d03aede8dd785c526f57ea19fac` |
| `classify_frames.py` | `verify/packets/einstein_macrostate/src/classify_frames.py` | `edc192b871b14884594e68541182a967cd7898b385360efb145444070f6f4e8d` |

Recheck the copies from the repository root with:

```sh
sha256sum simulations/explore/{build_candidate.py,build_solid.py,chair_core.py,framed_chair.py,explore_frames.py,classify_frames.py}
```

The source scripts expect the packet's own `results/` layout when executed.
They were preserved as records, rather than adapted to the canonical repository
layout, precisely so that the hashes remain meaningful.

