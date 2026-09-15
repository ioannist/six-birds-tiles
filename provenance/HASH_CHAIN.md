# Provenance hash chain: repo checkpoint 350 → R44

Verified 2026-09-06 in the fusion session (sha256, every link recomputed locally).

| Link | File | sha256 |
|---|---|---|
| root | six-birds-tiles_2026-09-06.zip (this repo at checkpoint 350) | 486d6aec268a2b9f21a32bcb40169da440b69e96af73cfc62d881bde1e429254 |
| 1 | einstein_takeover_handoff.zip (declares root as base) | e6a9f00baeae2ecd8792d662fa82fd95d1cfba4d98f92f62fff3e705997ada8c |
| 2 | einstein_next_batch.zip (embeds packet 1 verbatim under upstream/) | fef15bcfbfbf1509c0dcb80836bc8d3bd5024dccfba27dedcb7c969666421173 |
| 3 | einstein_recursive_interface.zip (INPUT_PROVENANCE names root + packet 2 by the hashes above) | ffd944bf29027ad3dc236ea171a3aea4f7f36076b472948734ede14cc8fbb9ac |
| 4 | einstein_reverse_descent.zip (ships packet 3 under upstream/, hash + content match) | ac6016d8e72b36abcf41a0250dfd456633714825315c41cb3623a0879a642243 |
| 5 | einstein_r44_proof_submission.zip (ships packet 4 under upstream/, hash + content match) | ec2185fda29034a4581fafd308f8866ff1cb91beaaf85ccbf9e26803febe7f45 |
| 6 | r44_unrestricted_alignment.zip (ships packet 5 under upstream/, hash + content match) | a3979ab542a9aed2fffc8dcc6b23f946425c631ca332b100061afe402d140dae |
| solid | r44_solid.json, identical in packets 5 and 6 | f320d7a0c2d784a3eb29f001dc035808f67591d9ea8d3dd45949e66442f0ed55 |

Packet 3 also names a third input, `tsiokos(20260905-200915).zip`
(a68c8f63…), the SBT paper corpus supplied to the external thread; the same
Foundations IV source is cited by hash 4754d40e… in packet 5's SOURCE_AUDIT.md.
That corpus is `provenance/sbt_papers/` here (not re-hashed against the zip).

Every packet's own MANIFEST.json was checked file-by-file against its bytes
(48/48, 81/81, 39/39, 28/28, 41/41, 13/13). Every packet's stdlib replay
passed; the six mutation controls in packet 6 were all rejected.
