# Public release boundary

The public repository contains the Chair44 source, exact solid and certificates,
verification code, Lean development, paper source, viewer, simulations, notebook,
reader-package builder, media generators, video sources, and a small set of web
images. Large generated deliverables are published as GitHub or Zenodo release
assets instead of Git blobs.

The private working tree may continue to contain the ignored paths. Preparing a
release must not delete them. The final public branch is constructed as a clean,
pruned commit so that files already tracked in the private history do not enter
the public tree merely because `.gitignore` cannot affect tracked files.

## Excluded from the public tree

- internal agent configuration, prompts, logs, thread state, and raw dialogue;
- the construction cascade, retired implementations, and superseded delivery
  trees;
- review prompts, raw transcripts, temporary source extracts, PIDs, and nested
  review archives;
- downloaded third-party papers and validation archives;
- local environments, Lean dependencies, Blender distributions, caches, build
  products, raw render frames, audio intermediates, and duplicate movie revisions;
- bulk provenance snapshots, checkpoint archives, and duplicate upstream ZIPs;
- generated preview reader packages and notebook execution artifacts.

## Release assets outside Git

Build the reader bundles from the final public commit and attach them to the
release. Publish only the selected final captioned/clean film, subtitle file,
teaser, thumbnail, and their manifest. Print-resolution image masters may be
attached as a separate media pack. Checksums should accompany every binary
release asset.

## Licensing and third-party material

Unless a file says otherwise, original material in this repository is licensed
under Creative Commons Attribution 4.0 International; see `LICENSE`. Vendored or
third-party material retains its own licence and attribution, including
`viewer/vendor/THREE_LICENSE`. Downloaded papers are not redistributed.

CC BY 4.0 is the default licence used by Zenodo. Although software projects often
choose an OSI software licence, this repository intentionally applies the one
CC BY licence requested by its owner across its original mixed research material.
