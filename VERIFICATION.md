# Verification scope

The author and an independent AI reviewer verified the exact Lean proof bytes at Lean `4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Solution has 297 lines and no admissions or new axioms. Challenge is 1,651 bytes and has exactly three deliberate statement holes; it imports Mathlib alone.

| Check | Result |
| --- | --- |
| Fresh direct Solution compilation with warnings as errors | Author and independent reviewer passed |
| Random-name Challenge using dependency paths alone | Both passed, with exactly three deliberate-hole warnings |
| Complete raw selected declaration types and universe parameter lists | Both passed byte equality in separate processes |
| Transitive axioms of all three selected theorems | Only `propext`, `Classical.choice`, `Quot.sound` |
| Official v0.4 JSON Schema on the reviewed metadata | Author and independent reviewer passed |
| Pinned unchanged intake validators on the reviewed JSON document | Both passed through a strict JSON decoding adapter |
| Refreshed review-status metadata | Revalidated locally after review |
| Exact dependency and source inventories | Nine pinned source trees; 12,684 copied files and 9,090 Mathlib source files qualified |
| Independent mathematical scope and public whitelist review | Approved without blocking findings or source corrections |

Each proof stage used one serial compiler inside a Windows Job Object capped at one CPU and 3 GiB, with a bounded timeout and ownership cleanup. The author's final stage took 44.05 seconds and peaked at 2,404,720,640 bytes of job commit. The independent proof stage took 154.11 seconds and peaked at 2,402,414,592 bytes. Both had stable source hashes and no remaining owned processes. Full commands, hashes, measurements, and failure history are retained privately.

Dependency objects came from a pinned local cache. The author checked exact source revisions and clean tracked source trees; both author and reviewer checked copied source/artifact byte identity. Those objects were not rebuilt from source. The complete pinned Mathlib search and independent candidate inspection found no equivalent target at that revision; no worldwide formalization-priority claim follows.

The metadata is JSON-form YAML. Both validators checked the complete supplied official v0.4 JSON Schema and rejected invalid relationship, missing substantive-source, and negative-admission controls. The pinned Python intake validators ran unchanged, with only decoding replaced by a duplicate-rejecting JSON parser. This qualifies the exact JSON document; a general YAML parser was not tested. The refreshed review status is covered by a new local schema and intake-validator check. The original reviewer receipts remain historical evidence of the earlier metadata bytes.

The approved proof bytes did not change during the documentation and metadata refresh, so their successful compilation, type, universe, and axiom checks were preserved without duplicate proof builds. `REVIEW.md` records their exact hashes. The public whitelist contains 16 files; the full diagnostic archive remains private.

A clean dependency installation and ordinary Lake build, GitHub Actions, hosted Comparator, NaNoDa, and human mathematical review remain unrun. The minimal CI workflow is present. Publication and any collaborator invitation belong to the parent workflow; this desktop task makes no public repository mutation or registry submission.
