# Zenodo deposit metadata / Zenodo 提交元数据

Version 1.1 is archived at [Zenodo record 23249802](https://zenodo.org/records/23249802),
with version DOI [10.5281/zenodo.23249802](https://doi.org/10.5281/zenodo.23249802)
and concept DOI [10.5281/zenodo.23233165](https://doi.org/10.5281/zenodo.23233165).
The fields below preserve the deposit description and upload instructions for
that version. Later repository edits are not part of the existing archive.

The public record's structured creator field, checked on 9 October 2026, spells
the first creator as `Liu, Xingxhen`. It should read `Liu, Xingchen`, as in the
manuscript and citation metadata. Correct this field in the existing record;
the title and description already use the intended author name.

Use the following fields when creating a **new version of the existing Zenodo record**.
This is a revised preprint/research manuscript, not an unrelated new deposit.
The previous published version and its DOI should remain intact.

## Basic information

- Resource type: **Publication → Preprint**
- Upload type / access: **Open access**
- License: **CC-BY-4.0** / Creative Commons Attribution 4.0 International
- Publication date: **2026-10-09**
- Title: **Constant-factor bounds for Hamiltonian paths in tournaments**
- Version: **1.1 (revised manuscript, 2026-10-09)**
- Language: **English** (the archive also contains a Chinese version)
- First creator: **Liu, Xingchen** — **Independent Researcher**
- Second creator: **Ye, Xiangyu** — **Independent Researcher**
- ORCID: leave blank unless an author provides a verified ORCID.

## Description

This record archives a bilingual research manuscript on constant-factor bounds
for the maximum number of directed Hamiltonian paths in an n-vertex tournament.
It includes English and Chinese PDF manuscripts, editable Markdown and LaTeX
sources, the companion Lean formalization, component proof-audit reports, exact
finite diagnostic records, and Python verification modules.

Let H(T) count vertex permutations forming a directed Hamiltonian path, let
P(n) be its maximum over n-vertex tournaments, and put mu_n = n!/2^(n-1). The
manuscript establishes that there are absolute constants K and n_0 such that,
for all n >= n_0,

(L - K/n) mu_n <= P(n) <= (C_* + K/n) mu_n,

where L = cosh(1)/cos(1) and
C_* = (3 pi^4 + 4 pi^2 - 32)/(pi^4 + 4 pi^2 - 32). The manuscript does not
claim an exact finite formula for P(n), a sharp global identity with leading
constant L, effective numerical values of K or n_0, or an extremal
classification.

Research status: this is a research manuscript/preprint. It has undergone an
AI-assisted internal proof reconstruction and cross-check, and its main theorem
has a companion Lean formalization contributed by second author Xiangyu Ye
(GitHub: makerY666) through PR #1. The PR includes a recorded successful
project build and transitive axiom audit; this manuscript revision did not
independently rerun the complete Lean verification. External human peer review
has not been reported. Finite computations are diagnostics, not replacements
for the all-order proof.

AI-use disclosure: AI assistants were used substantively for proof
reconstruction and cross-checking, translation, typesetting, and finite
diagnostic programming. The two named authors are credited for their respective
contributions. AI systems are not listed as authors or creators.

Repository and version control: https://github.com/LStar404/tournament-hamiltonian-paths

## Keywords

tournament; directed Hamiltonian path; permanent; matrix scaling; skew spectrum;
Gaussian determinant; preprint; graph theory; combinatorics

## Related identifiers

- Relation: **Is supplemented by**
- Identifier: https://github.com/LStar404/tournament-hamiltonian-paths
- Identifier scheme: URL
- Resource type: Software / Other

## Files to upload

Upload `tournament_hamiltonian_paths_zenodo_2026-10-09_v1.1.zip`. It is a checked
snapshot of the revised public repository, including both PDF manuscripts,
editable sources, the Lean formalization, and this metadata file.

## Submission checklist

1. Open the existing Zenodo record and select **New version**; do not start an
   unrelated new upload. Replace the previous archive with the revised archive.
2. Select **CC-BY-4.0** from Zenodo's license selector and Open access.
3. Preserve Zenodo's version chain. The new version receives its own DOI while
   the concept DOI continues to resolve to the latest version.
4. Use Zenodo's Preview, then publish only after reviewing both creators in
   order, the description, disclosure, version and replacement archive.
