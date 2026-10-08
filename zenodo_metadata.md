# Zenodo deposit metadata / Zenodo 提交元数据

Copy the following into a new Zenodo upload. This file deliberately describes
the item as a preprint/research manuscript and preserves the existing
limitations and AI-use disclosure.

## Basic information

- Resource type: **Publication → Preprint**
- Upload type / access: **Open access**
- License: **CC-BY-4.0** / Creative Commons Attribution 4.0 International
- Publication date: **2026-10-08**
- Title: **Constant-factor bounds for Hamiltonian paths in tournaments**
- Version: **Research manuscript, 2026-10-08**
- Language: **English** (the archive also contains a Chinese version)
- Creator: **Liu, Xingchen**
- Affiliation: **Independent Researcher**
- ORCID: leave blank unless the author chooses to add a verified ORCID.

## Description

This record archives a bilingual research manuscript on constant-factor bounds
for the maximum number of directed Hamiltonian paths in an n-vertex tournament.
It includes English and Chinese PDF manuscripts, editable Markdown and LaTeX
sources, component proof-audit reports, exact finite diagnostic records, and
the Python verification modules used by the diagnostics.

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
AI-assisted internal proof reconstruction and cross-check, but it has not
undergone external human peer review or formal proof-assistant verification.
Finite computations in the archive are diagnostics, not replacements for the
all-order proof.

AI-use disclosure: AI assistants were used substantively for proof
reconstruction and cross-checking, translation, typesetting, and finite
diagnostic programming. The named author accepts responsibility for the
record's contents. AI systems are not listed as authors or creators.

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

Upload `tournament_hamiltonian_paths_zenodo_2026-10-08.zip`. It is a checked
snapshot of the public repository, including this metadata file.

## Submission checklist

1. Start a **New upload** on Zenodo, choose the resource type and fields above,
   and upload the archive.
2. Select **CC-BY-4.0** from Zenodo's license selector and Open access.
3. Choose “no” for an existing DOI. Optionally reserve a new DOI before
   publishing; a DOI is registered only when the record is published.
4. Use Zenodo's Preview, then publish only after reviewing the visible title,
   author, description, disclosure and files.
