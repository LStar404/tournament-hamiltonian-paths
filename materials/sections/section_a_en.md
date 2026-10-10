## Appendix A. Formalization and reproducibility

### A.1 Formal statements and correspondence

The [companion Lean project](https://github.com/LStar404/tournament-hamiltonian-paths/tree/8ea3fcffcc12b6a06294ba7559885b439eda3cac/formalization) uses the same finite objects as this paper: a tournament is a loopless orientation of every pair of distinct labelled vertices; a Hamiltonian path is a vertex permutation whose consecutive arcs point forward; and $P(n)$ is the maximum of the resulting count. Lean and Mathlib are pinned to version 4.34.1.

The declaration `TournamentHamiltonian.mainBound : TournamentHamiltonian.MainBound` proves Theorem 1.1 with the exact constants $L$ and $C_*$. Its conclusion chooses one $K\ge0$ and one $n_0\ge2$ before quantifying over all $n\ge n_0$. The final theorem has no unproved permanent, scaling, activity or path-count premise. The separate declaration `small_score_pathCount_spectral_approximation_eventually` proves Theorem 4.1: its absolute error constant is independent of the score envelope $d(n)$, while its eventual threshold may depend on that envelope.

The formal development proves the principal analytic inputs as well as these conclusions. Some intermediate arguments differ from the presentation above. The permanent proof uses a geometric coefficient-moment bound in place of the displayed derivative constant $K_G$. The high-variance and exceptional-vertex cases use weaker sufficient estimates; for the latter the formal bound is $(10/3)4^{-f}(1+o(1))<1$ when $f\ge1$. The weighted determinant comparison uses positive principal-minor moments. Small-score restoration reuses paired preconditioning, and local scaling uses equivalent contraction estimates with a different fixed gap. The formal short-subset convention differs by one boundary layer, and the polarization and Gaussian-moment tools have finite-dimensional implementations. These choices prove the same stated rates and final bounds. The accompanying [result-by-result correspondence](verification/manuscript_alignment_20261011.md) records the intermediate differences.

### A.2 Verification records and auxiliary computations

The repository's [verification record](https://github.com/LStar404/tournament-hamiltonian-paths/blob/8ea3fcffcc12b6a06294ba7559885b439eda3cac/formalization/VERIFICATION.md) reports a successful complete run on 9 October 2026. The command `python verify_lean.py --require-main` builds the project, checks the actual `MainBound` declaration, checks project-source import coverage, and audits transitive theorem axioms against `propext`, `Classical.choice` and `Quot.sound`. The recorded audit contains 3674 theorem constants, including generated lemmas. All 246 stored Lean-source and configuration hashes match the sources inspected for this revision. These are the recorded build results and a source-correspondence check, rather than a new Lean build performed for the editorial revision.

A later remote CI run verifies the merged first-round baseline, commit `e07175db8b9b1df17a2434355953d3a05fbc625b`: [Verify proofs, run 38070905246](https://github.com/LStar404/tournament-hamiltonian-paths/actions/runs/38070905246) completed successfully on 10 October 2026 at 17:24 UTC (11 October at 01:24 UTC+8). Its build-and-audit and finite-diagnostics steps succeeded. This is remote evidence for that exact baseline, not a local rebuild or a claim that later editorial commits have already passed CI. The proof sources are unchanged in the present second-round revision; its own commit-specific CI result is recorded with its pull request. Successful compilation and finite checks do not replace a human audit of every displayed proof step.

Exact finite computations check normalizations, coefficient identities, deletion factors and the four-block expansion. They are separate from the all-order proof. The archived rational calculations give

$$
2.855957892565113<L<2.855957892565114,
$$

$$
2.857401177672316<C_*<2.857401177672317,
$$

and place $(C_*-L)/L$ between $0.000505359379058$ and $0.000505359379059$. The upper-constant enclosure is also proved in Lean; the other decimal enclosures are recorded in the rational computational certificates.

Xiangyu Ye contributed the companion formalization, submitted in [pull request 1](https://github.com/LStar404/tournament-hamiltonian-paths/pull/1). AI tools assisted proof reconstruction, cross-checking, translation and exact-arithmetic diagnostics.

## References

[1] John Irving and Mohamed Omar. Revisiting the Rédei-Berge Symmetric Functions via Matrix Algebra. The Electronic Journal of Combinatorics 32(4) (2025), Paper P4.43, 23 pp. [DOI: 10.37236/13841](https://doi.org/10.37236/13841).

[2] Noga Alon. The Maximum Number of Hamiltonian Paths in Tournaments. Combinatorica 10(4) (1990), 319–324. [DOI: 10.1007/BF02128667](https://doi.org/10.1007/BF02128667).

[3] Yanjun Han and Jonathan Niles-Weed. Approximate independence of permutation mixtures. The Annals of Statistics, to appear ([author publication list](https://yanjunhan2021.github.io/publication.html)). [arXiv:2408.09341v2](https://arxiv.org/html/2408.09341v2) (9 September 2024); this is the version used for the lemma numbering cited here.

[4] Bo Deng, Xueliang Li, Bryan Shader and Wasin So. On the Maximum Skew Spectral Radius and Minimum Skew Energy of Tournaments. Linear and Multilinear Algebra 66(7) (2018), 1434–1441. [DOI: 10.1080/03081087.2017.1357676](https://doi.org/10.1080/03081087.2017.1357676).

[5] Peter McCullagh. An asymptotic approximation for the permanent of a doubly stochastic matrix. Journal of Statistical Computation and Simulation 84(2) (2014), 404–414. [DOI: 10.1080/00949655.2012.712122](https://doi.org/10.1080/00949655.2012.712122). [arXiv:1205.5723](https://arxiv.org/abs/1205.5723).

[6] N. C. Wormald. Tournaments with many Hamilton cycles. [Undated preprint](https://users.monash.edu.au/~nwormald/papers/hamtourn.pdf), 20 pp. Accessed 10 October 2026.

[7] Ehud Friedgut and Jeff Kahn. On the Number of Hamiltonian Cycles in a Tournament. Combinatorics, Probability and Computing 14(5–6) (2005), 769–781. [DOI: 10.1017/S0963548305006863](https://doi.org/10.1017/S0963548305006863).

[8] Eric Li. The Godsil–McKay Asymptotic for Latin Rectangles in the Sublinear Range of Erdős Problem 725. [arXiv:2608.01671v1](https://arxiv.org/html/2608.01671v1) (2026).

[9] Ilan Adler, Noga Alon and Sheldon M. Ross. On the Maximum Number of Hamiltonian Paths in Tournaments. Random Structures & Algorithms 18(3) (2001), 291–296. [DOI: 10.1002/rsa.1010](https://doi.org/10.1002/rsa.1010).

[10] Tibor Szele. Kombinatorikai vizsgálatok az irányított teljes gráffal kapcsolatban. Matematikai és Fizikai Lapok 50 (1943), 223–256. [Original volume archive](https://real-j.mtak.hu/7300/).
