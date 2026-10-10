# 双语稿件与 Lean 证明对应记录

11 October 2026

## 范围和结论

本记录说明重组后的中英文正文如何对应已有 Lean 证明。主要定理使用真实的有限竞赛图、按顶点排列计数的有向 Hamilton 路径，以及相同的常数 L 和 C*；最终声明没有未解除的永久式近似、缩放、Gaussian 比较或图活动量假设。一般小比分路径近似也已单独形式化。

This record maps the reorganized bilingual manuscript to the companion Lean proof. It records source correspondence, including alternative sufficient intermediate estimates. It is not a new build certificate or a claim that every displayed intermediate constant is formalized verbatim.

The formal-source baseline is commit `8ea3fcffcc12b6a06294ba7559885b439eda3cac`. The proof sources and historical verification records are unchanged by the manuscript reorganization. All theorem names below are in the namespace `TournamentHamiltonian`.

## Section migration

| Previous manuscript | Revised manuscript | Content |
|---|---|---|
| §1 | §1 | Main theorem and proof roadmap |
| §2.1 | §2.1 | Matrices, scores and spectral factors |
| §2.2 | §2.2 | Positive convolution and uniform long tail |
| New explanation | §2.3 | Why the spectral ratio controls small-score paths |
| §2.3 | §2.4 | Operator cap and convex spectral packing |
| §5.1 | §3.1 | Paired nonprincipal permanent input, proved in §6.4 |
| §5.2–5.5 | §3.2–3.5 | High variance, exceptional vertices and dense score absorption |
| §6 | §4 | Small-score path approximation and carousel lower bound |
| §3 | §5 | General permanent approximation; explicit error budget at the end |
| §4 | §6 | Scaling, Gaussian deletion and restoration |
| §7.2 | §7 | Questions not settled by the theorem |
| §7.1, §7.3, §7.4 | Appendix A | Verification, provenance and disclosure |

The ordering change puts the main implication chain before the technical proofs of its analytic inputs. The inputs remain stated with their hypotheses and proved later; no new mathematical assumption is introduced.

## Objects and quantifier order

- `Tournament n`, `IsHamiltonian`, `pathCount`, `maxPaths`, `meanPaths`, `lowerConstant`, and `MainBound` are defined in [Definitions.lean](../../formalization/TournamentHamiltonian/Definitions.lean). Paths are not identified with their reversals. `MainBound` chooses one real K≥0 and one integer n₀≥2 before quantifying over all n≥n₀
- The paper's V corresponds to `degreeVariance`; τ corresponds to `scoreVariance`. Its Dₙ and ρₙ correspond to `gaussianFactor` and `spectralRatio`; [SkewSpectrum.lean](../../formalization/TournamentHamiltonian/SkewSpectrum.lean) proves the determinant and paired-frequency identities
- The general permanent theorem fixes C≥0 and 0≤q<1 before dimension and matrix. It applies to arbitrary real doubly centred kernels with the stated entry and Euclidean operator bounds, without positivity, symmetry or normality assumptions
- The paired minor theorem fixes the score cap and logarithmic-window constants before choosing its common threshold. The two deletion sets are independent, subject only to equal cardinality
- Lemma 6.4 fixes B₀>0 before C_err, δ and N₀, then quantifies over n, tournament and independent deletion sets of equal size t≤B₀ log n. If η=(d+t+1)²/n≤δ, its relative error is at most C_errη. This finite uniform form follows from `adjacency_nonprincipal_small_score_uniform` in [UniformSmallScoreMinor.lean](../../formalization/TournamentHamiltonian/UniformSmallScoreMinor.lean), with the fixed smallness threshold chosen to imply its variance and logarithmic-error hypotheses; it does not expand the logarithmic deletion window
- For the small-score path theorem, one absolute error constant works for every nonnegative envelope d(n) with d(n)/√n→0. The eventual threshold may depend on that envelope; after it is chosen the estimate applies to every tournament whose scores are bounded by d(n). No condition d(n)log(n)=o(√n) is imposed

## Principal claims and formal entry points

| Revised part | Mathematical claim | Lean declarations and source |
|---|---|---|
| Theorem 1.1 | Actual maximum-path bound with common K and n₀ | `mainBound`, assembled from `maxPaths_lower_uniform` and `maxPaths_upper_uniform`, in [MainBound.lean](../../formalization/TournamentHamiltonian/MainBound.lean) |
| §2.1 | Exact adjacency/sign conventions and score mass | `twice_adjacency`, `signMatrix_skew`, `score_sum_zero`, `signMatrix_total_sq` in [Definitions.lean](../../formalization/TournamentHamiltonian/Definitions.lean) |
| §2.1 | Paired spectrum and determinant factors | `pairedMasses_sum`, `gaussianFactor_complex_eq_inverse_det`, `spectralRatio_eq_paired_product`, `determinantRatio_eq_spectralRatio` in [SkewSpectrum.lean](../../formalization/TournamentHamiltonian/SkewSpectrum.lean) |
| Lemma 2.1 | Exact positive path convolution | `pathCount_eq_positive_convolution` in [PathConvolutionGenerating.lean](../../formalization/TournamentHamiltonian/PathConvolutionGenerating.lean); `complementAdjacency_eq` in [PathConvolution.lean](../../formalization/TournamentHamiltonian/PathConvolution.lean) retains diagonal loops in the complement |
| §2.2 | Positive minor weights, summable moments and uniform path tail | `principal_weight_pos`, `principal_weight_le_rpow`, `subsetMoment_summable`, `longConvolution_eventually_small` in [PositiveDeterminant.lean](../../formalization/TournamentHamiltonian/PositiveDeterminant.lean), [Hadamard.lean](../../formalization/TournamentHamiltonian/Hadamard.lean), [SubsetWeights.lean](../../formalization/TournamentHamiltonian/SubsetWeights.lean), [NormalizedConvolution.lean](../../formalization/TournamentHamiltonian/NormalizedConvolution.lean) |
| Lemma 2.2 (§2.4) | Cotangent cap and packed spectral bound | `signMatrix_complex_opNorm_le_cot`, `transitive_cot_lt_two_mul_div_pi` in [TransitiveCotSpectrum.lean](../../formalization/TournamentHamiltonian/TransitiveCotSpectrum.lean); `spectralRatio_le_upperConstant` in [OperatorCap.lean](../../formalization/TournamentHamiltonian/OperatorCap.lean) |
| Lemma 3.1 (§3.1; proof §6.4) | Uniform paired nonprincipal permanent estimate | `adjacency_nonprincipal_gaussian_uniform_log` in [UniformPairedPermanentGaussian.lean](../../formalization/TournamentHamiltonian/UniformPairedPermanentGaussian.lean) constructs scaling, Gaussian comparison and activity estimates internally |
| Lemma 3.2 and §3.2 | High-variance tournaments have H/μ=o(1/n) | `adjacency_permanent_le_stirling_variance` (m≥3; m=1,2 have zero permanent) in [StirlingNormalization.lean](../../formalization/TournamentHamiltonian/StirlingNormalization.lean), then `highVariance_pathCount_eventually_small` in [HighVariance.lean](../../formalization/TournamentHamiltonian/HighVariance.lean) |
| §3.3 | Exceptional vertices eventually imply H<μ | `permanent_four_blocks_by_size` in [FourBlockPermanent.lean](../../formalization/TournamentHamiltonian/FourBlockPermanent.lean); `exists_uniformExceptionalCoreMinorBound`, `actual_largeScore_eventually_lt_mean` in [ActualExceptionalExclusion.lean](../../formalization/TournamentHamiltonian/ActualExceptionalExclusion.lean) |
| §3.4 | Full score penalty retained through weighted summation | `paired_shortConvolution_spectral_of_principal_bound`, `actual_full_score_factor_uniform` and `actual_paired_shortConvolution_uniform_upper` in [PairedShortSpectral.lean](../../formalization/TournamentHamiltonian/PairedShortSpectral.lean), [FullScoreAbsorption.lean](../../formalization/TournamentHamiltonian/FullScoreAbsorption.lean), [UniformPairedShortUpper.lean](../../formalization/TournamentHamiltonian/UniformPairedShortUpper.lean) |
| §3.5 | Three classes give an unconditional uniform upper bound | `actual_uniform_pathCount_upper` in [ActualUniformUpper.lean](../../formalization/TournamentHamiltonian/ActualUniformUpper.lean) |
| Theorem 4.1 | Uniform whole-path approximation for d=o(√n) | `small_score_pathCount_spectral_approximation_eventually` in [GeneralSmallScoreAsymptotic.lean](../../formalization/TournamentHamiltonian/GeneralSmallScoreAsymptotic.lean); its finite-window input is `score_pathCount_spectral_approximation_uniform` |
| §4 | Actual carousel constructions for both parities | `carouselTournament_residue_arc`, `carouselTournament_score`, `evenCarouselTournament_score` in [Carousel.lean](../../formalization/TournamentHamiltonian/Carousel.lean); `carousel_spectralRatios_error_bound` in [SkewSpectrum.lean](../../formalization/TournamentHamiltonian/SkewSpectrum.lean) |
| Corollary 4.2 | Two-sided carousel path approximation and maximum-path lower bound | `unit_score_pathCount_spectral_approximation_uniform` in [UnitScorePathsApproximation.lean](../../formalization/TournamentHamiltonian/UnitScorePathsApproximation.lean), together with `carousel_spectralRatios_error_bound`; `maxPaths_lower_uniform` in [CarouselPathLower.lean](../../formalization/TournamentHamiltonian/CarouselPathLower.lean) gives the resulting extremal lower bound |
| Theorem 5.1 | General uniform permanent approximation | `uniform_permanent_approximation_from_matrix_bounds` in [UniformPermanentUnconditional.lean](../../formalization/TournamentHamiltonian/UniformPermanentUnconditional.lean) |
| §5 | Genuine coefficients, core decomposition and compression counts | `normalized_coeff_distinct_coordinates`, `distinctCoordinateSum_div_gaussian_excess_convolution`, `actualCoreFiberEncoding_injective`, `actualCoreFiberEncoding_weight`, `encodedCoreData_finite_window_weight_le` in [PermanentExpansion.lean](../../formalization/TournamentHamiltonian/PermanentExpansion.lean), [GaussianCoreExcessCoefficients.lean](../../formalization/TournamentHamiltonian/GaussianCoreExcessCoefficients.lean), [CoreEncodingInjectivity.lean](../../formalization/TournamentHamiltonian/CoreEncodingInjectivity.lean), [CoreEncodingCount.lean](../../formalization/TournamentHamiltonian/CoreEncodingCount.lean) |
| Lemma 5.2 (§5.3) | All-degree fixed-excess activities, including 710, 3/2 and 10/3 | `actualCoreExcessCoefficient_tsum_activity_le`, `actualCoreExcessCoefficient_one_tsum_le` in [ActualCoreActivitySeries.lean](../../formalization/TournamentHamiltonian/ActualCoreActivitySeries.lean) |
| Lemmas 5.3 and 5.4 (§5.5) | Polarization, PSD estimate and actual polynomial tail | `permanent_polarization`, `complex_posSemidef_permanent_le_homogeneous`, `actual_normalized_permanent_floor_tail_bound` in [PermanentPolarization.lean](../../formalization/TournamentHamiltonian/PermanentPolarization.lean), [CircularPSDComparison.lean](../../formalization/TournamentHamiltonian/CircularPSDComparison.lean), [ActualPermanentFloorTail.lean](../../formalization/TournamentHamiltonian/ActualPermanentFloorTail.lean) |
| Proposition 5.5 (§5.6) | Explicit error budget | `actual_permanent_approximation_of_core_activities` in [PermanentApproximationFromActivities.lean](../../formalization/TournamentHamiltonian/PermanentApproximationFromActivities.lean) proves an alternative sufficient budget. Its Gaussian recovery constant differs from the displayed K_G; the literal proposition is not claimed to be the Lean statement |
| Lemmas 6.1 and 6.2 (§6.1) | Actual local scaling, displacement, capacity and same-witness quantitative controls | `exists_local_scaling`, `exists_local_scaling_witness`, `exists_normalized_local_scaling_witness` in [LocalScalingEstimates.lean](../../formalization/TournamentHamiltonian/LocalScalingEstimates.lean) and [LocalScalingComplete.lean](../../formalization/TournamentHamiltonian/LocalScalingComplete.lean) |
| Lemma 6.3 (§6.2) | General deletion, centering and Frobenius log-Lipschitz bounds | `gramGaussian_deletion_bound`, `gramGaussian_centering_bound`, `gramGaussian_log_lipschitz` in [GramDeletion.lean](../../formalization/TournamentHamiltonian/GramDeletion.lean), [GramCentering.lean](../../formalization/TournamentHamiltonian/GramCentering.lean), [GramLipschitz.lean](../../formalization/TournamentHamiltonian/GramLipschitz.lean) |
| §6.2 | Explicit tournament deletion error (24t+18τ+11)/n | `tournament_gaussian_deletion_loss` in [TournamentGaussianLoss.lean](../../formalization/TournamentHamiltonian/TournamentGaussianLoss.lean), assuming n≥4, |I|=|J|=t and 2t≤n |
| §6.3 | True preconditioning mass cancellation and Gaussian cost | `preconditionedTournamentDensity_mass` in [PairedPreconditioning.lean](../../formalization/TournamentHamiltonian/PairedPreconditioning.lean); `exists_preconditioned_scaling_gaussian_cost_uniform_log` in [UniformGaussianCost.lean](../../formalization/TournamentHamiltonian/UniformGaussianCost.lean) |
| Lemma 6.4 (§6.5) | Two-sided actual small-score minor approximation | `adjacency_nonprincipal_small_score_uniform` in [UniformSmallScoreMinor.lean](../../formalization/TournamentHamiltonian/UniformSmallScoreMinor.lean) |

The small-score minor theorem has explicit finite-domain premises τ≤1 and a small quadratic error budget. The asymptotic theorem in Section 4 discharges them internally from d(n)=o(√n); they are not extra assumptions on the final result. Likewise, intermediate lemmas taking `ActualCoreActivities` as input are followed by actual matrix-bound proofs of that predicate.

## Alternative intermediate estimates

The following differences explain why final-statement correspondence does not mean a literal translation of every displayed proof line.

1. Gaussian factorial recovery uses the Lean bound K̃_G=Γ(R)r(1+r)/(1−r)³, r=σ/R, rather than the displayed derivative-based K_G. The definitions of R, σ, W, D=710W³, T₁ and the chosen window fraction agree. See [GaussianFactorialRecovery.lean](../../formalization/TournamentHamiltonian/GaussianFactorialRecovery.lean)
2. High-variance deletion uses `(7/8)V−kn²/4−2nk²` as a lower bound for retained variance. The resulting n^(−13/8) permanent penalty still gives a normalized short contribution O(n^(−9/8))=o(1/n), sufficient for the same exclusion. See [DegreeDeletion.lean](../../formalization/TournamentHamiltonian/DegreeDeletion.lean) and [HighVariance.lean](../../formalization/TournamentHamiltonian/HighVariance.lean)
3. Exceptional exclusion uses D<2 and det(I+S/N)<5/3 rather than retaining the sharper common-core factor. The multiplicative bound `(10/3)4^(−f)exp(E+2K²/n)` controls only `disjointShortConvolution / meanPaths`. The short terms meeting F and the long terms are added separately, so the full bound is `(10/3)4^(−f)(1+ε_n)+δ_n`, with both errors uniform and tending to zero. Since f may grow, the additive error is not absorbed into the multiplicative factor. For f≥1, the formal budget is `(10/3)(1/4)(21/20)+1/25+1/25=191/200<1`. This is Equation (3.1) in both manuscripts. See `disjointShortConvolution_le_crude` and `exceptional_pathCount_lt_mean_of_crude_bound` in [CrudeExceptionalExclusion.lean](../../formalization/TournamentHamiltonian/CrudeExceptionalExclusion.lean)
4. Dense weighted inflation uses positive principal-minor moments rather than the nuclear-norm perturbation argument. The difference is controlled by `n⁻¹ Σ_i(w_i−1) Σ_k kW^kw_k`, and the score penalty remains outside the complete sum. See [WeightedPrincipalGenerating.lean](../../formalization/TournamentHamiltonian/WeightedPrincipalGenerating.lean)
5. The small-score minor proof reuses paired preconditioning and the same balancing witness, bounding every restoration term at the required quadratic rate, rather than making a separate unpaired construction
6. The local fixed-point implementation keeps the Hessian perturbation in the remainder and applies the balanced inverse. The tournament application chooses pre-scaling gap 9/10 and final gap 19/20, which suffice without the optional sharper 4/5 estimate
7. Lean uses |U|<kₙ for short terms and |U|≥kₙ for the tail; the original prose uses ≤kₙ and >kₙ. This is a harmless boundary-layer convention difference
8. The PSD permanent proof uses finite phase averages and exponential radial moments, and polarization uses block-Gram positivity. These prove the same inequalities as the tensor and circular-Gaussian presentation

Signed switching in the carousel argument preserves the spectral factor; it is not used to claim that switching preserves Hamiltonian path counts. The cap-plus-mass optimization is a spectral relaxation, not a realization theorem for its maximizing vector.

## Verification provenance and current checks

The project pins Lean 4.34.1 and Mathlib v4.34.1; [lake-manifest.json](../../formalization/lake-manifest.json) pins Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The stored [Lean verification record](../../formalization/audit/lean-verification.json) is dated `2026-10-09T07:19:29.938467+00:00`. It records exit code zero for the complete build, transitive axiom audit and independent `MainBound` type check. The build reports 4022 jobs. The audit reports 3674 theorem constants in the project namespace, including generated lemmas; only `propext`, `Classical.choice` and `Quot.sound` are allowed.

For the present source review, all 246 hashes in that record were recomputed and matched. An independent static import traversal reached all 240 component modules, as well as the root import and audit modules. Every theorem name in the cumulative proof ledger resolves to a declaration. No project placeholder or custom-axiom declaration was found in the source scan. No fresh local Lean build was run: Lean and Lake were unavailable on PATH. These are distinct kinds of evidence.

The historical [GitHub Actions run 37899160028](https://github.com/LStar404/tournament-hamiltonian-paths/actions/runs/37899160028) belongs to the supplied base revision. It is not a new run for the reorganized manuscript.

[verify_lean.py](../../formalization/verify_lean.py), with `--require-main`, runs the build, [Audit.lean](../../formalization/Audit.lean), an explicit theorem-type check, and project-source import coverage. The [CI workflow](../../.github/workflows/verify.yml) also runs four finite diagnostic entry points and saves their records. It does not automatically check the equivalence of edited prose to Lean, bilingual translation, bibliography accuracy, PDF layout, or every displayed intermediate constant. Finite diagnostics do not prove the all-order theorem.

The old source hashes and `proof-status.json` retain their historical role. This dated document adds the correspondence for the reorganization without rewriting that history.

## Recomputed proof-source anchors

The canonical comparison manifest consists of sorted lines `SHA256  relative-path`, each ending in a newline, for the 246 entries of the stored record. Its recomputed SHA-256 is `968cfbe44c298f095f2ba03168fac0a7eb7b9909e586a5d1576ea9d0f79cbbbf`.

| File under formalization | Recomputed SHA-256 |
|---|---|
| TournamentHamiltonian/Definitions.lean | `27f18e9989758e93c7cf738b62a587cc8b12d1345233bd7c813ec0ce5fb31293` |
| TournamentHamiltonian/MainBound.lean | `edec94852fe8ba31700c2145fd65839a9e2a7e43398237d3a1c1506907606bcc` |
| TournamentHamiltonian/GeneralSmallScoreAsymptotic.lean | `b433fc510ff17ed8960be37956d99ad0e4f8ba3a5430613b431bb1bbd2312719` |
| TournamentHamiltonian/UniformPermanentUnconditional.lean | `81abb9cfc6e1fe96f504ed0bc6c5acef58d6e5b5fa4e1fd8a4576fe05bf49404` |
| Audit.lean | `5e1acf7fdc736b4352b9f8264c706c29c1c5c8a15dd3720037b728e3edca259d` |
| verify_lean.py | `c934a17f79578376eecc954d857ec3338b4816a8fd6ee278c336e180dbba1cb0` |
