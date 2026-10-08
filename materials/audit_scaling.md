# Independent audit: scaling, nonprincipal deletion, and small-score approximation

Date: 2026-10-08. Auditor scope: local analytic interfaces, not new extremal searches.

## Verdict

The scaling and deletion chain passes the independent mathematical review described below. No incorrect sign, omitted restoration factor, unjustified use of skew symmetry for a nonprincipal submatrix, or loss of uniformity was found.

The permanent applications are explicitly conditional on the uniform dense permanent theorem, which is being audited separately. The passage from permanents to Hamilton paths uses the published tournament convolution of Irving and Omar; it is not a generic directed-graph convolution.

The conclusion certified by this audit is the correctness of the local interfaces, including the small-score permanent formula and its stated implication for paths once those two inputs are supplied. This audit alone does not certify the all-tournament upper bound, the leading spectral maximum, a finite exact value of the extremal function, or an extremal classification.

## Files read completely

- `outputs/tournament_nonprincipal_gaussian_deletion_audit_2026-10-08.md`.
- `outputs/tournament_explicit_local_scaling_lemma_2026-09-27.md`.
- `outputs/tournament_preconditioned_nonprincipal_scaling_2026-10-04.md`.

The positive convolution and tail passage in Section 4 of the current global proof were also checked against the small-score argument.

## 1. Local scaling existence

The gauge-fixed inverse in Section 2 of the explicit scaling note is correct. On the two constant directions its eigenvalues are respectively 1/2 and 1; on the two zero-sum spaces it is the usual inverse of the block operator with diagonal identity and off-diagonal centered kernel. The rank-one subtraction of one quarter of each constant block is necessary and has the correct sign.

The inverse one- and infinity-norm bound follows from the entry estimates for the resolvents and off-diagonal inverse block. The Hessian perturbation is at most three times the marginal infinity error. The stated epsilon threshold makes the nonlinear fixed-point map contractive by at most 1/2 on the stated gauge ball. Consequently the finite real scaling potentials are constructed, rather than inferred from numerical convergence or a support guess.

For nonnegative matrices the constructed balance is genuinely doubly stochastic and retains the support. The entry bound and the fixed centered operator gap follow from the same explicit estimates. The signed-matrix branch is not mislabeled as a nonnegative scaling.

The vague last sentence about arbitrary fixed higher derivatives in the old note is not needed for any theorem in the proposed zero-order paper and should not be used as an unproved substitute for a higher-order expansion.

## 2. Euclidean displacement and capacity

For the nonnegative input, write the convex scaling potential as the sum of scaled entries minus the sum of the two potential vectors. Along the segment from the origin to the balancing potential, its Hessian is bounded below by a fixed multiple of the balanced endpoint Hessian. The latter has a fixed positive lower eigenvalue on the gauge space.

Integrating the gradient gives the Euclidean potential bound by the Euclidean marginal error. The dense entry bound then gives a Frobenius matrix displacement smaller by the square root of the matrix dimension. These are the bounds needed in the paper; merely using the infinity potential bound would not be sufficient for the small-score error rate.

For a mass-normalized matrix, the total potential is nonnegative and is bounded above by a constant times the squared Euclidean marginal error. For a matrix of arbitrary mass, the exact correction is dimension times the logarithm of dimension divided by mass. Its sign need not be positive. The notes retain this correction, and the safe permanent upper bound has the correct direction.

## 3. Gram deletion and centering

The Gaussian determinant deletion inequality is valid for arbitrary real, possibly nonnormal and rectangular matrices. First deleting rows produces a positive semidefinite difference in the column Gram matrix. Deleting columns next uses the row Gram matrix. This prevents the unjustified square-root loss that would arise from a crude Frobenius comparison of zero-padded matrices.

The same argument gives the two-sided centering inequality. Both remaining all-one directions are included. No skew-symmetry assumption is made for a nonprincipal submatrix.

The logarithmic determinant Lipschitz bound used for subsequent genuine scaling perturbations follows from the Gram trace-norm bound and the fixed gap. It is not used in place of the sharper deletion inequality.

For the tournament kernel Y=(S-I)/(n-1), the claimed operator bound is correct. Its squared gap is exactly n(n-3)/(2(n-1)^2) under the stated conservative bound. The deletion-and-centering budget simplifies to the expression displayed in the notes. For m at least n/2, the coefficients 24, 18, and 8 are valid. The full-kernel normalization comparison has a positive semidefinite Gram difference and is bounded by 43/(4n), a conservative valid constant. Comparing the two nonnegative losses from the same full kernel gives the absolute bound with 24t+18 tau+11, not their sum.

## 4. Paired preconditioning and nonprincipal restoration

The paired mass identity is correct. It follows by expanding ell=1-v+w and r=1+v+w, using the zero sum of the scores and the identity 1^T S v=-(n-1) sum w_i. The scalar mass discrepancy has no first-order contribution.

The preconditioned marginal formulas, Euclidean bounds, and Frobenius perturbation follow directly from the dense row/column norms. The subsequent deletion mass formula contains the necessary subtraction t^2/n. Its sign and the scaling n/m are correct.

The centered normalized minor is the compression of Y plus the compression of the preconditioning perturbation, multiplied by the exact scalar n^2 divided by the two masses. This scalar has n/m as its leading value when t is positive. The proof does not forget this normalization. The centered gap tends uniformly to at most 1/sqrt(2), and the constructed true scaling changes it only by a term tending to zero.

The permanent restoration has the full factor Gamma times the product of ell over deleted rows times the product of r over deleted columns. These row and column factors must not be interchanged. Combining the mass, capacity, Gaussian, and factorial restorations gives exactly the upper exponent required by the main proof:

$$
K\left[\mathcal M_\tau+\sqrt{\tau/n}+(t+1)/n+t\sqrt{\tau/n}+t^2/n\right].
$$

The correction from general nonprincipal deletion is linear in t/n, not a square root.

## 5. Small-score formula and paths

For d equal to the maximum absolute score and d=o(sqrt(n)), direct normalization without paired preconditioning gives marginal infinity error O((d+t)/n), Euclidean marginal error O((d+t)/sqrt(n)), and mass error O(t(d+t)/n). Genuine scaling therefore moves the matrix in Frobenius norm by O((d+t)/n), with absolute capacity error O((d+t)^2/n).

The exact restoration factor is [m(n-1)/(2n)]^m. Together with the uniform permanent theorem and Gaussian comparison, it yields the relative error O((d+t+1)^2/n), uniformly over all distinct deleted row and column sets of logarithmic size.

For clarity, the paper should state this in the regime d+t+1=o(sqrt(n)), or equivalently impose a fixed sufficiently small upper bound on (d+t+1)^2/n when interpreting the quantitative big-O statement. The constants are independent of the particular graph and deleted sets; this does not furnish a useful finite starting order.

The path argument is also correct under the published tournament convolution. Its determinant weights are positive. Normalized short terms have total error controlled by the finite second moment of the weights w_k, rather than by the largest cutoff k. Thus no extra logarithmic factor is needed. The long terms are o(1/n) under the universal permanent bound. The final rank-one determinant comparison is valid because the skew part contributes zero to the real quadratic form. This gives H/mu=rho+O((d+1)^2/n).

The odd circular construction has zero scores. Deleting one vertex from the next odd construction has maximum absolute score one. Switching and permutation preserve their spectra, not their Hamilton path counts. Both parities have the stated exact transitive spectral ratio; its coefficient -L/n is only a spectral coefficient, not an asserted Hamilton-path coefficient.

## 6. Read-only reruns

Two existing verifiers were rerun without writing any file. Both returned exit code 0.

- Explicit scaling: 12 exact gauge-inverse identities and 6 known scaling solutions in the stated sufficient domain.
- Nonprincipal deletion: 267 general deletion and 267 centering comparisons; 693 tournament Gaussian comparisons, including 396 nonprincipal cases; 635 scalar restorations; 56 exact permanent examples and 14 exact path examples.

The latter source hash is `17615a1fb10e3d3222e231c6824a3ebdee35c5ad0593215e27ce3962e9ebcecd`.

These runs support formula-error detection only. No universal asymptotic constant, threshold, or theorem is inferred from finite numerical examples.
