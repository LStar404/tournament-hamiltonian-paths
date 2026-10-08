# Independent audit: global constant-factor Hamilton-path reduction

Date: 2026-10-08. Scope: Sections 3–8 of `tournament_operator_packing_global_path_bound_2026-10-08.md` and the nonprincipal Gaussian/permanent interfaces on which those sections rely. This audit does not certify the upstream uniform permanent theorem or the local scaling-existence theorem; those are explicit conditions and are being reviewed separately.

## Verdict

Conditional on the stated uniform zeroth-order permanent theorem and the stated local real-scaling interface, the global reduction is mathematically consistent. I found no counterexample or fatal gap in the spectral cap, convex packing, variance exclusion, exceptional-vertex exclusion, weighted short-subset summation, or final score-penalty absorption. The finite tests are not needed to infer the asymptotic statement; the all-order estimates below explain the relevant uniformity.

The draft is not yet a stand-alone paper proof: several steps should be expanded as below. In particular the four-block normalization has a factor `2^s`, and the short-subset error needs to be accumulated before removing the common score product. Both are controllable by the estimates already asserted in the draft; neither changes the claimed conclusion.

## 1. Spectral cap and packing

For a real skew tournament matrix S and a complex vector z, simultaneously conjugate S by a signed permutation and apply the same transformation to z. This preserves the Rayleigh quotient of iS. Every nonzero coordinate phase can be moved into [0,pi), then put in increasing order. Consequently Im(conj(z_i)z_j) is nonnegative for i<j, and comparison of the signs S_ij gives z* iS z <= z* (-iT) z, with T the upper-triangular-positive transitive skew matrix. The eigenvalues of iS are symmetric about zero, so its maximum eigenvalue is ||S||_op. The determinant polynomial of T gives ||T||_op = cot(pi/(2n)). This proves the operator-norm cap for every n, not merely for tested orders.

Write x_j=lambda_j^2/n^2 for one member from each positive/negative frequency pair. Then sum_j x_j=(n-1)/(2n), and x_j<4/pi^2. On [0,1), phi(x)=log((1+x)/(1-x)) is increasing and convex. Pushing mass to a capped coordinate, a single residual coordinate, and zeros is a rigorous convex maximization; increasing the mass budget to 1/2 yields the stated C_*. If the original number of coordinates is too small, adjoining zeros only enlarges the relaxed feasible set. No realizability of the packed frequency vector is claimed or required.

## 2. Uniform determinant weights and long terms

The symmetric part of I+A[U] is (I+J)/2, hence its determinant is positive. Hadamard followed by arithmetic–geometric mean gives det(I+A[U]) <= ((k+1)/2)^(k/2).

For w_k=2^k((k+1)/2)^(k/2)/k!, Stirling gives

    log(c^k w_k) = -(k/2)log k + O_c(k).

Thus all fixed polynomial moments of c^k w_k are finite, and with K_n=ceil(4 log n/log log n), sum_{k>K_n} c^k w_k = n^(-2+o(1)). The generic tournament permanent estimate C sqrt(m+1)m!/2^m then makes the normalized long-path contribution n^(-3/2+o(1))=o(1/n), uniformly over all tournaments. Orders m=0,1,2 are covered by the empty-matrix convention and an enlarged universal constant.

## 3. Discrete concavity and the variance penalty

Let f(k)=log(k!)/k for integers k>=1 and mu=(m-1)/2. The displayed second difference in the draft is correct. AM–GM gives log k-f(k-1)>=log 2, and k log(1+1/k)<log 3, so

    2f(k)-f(k-1)-f(k+1) >= 1/[4k(k+1)] >= 1/(4m^2)

for every interior degree k in {2,...,m-2}. Therefore the integer-point linear interpolation of g(k)=f(k)+k^2/(8m^2) is concave on [1,m-1]. If all degrees are positive, Jensen at mu gives

    sum_i f(d_i) <= m f_tilde(mu) - V/(8m^2) + 1/(32m),

where f_tilde is linear interpolation and the last term accounts for a half-integer mean. For an integer mean it can be dropped. The balanced Stirling estimate exp(m f_tilde(mu)) <= C sqrt(m+1)m!/2^m proves the asserted Brégman variance bound. A zero outdegree makes the permanent zero and is handled separately.

After deleting k vertices, every surviving centered degree changes by at most k/2. Removing the k old squared deviations costs at most kn^2/4; Cauchy–Schwarz bounds the cross term by k sqrt(nV). This yields exactly the stated deletion inequality.

When V>=16n^2 log n and k<=K_n, the relative variance loss is o(1), uniformly. The permanent penalty is at most exp(-(2-o(1))log n). Together with sqrt n and the summable determinant weights, the entire short contribution is n^(-3/2+o(1)); adding long terms gives o(1/n). The threshold 16, rather than a casually smaller threshold, is sufficient for this conclusion.

## 4. Exceptional vertices: complete normalization

The low-variance condition makes the number f of degrees outside [0.05(n-1),0.95(n-1)] at most O(log n). Deleting them leaves a core of size N=n-f whose score fractions have absolute value below 0.95 for all sufficiently large n. Indeed a surviving full score had absolute value at most 0.9(n-1) and changes by at most f. The core score-square sum is O(log n).

For core paired weights ell_i=(1+a_i)^(-1), r_i=(1-a_i)^(-1), the total absolute displacement of both weight vectors from one is O(sqrt(N log n)). Every cross-neighbor sum is thus bounded by N(q_x+beta) or N(1-q_x+beta), with beta=O(sqrt(log n/n)). Here q_x is the actual core win fraction of the exceptional vertex, differing from its full win fraction by O(f/n).

Let s denote the number of internally matched exceptional rows and columns, and t=f-s. The core permanent deletes t rows and t columns, usually different sets. Its omitted paired factors are ell on deleted rows and r on deleted columns; these are precisely the factors used by the two cross-neighbor sums. Summing matchings can safely drop distinctness constraints, giving product bounds for the cross sums.

After division by (N+f)!/2^(N+f), the complete scalar per summand is

    2^s * N^(2t) * (N-t)!/(N+f)!
      = (2/N)^s exp(O(f^2/N)).

The factor 2^s is real and must be displayed in the paper, even though it is covered by the draft's final exp(O(f^2/N)). Put L_n=2+o(1), c_n=0.19+o(1). If R,C are the exceptional internal row/column sets, both of size s, and h=|R intersect C|, then

    product_{x notin R} u_x product_{y notin C} v_y
      <= c_n^(f-2s) L_n^(2s) (c_n/L_n^2)^h
      <= c_n^(f-2s) L_n^(2s).

This identity explains why the estimate is still valid when f-2s<0. With binom(f,s)^2 s! <= f^(2s)/s!, summation gives the explicit upper factor

    c_n^f exp(O(f^2/N)) exp(2 L_n^2 f^2/(c_n^2 N)).

The nonprincipal permanent error is o(1), uniformly over t<=f=O(log n), because its displayed budget is O((log n)^(3/2)/sqrt n + (log n)^2/n). Repeating the argument after a short core subset is deleted preserves all constants. Replacing the new core Gaussian by the original one costs O(k/n) in logarithm by deletion and scale comparison.

Subsets touching F need only be controlled to o(1): their fraction among k-subsets is at most fk/n, so the generic permanent bound and the first moment of w_k give O(f/sqrt n). This weaker error is sufficient, since the total bound for f>=1 is at most C_*/4+o(1)<1. It is not claimed to be an O(1/n) estimate for those tournaments.

## 5. Short-subset accumulation with the common product retained

Set G=100/19, delta_n=sqrt(tau/n)+1/n, and

    c_k=(2/n)^k sum_{|U|=k} det(I+A[U]) product_{i in U} g_i.

Then 0<=c_k<=G^k w_k and c_0=1. For k<=K_n, the exponent in the per-minor bound together with the falling-factorial restoration is

    r_k=R_{tau,k}+log(n^k/(n)_k)
        <= C [k sqrt(tau/n)+(k+k^2)/n]
        <= C delta_n(k+k^2).

Uniformly for tau<=C_0 log n, max_{k<=K_n} r_k=o(1). Hence e^(r_k)-1<=2r_k for all sufficiently large n. Summing against c_k gives

    sum_{k<=K_n} c_k e^(r_k)
      <= sum_{k>=0} c_k + C delta_n sum_{k>=0}G^k w_k(k+k^2)
      <= (sum_{k>=0}c_k) exp(C' delta_n).

The last step uses sum c_k>=1. It is crucial that the common Gamma remains outside this entire inequality. This proves the claimed relative, rather than unpenalized additive, error without inserting a worst-case K_n factor into the final error rate.

## 6. Weighted generating determinant and score absorption

Let W=I+(2/n)(I+A). Its symmetric part is at least I, so ||W^(-1)||_op<=1. The weighted matrix is W+Delta, with

    Delta=(2/n)diag(g-1)(I+A).

Decompose Delta as a sum of rank-one row matrices. Each row of I+A has norm at most sqrt n, while sum_i(g_i-1)<=C tau. Thus ||Delta||_*<=C tau/sqrt n. The determinant inequality |det(I+E)|<=exp(||E||_*) and positivity of the weighted principal-minor expansion give

    det(W+Delta) <= det(W) exp(C tau/sqrt n).

The unweighted rank-one identity gives det(W)<=2e det(I+S/n). More generally for a core of size N<=n the same argument gives det(I_N+(2/n)(I_N+A_M))<=2e det(I_N+S_M/N).

Combining the factors before removing Gamma gives the exponent displayed in equation (13). For tau<=C_0 log n, the ratios (1+tau)/n and (sqrt(tau)+1)/sqrt n tend uniformly to zero. Thus all error terms except the constant 1/n and sqrt(tau/n) consume at most tau/4. Young bounds C sqrt(tau/n)<=tau/4+C^2/n. This leaves -tau/2+C'/n. Together with rho<=C_* and the o(1/n) long tail it proves the claimed upper bound uniformly over the no-exceptional class. The other classes are already below one and therefore below C_*+O(1/n).

## 7. Matching lower scale and limitations

The small-score path formula is an upstream implication of the same permanent/scaling interfaces plus the positive convolution. Applying it to odd carousel tournaments (maximum score zero) and one-vertex deletions of the next odd carousel (maximum absolute score one) gives L+O(1/n). Their spectral ratio agrees with the transitive skew ratio by signed-permutation similarity; that similarity must not be claimed to preserve path counts.

The spectral ratio itself expands as L-L/n+O(1/n^2). The current path approximation has O(1/n) error and therefore does not determine the first correction coefficient of the actual carousel path count.

This audit verifies only the full-graph reduction conditional on the two upstream analytic inputs. It does not prove sharp L as a global spectral upper constant, finite P(n), carousel uniqueness, an effective starting order, or an unconditional theorem if the upstream permanent/scaling audits find a gap.

## Primary-source checks

Alon, Lemma 2.1, states the row-degree Brégman permanent bound: https://web.math.princeton.edu/~nalon/PDFS/hamilton.pdf .

Irving–Omar, Proposition 2, is the determinant/permanent Hamilton-path convolution using the complement adjacency matrix. Its complement includes diagonal entries; for a tournament it is I+A^T, giving precisely the positive convolution used here: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i4p43/pdf/ .

No finite enumeration is offered as proof of an asymptotic constant or threshold in this audit.
