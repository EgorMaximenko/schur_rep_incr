# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables"
# This the new version, with increasing powers.


import time


def partitions_with_bounded_sum(summax):
    plist = []
    for w in range(summax + 1):
        plist += list(Partitions(w))
    return list(sorted(plist))


def partitions_with_bounded_length_and_bounded_sum(nmax, summax):
    plist = []
    for w in range(summax + 1):
        plist += list(Partitions(w, max_length = nmax))
    return list(sorted(plist))


def partitions_with_given_length_and_bounded_sum(n, summax):
    plist = []
    for w in range(summax + 1):
        plist += list(Partitions(w, length = n))
    return list(sorted(plist))


def pol_ring(letter, n):
    varnames = [letter + str(k) for k in range(n)]
    PR = PolynomialRing(QQ, varnames)
    return PR


def pol_vars(letter, n):
    PR = pol_ring(letter, n)
    return vector(PR, n, PR.gens())


# The Sage function 'det' crashes for some symbolic matrices.
# The following simple recursive version is more stable.
# To speed up the function and save memory, we do not create the submatrices explicitly.
# The sum over all permutations is slower because our matrices usually have many zeros.


def det_recur(A, rfirst, cols):
    if rfirst == A.nrows():
        return A.base_ring().one()
    result = A.base_ring().zero()
    s = 1
    for k in cols:
        if A[rfirst][k] != 0:
            newcols = [c for c in cols if c != k]
            result += A[rfirst][k] * det_recur(A, rfirst + 1, newcols) * s
        s = -s
    return result


def my_det(A):
    return det_recur(A, 0, list(range(A.nrows())))


def hom_polynomials(xs, degstop):
    n = len(xs)
    R = parent(xs[0])
    hs = vector(R, degstop)
    if degstop > 0:
        for k in range(degstop):
            hs[k] = xs[0] ** k
        for j in range(1, n):
            hs_prev = hs
            hs[0] = R.one()
            for k in range(1, degstop):
                hs[k] = hs_prev[k] + xs[j] * hs[k - 1]
    return hs


def jacobi_trudi_matrix(la, xs):
    la_len = len(la)
    la_max = la[0] if len(la) > 0 else 0
    R = parent(xs[0])
    hs = hom_polynomials(xs, la_max + la_len)
    hfun = lambda j: hs[j] if j >= 0 else R.zero()
    A = matrix(R, la_len, la_len)
    for j in range(la_len):
        for k in range(la_len):
            A[j, k] = hfun(la[j] - j + k)
    return A


# Construct matrix G_{\la,\ka}(ys) from the paper.

def generalized_confluent_vandermonde_matrix(la, ka, ys):
    n = len(ka)
    N = sum(ka)
    la_ext = la + [0] * (N - len(la))
    R = ys.base_ring()
    A = matrix(R, N, N)
    k = 0
    for p in range(n):
        for r in range(ka[p]):
            for j in range(N):
                mypower = la_ext[N - 1 - j] + j - r
                coef = binomial(la_ext[N - 1 - j] + j, r)
                A[j, k] = coef * (ys[p] ** mypower) if mypower >= 0 else R.zero()
            k += 1
    return A


def confluent_vandermonde_det_formula(ys, ka):
    n = len(ka)
    N = sum(ka)
    R = ys.base_ring()
    result = R.one()
    for j in range(n):
        for k in range(j + 1, n):
            result *= (ys[k] - ys[j]) ** (ka[j] * ka[k])
    return result


def list_with_reps(ys, ka):
    result = [0] * sum(ka)
    k = 0
    for p in range(len(ys)):
        for r in range(ka[p]):
            result[k] = ys[p]
            k += 1
    return result


def schur_rep_via_jacobi_trudi(la, ka, ys):
    xs = list_with_reps(ys, ka)
    return my_det(jacobi_trudi_matrix(la, xs))


def schur_rep_via_generalized_confluent_vandermonde(la, ka, ys):
    numer = my_det(generalized_confluent_vandermonde_matrix(la, ka, ys))
    denom = my_det(generalized_confluent_vandermonde_matrix([], ka, ys))
    return numer / denom


# Here is a slightly more efficient algorithm to construct G_{\la,\ka}(ys).


def binomial_coefs(t, m):
    # compute [C[0], ..., C[m - 1]] where C[k] = binomial(t, k)
    C = vector(ZZ, m)
    C[0] = 1  
    for k in range(1, m):
        C[k] = C[k - 1] * (t - k + 1) / k
    return C


def integer_log2(x):
    # compute floor(log2(x)), i.e.,
    # the maximum of k such that 2 ** k <= x
    y = 1
    k = 0
    while y <= x:
        y = 2 * y
        k += 1
    return k - 1


def binary_powers(a, L):
    # compute [a, a ** 2, a ** 4, a ** 8, ..., a ** (2 ** L)]
    R = a.parent()
    b = vector(R, L + 1)
    c = a
    for j in range(L + 1):
        b[j] = c
        c = c * c
    return b


def binary_expon(B, p):
    # compute a ** p using
    # B = [a, a ** 2, a ** 4, a ** 8, ..., a ** (2 ** L)];
    # we suppose that p < 2 ** (L + 1)
    R = B.base_ring()
    c = R.one()
    q = p
    j = 0
    while q > 0:
        if mod(q, 2) != 0:
            c = c * B[j]
        q = q // 2
        j = j + 1
    return c


def generalized_confluent_vandermonde_matrix_efficient(la, ka, y):
    n = len(ka)
    N = sum(ka)
    K = max(ka)
    la_ext = la + [0] * (N - len(la))
    L = integer_log2(la_ext[0] + N)
    R = y.base_ring()
    C = matrix(ZZ, N, K)
    for j in range(N):
        C[j, :] = binomial_coefs(la_ext[N - 1 - j] + j, K)
    G = matrix(R, N, N)
    k = 0
    for q in range(n):
        B = binary_powers(y[q], L)
        for r in range(ka[q]):
            u = [la_ext[N - 1 - j] + j - r for j in range(N)]
            jlist = [j for j in range(N) if u[j] >= 0]
            jmax = max(jlist, default = -1)
            for j in range(jmax + 1):
                G[j, k] = C[j, r] * binary_expon(B, u[j])
            k += 1
    return G


def schur_rep_via_generalized_confluent_vandermonde_efficient(la, ka, ys):
    numer = my_det(generalized_confluent_vandermonde_matrix_efficient(la, ka, ys))
    denom = confluent_vandermonde_det_formula(ys, ka)
    return numer / denom


# tests


def test_two_matrices(la, ka, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    r0 = generalized_confluent_vandermonde_matrix(la, ka, ys)
    r1 = generalized_confluent_vandermonde_matrix_efficient(la, ka, ys)
    if verbose:
        print(r0)
        print(r1)
    return r0 == r1


def test_schur_rep_three_formulas(la, ka, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    G0 = generalized_confluent_vandermonde_matrix(la, ka, ys)
    G1 = generalized_confluent_vandermonde_matrix_efficient(la, ka, ys)
    matrices_are_equal = (G0 == G1)
    r0 = schur_rep_via_jacobi_trudi(la, ka, ys)
    r1 = schur_rep_via_generalized_confluent_vandermonde(la, ka, ys)
    r2 = schur_rep_via_generalized_confluent_vandermonde_efficient(la, ka, ys)
    polynomials_are_equal = (r0 == r1) and (r0 == r2)
    if verbose:
        print('test_schur_rep_two_formulas,')
        print('la = ' + str(la) + ', n = ' + str(n) + ', ka = ' + str(ka))
        print('r0 = ', r0)
        print('r1 = ', r1)
        print('r2 = ', r2)
        print('are equal the matrices? ', matrices_are_equal)
        print('are equal the polynomials? ', polynomials_are_equal)
    return matrices_are_equal and polynomials_are_equal


def random_symbolic_test_schur_rep_three_formulas():
    nmax = 4
    lambda_sum_max = 7
    kappa_sum_max = 7
    n = ZZ.random_element(1, nmax + 1)
    lambda_list = partitions_with_bounded_length_and_bounded_sum(n, lambda_sum_max)
    kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
    j_lambda = ZZ.random_element(0, len(lambda_list))
    la = lambda_list[j_lambda]
    j_kappa = ZZ.random_element(0, len(kappa_list))
    ka = kappa_list[j_kappa]
    return test_schur_rep_three_formulas(la, ka, True)


def big_symbolic_test_schur_rep_three_formulas(lambda_sum_max, kappa_sum_max):
    print('big_symbolic_test_schur_rep_three_formulas,')
    print('lambda_sum_max = %d, kappa_sum_max = %d.' % (lambda_sum_max, kappa_sum_max))
    t0 = time.time()
    nmax = kappa_sum_max
    tests = []
    for n in range(1, nmax):
        kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
        for ka in kappa_list:
            N = sum(ka)
            lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
            tests += [(la, ka) for la in lambda_list]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, ka in tests:
        result = test_schur_rep_three_formulas(la, ka, False)
        big_result = big_result and result
        print('la = ' + str(la) + ', ka = ' + str(ka) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


print(big_symbolic_test_schur_rep_three_formulas(5, 5))

# the following test takes almost 14 hours on a personal computer with 3.60GHz CPU.
#print(big_symbolic_test_schur_rep_three_formulas(9, 9))

