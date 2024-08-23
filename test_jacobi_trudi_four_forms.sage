# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables".

# Let la=(la[0],...,la[L-1]), x=(x[0],...,x[N-1]) with L <= N.
# We test that the determinants of the following four matrices coincide:
# 1) the Jacobi-Trudi matrix with powers la[0],...,la[L-1] on the main diagonal,
# 2) the extended Jacobi-Trudi matrix with powers la[0],...,la[N-1] on the main diagonal,
# 3) the extended Jacobi-Trudi matrix with reverted rows and columns,
#    with powers la[N-1],...,la[0] on the main diagonal,
# 4) a modification of 3) where in column k we use only x[0],...,x[k].


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
# Note that we do not create the submatrices explicitly.
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
    R = xs.base_ring()
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
    R = xs.base_ring()
    hs = hom_polynomials(xs, la_max + la_len)
    hfun = lambda j: hs[j] if j >= 0 else R.zero()
    A = matrix(R, la_len, la_len)
    for j in range(la_len):
        for k in range(la_len):
            A[j, k] = hfun(la[j] - j + k)
    return A


def jacobi_trudi_matrix_extended(la, xs):
    N = len(xs)
    la_max = la[0] if len(la) > 0 else 0
    la_ext = la + [0] * (N - len(la))
    R = xs.base_ring()
    hs = hom_polynomials(xs, la_max + N)
    hfun = lambda j: hs[j] if j >= 0 else R.zero()
    A = matrix(R, N, N)
    for j in range(N):
        for k in range(N):
            A[j, k] = hfun(la_ext[j] - j + k)
    return A


def jacobi_trudi_matrix_extended_increasing(la, xs):
    N = len(xs)
    la_max = la[0] if len(la) > 0 else 0
    la_ext = la + [0] * (N - len(la))
    R = xs.base_ring()
    hs = hom_polynomials(xs, la_max + N)
    hfun = lambda j: hs[j] if j >= 0 else R.zero()
    A = matrix(R, N, N)
    for j in range(N):
        for k in range(N):
            A[j, k] = hfun(la_ext[N - j - 1] + j - k)
    return A


def jacobi_trudi_matrix_with_reduced_variables(la, xs):
    N = len(xs)
    la_max = la[0] if len(la) > 0 else 0
    la_ext = la + [0] * (N - len(la))
    R = xs.base_ring()
    A = matrix(R, N, N)
    for k in range(N):
        zs = vector(R, k + 1, xs[0 : k + 1])
        hs = hom_polynomials(zs, la_max + N)
        hfun = lambda j: hs[j] if j >= 0 else R.zero()
        for j in range(N):
            A[j, k] = hfun(la_ext[N - j - 1] + j - k)
    return A


# tests


def test_schur_via_jacobi_trudi_four_forms(la, N, verbose):
    xs = pol_vars('x', N)
    A0 = jacobi_trudi_matrix(la, xs)
    r0 = my_det(A0)
    A1 = jacobi_trudi_matrix_extended(la, xs)
    r1 = my_det(A1)
    A2 = jacobi_trudi_matrix_extended_increasing(la, xs)
    r2 = my_det(A2)
    A3 = jacobi_trudi_matrix_with_reduced_variables(la, xs)
    r3 = my_det(A3)
    if verbose:
        print('test_schur_via_jacobi_trudi_four_forms')
        print('la = ' + str(la) + ', N = ' + str(N))
        print(r0)
        print(r1)
        print(r2)
        print(r3)
    return (r0 == r1) and (r0 == r2) and (r0 == r3)


def big_symbolic_test_schur_via_jacobi_trudi_four_forms(lambda_sum_max, N_max):
    print('big_symbolic_test_schur_via_jacobi_trudi_four_forms,')
    print('lambda_sum_max = %d, N_max = %d.' % (lambda_sum_max, N_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        tests += [(la, N) for la in lambda_list]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N in tests:
        result = test_schur_via_jacobi_trudi_four_forms(la, N, False)
        big_result = big_result and result
        print('la = ' + str(la) + ', N = ' + str(N) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


#print(big_symbolic_test_schur_via_jacobi_trudi_four_forms(12, 6))


# The following test takes about 3 hours.
#print(big_symbolic_test_schur_via_jacobi_trudi_four_forms(16, 8))

