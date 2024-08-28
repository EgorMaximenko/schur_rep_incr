# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables".
# This the new version, with increasing powers.
# In this file, we test the matrix identity $G=JM$ used in our "first proof".


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


def jacobi_trudi_matrix_extended_increasing(la, xs):
    # The powers on the main diagonal are la[N-1], \ldots, la[0].
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


def elem_polynomials(xs):
    n = len(xs)
    R = xs.base_ring()
    es = vector(R, n + 1)
    es[0] = R.one()
    for j in range(n):
        es[j + 1] = es[j] * xs[j]
        for k in range(j, 0, -1):
            es[k] = es[k] + es[k - 1] * xs[j]
    return es


def list_with_reps(ys, ka):
    PR = ys.base_ring()
    N = sum(ka)
    result = vector(PR, N)
    k = 0
    for p in range(len(ys)):
        for r in range(ka[p]):
            result[k] = ys[p]
            k += 1
    return result


def M_matrix(ka, ys):
    n = len(ka)
    N = sum(ka)
    R = ys.base_ring()
    M = matrix(R, N, N)
    k = 0
    for p in range(n):
        for r in range(ka[p]):
            ka1 = list(ka[ : ])
            ka1[p] -= r + 1
            zs = list_with_reps(ys, ka1)
            es = elem_polynomials(zs)
            for j in range(N):
                mydeg = j - r
                mysign = (-1) ** mydeg
                isgood = (mydeg >= 0) and (mydeg <= N - r - 1)
                if isgood:
                    M[j, k] = mysign * es[mydeg]
            k += 1
    return M


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


def sums_hom_by_elem_rep_lhs(ka, q, r, dstop, ys):
    # 0 <= r <= ka[q]
    n = len(ka)
    N = sum(ka)
    R = ys.base_ring()
    ka1 = list(ka[ : ])
    ka1[q] -= r
    xs = list_with_reps(ys, ka)
    zs = list_with_reps(ys, ka1)
    es = elem_polynomials(zs)
    hs = hom_polynomials(xs, dstop)
    result = vector(R, dstop)
    for d in range(dstop):
        lmax = min(d, N - r)
        s = R.zero()
        for l in range(lmax + 1):
            factor0 = (-1) ** l
            factor1 = hs[d - l]
            factor2 = es[l]
            term = factor0 * factor1 * factor2
            s += term
        result[d] = s
    return result


def sums_hom_by_elem_rep_rhs(ka, q, r, dstop, ys):
    # d >= 0
    # 0 <= r <= ka[q]
    R = ys.base_ring()
    result = vector(R, dstop)
    for d in range(dstop):
        factor0 = binomial(r + d - 1, r - 1)
        factor1 = ys[q] ** d
        result[d] = factor0 * factor1
    return result


# tests


def test_sum_hom_by_elem_rep(ka, q, r, dstop, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    r0 = sums_hom_by_elem_rep_lhs(ka, q, r, dstop, ys)
    r1 = sums_hom_by_elem_rep_rhs(ka, q, r, dstop, ys)
    result = (r0 == r1)
    if verbose:
        print('test_sum_hom_by_elem_rep')
        print('ka =', ka)
        print('q =', q)
        print('r =', r)
        print('dstop =', dstop)
        print('r0 =', r0)
        print('r1 =', r1)
        print('result =', result)
    return result


def big_test_sum_hom_by_elem_rep(ka, dstop, verbose):
    if verbose:
        print('big_test_sum_hom_by_elem_rep,')
        print('ka = %s, dstop = %d.' % (str(ka), dstop))
    n = len(ka)
    tests = [(q, r) for q in range(n) for r in range(1, ka[q] + 1)]
    big_result = True
    for q, r in tests:
        result = test_sum_hom_by_elem_rep(ka, q, r, dstop, False)
        if verbose:
            print('q = %d, r = %d, result = %s' % (q, r, str(result)))
        big_result = big_result and result
    return big_result


def huge_test_sum_hom_by_elem_rep(kappa_sum_max, dstop):
    print('huge_test_sum_hom_by_elem_rep,')
    print('kappa_sum_max = %d, dstop = %d.' % (kappa_sum_max, dstop))
    t0 = time.time()
    nmax = kappa_sum_max
    tests = []
    for n in range(1, nmax):
        kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
        tests += kappa_list
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for ka in tests:
        result = big_test_sum_hom_by_elem_rep(ka, dstop, False)
        big_result = big_result and result
        print('ka = ' + str(ka) + ', ' + str(result))
    print('number of tests done: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


def test_G_eq_JM(la, ka, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    G = generalized_confluent_vandermonde_matrix(la, ka, ys)
    xs = list_with_reps(ys, ka)
    J = jacobi_trudi_matrix_extended_increasing(la, xs)
    M = M_matrix(ka, ys)
    JM = J * M
    result = (G == JM)
    if verbose:
        print('test_G_eq_JM')
        print('la =', la)
        print('ka =', ka)
        print('ys =', ys)   
        print('G =')
        print(G)
        print('J = ')
        print(J)
        print('M = ')
        print(M)
        print('JM =')
        print(JM)
        print('result =', result)
    return result


def big_test_G_eq_JM(lambda_sum_max, kappa_sum_max):
    print('big_test_G_eq_JM,')
    print('lambda_sum_max = %d, kappa_sum_max = %d.' % (lambda_sum_max, kappa_sum_max))
    t0 = time.time()
    nmax = kappa_sum_max
    tests = []
    for n in range(1, nmax + 1):
        kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
        for ka in kappa_list:
            N = sum(ka)
            lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
            tests += [(la, ka) for la in lambda_list]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, ka in tests:
        result = test_G_eq_JM(la, ka, False)
        big_result = big_result and result
        print('la = ' + str(la) + ', ka = ' + str(ka) + ', ' + str(result))
    print('number of tests done: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


#print(test_sum_hom_by_elem_rep([4, 2], 0, 3, 5, True))

#print(big_test_sum_hom_by_elem_rep([4, 3, 1], 10, True))

print(huge_test_sum_hom_by_elem_rep(8, 16))



print(big_test_G_eq_JM(8, 8))

#print(big_test_G_eq_JM(12, 8))


