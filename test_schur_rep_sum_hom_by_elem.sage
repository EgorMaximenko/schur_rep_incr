# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables".
#
# Here we test the formula
# \sum_{l\in \bZ } (-1)^l \hom_{d - l}(y^{[\ka]}) \elem_l(y^{[\ka - rb_q]})
# = \binom{r + d - 1}{r-1}\; \hom_d(y_q) = \hom_d(y_q^{[r]}).


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

def symbolic_test_sum_hom_by_elem_rep(ka, q, r, dstop, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    r0 = sums_hom_by_elem_rep_lhs(ka, q, r, dstop, ys)
    r1 = sums_hom_by_elem_rep_rhs(ka, q, r, dstop, ys)
    result = (r0 == r1)
    if verbose:
        print('symbolic_test_sum_hom_by_elem_rep')
        print('ka =', ka)
        print('q =', q)
        print('r =', r)
        print('dstop =', dstop)
        print('r0 =', r0)
        print('r1 =', r1)
        print('result =', result)
    return result


def big_symbolic_test_sum_hom_by_elem_rep(ka, dstop, verbose):
    if verbose:
        print('big_symbolic_test_sum_hom_by_elem_rep,')
        print('ka = %s, dstop = %d.' % (str(ka), dstop))
    n = len(ka)
    tests = [(q, r) for q in range(n) for r in range(1, ka[q] + 1)]
    big_result = True
    for q, r in tests:
        result = symbolic_test_sum_hom_by_elem_rep(ka, q, r, dstop, False)
        if verbose:
            print('q = %d, r = %d, result = %s' % (q, r, str(result)))
        big_result = big_result and result
    return big_result


def huge_symbolic_test_sum_hom_by_elem_rep(kappa_sum_max, dstop):
    print('huge_symbolic_test_sum_hom_by_elem_rep,')
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
        result = big_symbolic_test_sum_hom_by_elem_rep(ka, dstop, False)
        big_result = big_result and result
        print('ka = ' + str(ka) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result



#print(symbolic_test_sum_hom_by_elem_rep([4, 2], 0, 3, 5, True))

#print(big_symbolic_test_sum_hom_by_elem_rep([4, 3, 1], 10, True))

print(huge_symbolic_test_sum_hom_by_elem_rep(8, 16))

