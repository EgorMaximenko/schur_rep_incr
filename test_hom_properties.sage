# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables".


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


def Hcolumn(la, N, k, ts):
    R = ts.base_ring()
    la_max = la[0] if len(la) > 0 else 0
    la_ext = la + [0] * (N - len(la))
    degstop = max(la_max + N - k, 1)
    hs = hom_polynomials(ts, degstop)
    hfun = lambda j: hs[j] if j >= 0 else R.zero()
    H = vector(R, N)
    for j in range(N):           
        H[j] = hfun(j - k + la_ext[N - 1 - j])
    return H


# tests


def test_sum_elem_by_hom(n, degstop):
    xs = pol_vars('x', n)
    R = xs.base_ring()
    hs = hom_polynomials(xs, degstop)
    es = elem_polynomials(xs)
    efun = lambda j: es[j] if j <= n else R.zero()
    lhs = vector(R, degstop)
    rhs = vector(R, degstop)
    rhs[0] = R.one()
    for m in range(degstop):
        for k in range(m + 1):
            lhs[m] +=  ((-1) ** k) * hs[m - k] * efun(k)
    return lhs == rhs


def big_test_sum_elem_by_hom(nmax, degstop):
    print('big_test_sum_elem_by_hom')
    print('nmax = %d, degstop = %d' % (nmax, degstop))
    t0 = time.time()
    big_result = True
    for n in range(1, nmax + 1):
        result = test_sum_elem_by_hom(n, degstop)
        big_result = big_result and result
        print('n = %d, result = %s' % (n, str(result)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds\n' % (t1 - t0))
    return big_result


def test_hom_difference_relation(n, m, verbose):
    ts = pol_vars('t', n + 2)
    R = ts.base_ring()
    ts1 = vector(R, n + 1)
    ts1[0 : n] = ts[0 : n]
    ts1[n] = ts[n]
    ts2 = vector(R, n + 1)
    ts2[0 : n] = ts[0 : n]
    ts2[n] = ts[n + 1]
    hs = hom_polynomials(ts, m + 2)
    hs1 = hom_polynomials(ts1, m + 2)
    hs2 = hom_polynomials(ts2, m + 2)
    lhs = (ts[n] - ts[n + 1]) * hs[m]
    rhs = hs1[m + 1] - hs2[m + 1]
    result = lhs == rhs
    if verbose:
        print('test_hom_difference_relation')
        print('n = %d, m = %d' % (n, m))
        print('lhs =', lhs)
        print('rhs =', rhs)
        print('result =', result, '\n')
    return result


def big_test_hom_difference_relation(nmax, mmax):
    print('big_test_hom_difference_relation')
    print('nmax = %d, mmax = %d' % (nmax, mmax))
    t0 = time.time()
    tests = [(n, m) for n in range(1, nmax + 1) for m in range(0, mmax + 1)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for n, m in tests:
        result = test_hom_difference_relation(n, m, False)
        big_result = big_result and result
        print('n = %d, m = %s, result = %s' % (n, m, str(result)))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds\n' % (t1 - t0))
    return big_result


def test_hom_rep_single_variable(r, m, verbose):
    ts = pol_vars('t', 1)
    R = ts.base_ring()
    t = ts[0]
    trep = vector(R, r, [t for j in range(r)])
    hs = hom_polynomials(trep, m + 1)
    lhs = hs[m]
    rhs = binomial(r + m - 1, r - 1) * (t ** m)
    result = (lhs == rhs)
    if verbose:
        print('test_hom_rep_single_variable')
        print('r = %d, m = %d' % (r, m))
        print('lhs =', lhs)
        print('rhs =', rhs)
        print('result =', result, '\n')
    return result


def big_test_hom_rep_single_variable(rmax, mmax):
    print('big_test_hom_rep_single_variable')
    print('rmax = %d, mmax = %d' % (rmax, mmax))
    t0 = time.time()
    tests = [(r, m) for r in range(1, rmax + 1) for m in range(0, mmax + 1)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for r, m in tests:
        result = test_hom_rep_single_variable(r, m, False)
        big_result = big_result and result
        print('r = %d, m = %s, result = %s' % (r, m, str(result)))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds\n' % (t1 - t0))
    return big_result


def test_Hcolumn_recursive_relation(la, N, k, m, verbose):
    ts = pol_vars('t', m + 1)
    R = ts.base_ring()
    ts_reduced = vector(R, ts[0 : m])
    lhs = Hcolumn(la, N, k, ts) - ts[m] * Hcolumn(la, N, k + 1, ts)
    rhs = Hcolumn(la, N, k, ts_reduced)
    result = (lhs == rhs)
    if verbose:
        print('test_Hcolumn_recursive_relation')
        print('la = %s, N = %d, k = %d, m = %d' % (str(la), N, k, m))
        print('lhs =', lhs)
        print('rhs =', rhs)
        print('result =', result, '\n')
    return result


def big_test_Hcolumn_recursive_relation(lambda_sum_max, N_max, m_max):
    print('big_test_Hcolumn_recursive_relation')
    print('lambda_sum_max = %d, N_max = %d, m_max = %d' % (lambda_sum_max, N_max, m_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        tests += [(la, N, k, m) for la in lambda_list for k in range(lambda_sum_max) for m in range(1, m_max)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N, k, m in tests:
        result = test_Hcolumn_recursive_relation(la, N, k, m, False)
        big_result = big_result and result
        #print('N = %d, la = %s, k = %d, m = %d, result = %s' % (N, str(la), k, m, str(result)))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds\n' % (t1 - t0))
    return big_result


def test_Hcolumn_difference_relation(la, N, k, m, verbose):
    ts = pol_vars('t', m + 2)
    R = ts.base_ring()
    ts0 = vector(R, ts[0 : m])
    ts1 = vector(R, m + 1)
    ts1[0 : m] = ts0
    ts1[m] = ts[m]
    ts2 = vector(R, m + 1)
    ts2[0 : m] = ts0
    ts2[m] = ts[m + 1]
    lhs = Hcolumn(la, N, k, ts1) + (ts[m + 1] - ts[m]) * Hcolumn(la, N, k + 1, ts)
    rhs = Hcolumn(la, N, k, ts2)
    result = (lhs == rhs)
    if verbose:
        print('test_Hcolumn_difference_relation')
        print('la = %s, N = %d, k = %d, m = %d' % (str(la), N, k, m))
        print('lhs =', lhs)
        print('rhs =', rhs)
        print('result =', result, '\n')
    return result


def big_test_Hcolumn_difference_relation(lambda_sum_max, N_max, m_max):
    print('big_test_Hcolumn_difference_relation')
    print('lambda_sum_max = %d, N_max = %d, m_max = %d' % (lambda_sum_max, N_max, m_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        tests += [(la, N, k, m) for la in lambda_list for k in range(lambda_sum_max) for m in range(1, m_max)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N, k, m in tests:
        result = test_Hcolumn_difference_relation(la, N, k, m, False)
        big_result = big_result and result
        #print('N = %d, la = %s, k = %d, m = %d, result = %s' % (N, str(la), k, m, str(result)))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds\n' % (t1 - t0))
    return big_result


#print(test_hom_difference_relation(3, 4, True))
#print(big_test_hom_difference_relation(8, 16))

print(test_hom_rep_single_variable(3, 5, True))
print(big_test_hom_rep_single_variable(8, 16))

#print(big_test_sum_elem_by_hom(8, 16))

#print(test_Hcolumn_recursive_relation([2, 1], 5, 1, 3, True))
#print(big_test_Hcolumn_recursive_relation(8, 6, 4))

#print(test_Hcolumn_difference_relation([2, 1], 5, 1, 3, True))
#print(big_test_Hcolumn_difference_relation(8, 6, 4))

