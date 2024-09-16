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


def Hcolumn(la, N, k, ts):
    R = ts.base_ring()
    la_max = la[0] if len(la) > 0 else 0
    la_ext = la + [0] * (N - len(la))
    degstop = max(la_max + N + 1 - k, 1)
    hs = hom_polynomials(ts, degstop)
    hfun = lambda j: hs[j] if j >= 0 else R.zero()
    H = vector(R, N)
    for j in range(N):
        H[j] = hfun(j + 1 - k + la_ext[N - 1 - j])
    return H


# tests


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
    print('number of tests done: ' + str(len(tests)))
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
    print('number of tests done: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds\n' % (t1 - t0))
    return big_result



# H_q^{\la, N}(t_1,\ldots,t_m,t_{m + 1})
# - H_q^{\la, N}(t_1,\ldots,t_m,t_{m + 2})
# = (t_{m+1}-t_{m+2})
# H_{q + 1}^{\la, N}(t_1,\ldots,t_m,t_{m+1},t_{m+2}).


def test_Hcolumn_difference_relation2(la, N, k, m, verbose):
    ts = pol_vars('t', m + 2)
    R = ts.base_ring()
    ts0 = vector(R, ts[0 : m])
    ts1 = vector(R, m + 1)
    ts1[0 : m] = ts0
    ts1[m] = ts[m]
    ts2 = vector(R, m + 1)
    ts2[0 : m] = ts0
    ts2[m] = ts[m + 1]
    lhs = Hcolumn(la, N, k, ts1) - Hcolumn(la, N, k, ts2)
    rhs = (ts[m] - ts[m + 1]) * Hcolumn(la, N, k + 1, ts)
    result = (lhs == rhs)
    if verbose:
        print('test_Hcolumn_difference_relation2')
        print('la = %s, N = %d, k = %d, m = %d' % (str(la), N, k, m))
        print('lhs =', lhs)
        print('rhs =', rhs)
        print('result =', result, '\n')
    return result


def big_test_Hcolumn_difference_relation2(lambda_sum_max, N_max, m_max):
    print('big_test_Hcolumn_difference_relation2')
    print('lambda_sum_max = %d, N_max = %d, m_max = %d' % (lambda_sum_max, N_max, m_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        tests += [(la, N, k, m) for la in lambda_list for k in range(lambda_sum_max) for m in range(1, m_max)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N, k, m in tests:
        result = test_Hcolumn_difference_relation2(la, N, k, m, False)
        big_result = big_result and result
        #print('N = %d, la = %s, k = %d, m = %d, result = %s' % (N, str(la), k, m, str(result)))
    print('number of tests done: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds\n' % (t1 - t0))
    return big_result


#print(test_Hcolumn_recursive_relation([2, 1], 5, 1, 3, True))
print(big_test_Hcolumn_recursive_relation(10, 8, 5))

#print(test_Hcolumn_difference_relation([2, 1], 5, 1, 3, True))
print(big_test_Hcolumn_difference_relation(10, 8, 5))

#print(test_Hcolumn_difference_relation2([2, 1], 5, 1, 3, True))
print(big_test_Hcolumn_difference_relation2(10, 8, 5))


