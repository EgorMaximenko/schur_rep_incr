# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables".
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

def vars_us_vs_as(N, p, q):
    t = N - p - q
    na = N * t
    us_names = ['u' + str(k) for k in range(p)]
    vs_names = ['v' + str(k) for k in range(q)]
    as_names = ['a' + str(k) for k in range(na)]
    all_var_names = us_names + vs_names + as_names
    PR = PolynomialRing(QQ, all_var_names)
    all_vars = PR.gens()
    us = vector(PR, p, all_vars[0 : p])
    vs = vector(PR, q, all_vars[p : p + q])
    avars = vector(PR, N * t, all_vars[p + q : p + q + na])
    return us, vs, avars


def test_elimination_of_variables(la, N, p, q, verbose):
    t = N - p - q
    us, vs, avars = vars_us_vs_as(N, p, q)
    PR = us.base_ring()
    # matrices in the left-hand side and right-hand side
    L = matrix(PR, N, N)
    R = matrix(PR, N, N)
    for k in range(p):
        us_reduced = vector(PR, k + 1, us[0 : k + 1])
        L[:, k] = Hcolumn(la, N, k, us_reduced)
        R[:, k] = Hcolumn(la, N, k, us_reduced)
    for k in range(q):
        vs_reduced = vector(PR, k + 1, vs[0 : k + 1])
        uvs_reduced = vector(PR, p + k + 1)
        uvs_reduced[0 : p] = us
        uvs_reduced[p : p + k + 1] = vs_reduced
        L[:, p + k] = Hcolumn(la, N, p + k, uvs_reduced)
        R[:, p + k] = Hcolumn(la, N, k, vs_reduced)       
    for k in range(t):
        for j in range(N):
            L[j, p + q + k] = avars[N * k + j]
            R[j, p + q + k] = avars[N * k + j]
    # denominator of the right-hand side
    D = PR.one()
    for j in range(p):
        for k in range(q):
            D *= vs[k] - us[j]
    # comparison
    lhs = my_det(L)
    rhs = my_det(R) / D
    result = (lhs == rhs)
    if verbose:
        print('test_elimination_of_variables')
        print('la = %s, N = %d, p = %d, q = %d' % (str(la), N, p, q))
        print('lhs = ' + str(lhs))
        print('rhs = ' + str(rhs))
        print('result = ' + str(result) + '\n')
    return result


def big_test_elimination_of_variables(la, N, verbose):
    if verbose:
        print('big_test_elimination_of_variables')
        print('la = %s, N_max = %d' % (str(la), N))
    tests = [(la, N, p, q) for p in range(1, N) for q in range(1, N + 1 - p)]
    big_result = True
    for la, N, p, q in tests:
        result = test_elimination_of_variables(la, N, p, q, False)
        big_result = big_result and result
        if verbose:
            print('N = %d, la = %s, p = %d, q = %d, result = %s' % (N, str(la), p, q, str(result)))
    return big_result   


def huge_test_elimination_of_variables(lambda_sum_max, N_max):
    print('big_test_elimination_of_variables')
    print('lambda_sum_max = %d, N_max = %d' % (lambda_sum_max, N_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max + 1):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        tests += [(la, N) for la in lambda_list]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N in tests:
        result = big_test_elimination_of_variables(la, N, False)
        big_result = big_result and result
        print('N = %d, la = %s, result = %s' % (N, str(la), str(result)))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


#print(test_elimination_of_variables([3, 3, 1], 5, 2, 2, True))

huge_test_elimination_of_variables(7, 7)

#huge_test_elimination_of_variables(8, 8)


