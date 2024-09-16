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


# With 1-based numeration, the jth component of Hcolumn is
# \hom_{j - k + \la_{N+1-j}}(t_1,\ldots,t_m)
# With 0-based numeration, the jth component of Hcolumn is
# \hom_{j + 1 - k + \la_{N-1-j}(t_0,\ldots,t_{m-1})

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


def Block(la, N, M, ts):
    R = ts.base_ring()
    B = matrix(R, N, M)
    for k in range(M):
        ts_reduced = vector(R, k + 1, ts[0 : k + 1])
        B[:, k] = Hcolumn(la, N, k + 1, ts_reduced)
    return B


def partial_sums(ka):
    n = len(ka)
    om = [0] * n
    om[0] = ka[0]
    for j in range(1, n):
        om[j] = om[j - 1] + ka[j]
    return om


# Construct matrix A_{\la,\ka}(xs) from the paper.


def A_matrix(la, ka, xs):
    om = [0] + partial_sums(ka)
    n = len(ka)
    N = sum(ka)
    la_ext = la + [0] * (N - len(la))
    R = xs.base_ring()
    A = matrix(R, N, N)
    for q in range(n):
        local_vars = vector(R, ka[q], xs[om[q] : om[q + 1]])
        A[:, om[q] : om[q + 1]] = Block(la, N, ka[q], local_vars)  
    return A


def V_matrix(la, xs):
    R = xs.base_ring()
    N = len(xs)
    la_ext = la + [0] * (N - len(la))
    V = matrix(R, N, N)
    for j in range(N):
        for k in range(N):
            p = j + la_ext[N - 1 - j]
            if p >= 0:
                V[j, k] = xs[k] ** p
    return V


# tests

def vars_ts_as(p, N):
    # create p variables ts[0],...,ts[p-1]
    # and N*N variables avars[0],...,avars[N*N-1]
    na = N * N
    ts_names = ['t' + str(k) for k in range(p)]
    as_names = ['a' + str(k) for k in range(na)]
    all_var_names = ts_names + as_names
    PR = PolynomialRing(QQ, all_var_names)
    all_vars = PR.gens()
    ts = vector(PR, p, all_vars[0 : p])
    avars = vector(PR, na, all_vars[p : p + na])
    return ts, avars


def test_join_block_and_column(la, N, p, d, verbose):
    # p + 1 + d <= N
    ts, avars = vars_ts_as(p + 1, N)
    PR = ts.base_ring()
    # matrices in the left-hand side and right-hand side
    L = matrix(PR, N, N)
    R = matrix(PR, N, N)
    for k in range(N):
        for j in range(N):
            L[j, k] = avars[N * k + j]
            R[j, k] = avars[N * k + j]
    ts_first = vector(PR, p, ts[0 : p])
    ts_last = vector(PR, 1, [ts[p]])
    L[:, d : d + p] = Block(la, N, p, ts_first)
    L[:, d + p] = Hcolumn(la, N, 1, ts_last)
    R[:, d : d + p + 1] = Block(la, N, p + 1, ts)
    # comparison
    prod_diff = PR.one()
    for j in range(p):
        prod_diff *= ts[p] - ts[j]
    lhs = my_det(L)
    rhs = my_det(R) * prod_diff
    result = (lhs == rhs)
    if verbose:
        print('test_join_block_and_column')
        print('la = %s, N = %d, p = %d, d = %d' % (str(la), N, p, d))
        print('lhs = ' + str(lhs))
        print('rhs = ' + str(rhs))
        print('result = ' + str(result) + '\n')
    return result


def big_test_join_block_and_column(lambda_sum_max, N_max):
    print('big_test_join_block_and_column')
    print('lambda_sum_max = %d, N_max = %d' % (lambda_sum_max, N_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max + 1):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        for la in lambda_list:
            for p in range(N - 1):
                for d in range(N - p):
                    tests += [(la, N, p, d)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N, p, d in tests:
        result = test_join_block_and_column(la, N, p, d, False)
        big_result = big_result and result
        s = 'la = ' + str(la)
        s += ', N = %d, p = %d, d = %d' % (N, p, d)
        s += ', result = ' + str(result)
        print(s)
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


def test_assemble_block_from_columns(la, N, M, K, verbose):
    # M + K <= N
    ts, avars = vars_ts_as(M, N)
    PR = ts.base_ring()
    # matrices in the left-hand side and right-hand side
    L = matrix(PR, N, N)
    R = matrix(PR, N, N)
    for k in range(N):
        for j in range(N):
            L[j, k] = avars[N * k + j]
            R[j, k] = avars[N * k + j]
    for k in range(M):
        local_vars = vector(PR, 1, [ts[k]])
        L[:, K + k] = Hcolumn(la, N, 1, local_vars)
    R[:, K : K + M] = Block(la, N, M, ts)
    # comparison
    prod_diff = PR.one()
    for j in range(M - 1):
        for k in range(j + 1, M):
            prod_diff *= ts[k] - ts[j]
    lhs = my_det(L)
    rhs = my_det(R) * prod_diff
    result = (lhs == rhs)
    if verbose:
        print('test_assemble_block_from_columns')
        print('la = %s, N = %d, M = %d, K = %d' % (str(la), N, M, K))
        print('lhs = ' + str(lhs))
        print('rhs = ' + str(rhs))
        print('result = ' + str(result) + '\n')
    return result


def big_test_assemble_block_from_columns(lambda_sum_max, N_max):
    print('big_test_assemble_block_from_columns')
    print('lambda_sum_max = %d, N_max = %d' % (lambda_sum_max, N_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max + 1):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        for la in lambda_list:
            for M in range(N):
                for K in range(N - M):
                    tests += [(la, N, M, K)]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N, M, K in tests:
        result = test_assemble_block_from_columns(la, N, M, K, False)
        big_result = big_result and result
        s = 'la = ' + str(la)
        s += ', N = %d, M = %d, K = %d' % (N, M, K)
        s += ', result = ' + str(result)
        print(s)
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


def test_V_via_A(la, ka, verbose):
    n = len(ka)
    N = sum(ka)
    om = [0] + partial_sums(ka)
    xs = pol_vars('x', N)
    V = V_matrix(la, xs)
    A = A_matrix(la, ka, xs)  
    PR = xs.base_ring()
    prod_diff = PR.one()
    for q in range(n):
        for j in range(om[q], om[q + 1] - 1):
            for k in range(j + 1, om[q + 1]):
                prod_diff *= xs[k] - xs[j]
    lhs = my_det(V)
    rhs = my_det(A) * prod_diff
    result = (lhs == rhs)
    if verbose:
        print('test_V_via_A')
        print('la = %s, ka = %s' % (str(la), str(ka)))
        print('lhs = ' + str(lhs))
        print('rhs = ' + str(rhs))
        print('result = ' + str(result))
    return result


def big_test_V_via_A(lambda_sum_max, kappa_sum_max):
    print('big_test_V_via_A,')
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
        result = test_V_via_A(la, ka, False)
        big_result = big_result and result
        print('la = ' + str(la) + ', ka = ' + str(ka) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


def test_schur_and_A_and_A0(la, ka, verbose):
    n = len(ka)
    N = sum(ka)
    xs = pol_vars('x', N)
    J = jacobi_trudi_matrix(la, xs)
    A = A_matrix(la, ka, xs)
    A0 = A_matrix([], ka, xs)
    lhs = my_det(J) * my_det(A0)
    rhs = my_det(A)
    result = (lhs == rhs)
    if verbose:
        print('test_schur_and_A_and_A0')
        print('la = %s, ka = %s' % (str(la), str(ka)))
        print('lhs = ' + str(lhs))
        print('rhs = ' + str(rhs))
        print('result = ' + str(result))
    return result


def big_test_schur_and_A_and_A0(lambda_sum_max, kappa_sum_max):
    print('big_test_schur_and_A_and_A0,')
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
        result = test_schur_and_A_and_A0(la, ka, False)
        big_result = big_result and result
        print('la = ' + str(la) + ', ka = ' + str(ka) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


def show_schur_rep_third_proof_big_tests():
    result0 = big_test_join_block_and_column(7, 7)
    result1 = big_test_assemble_block_from_columns(7, 7)
    result2 = big_test_V_via_A(7, 7)
    result3 = big_test_schur_and_A_and_A0(7, 7)
    print('')
    print('big_test_join_block_and_column(7, 7):')
    print(result0)
    print('big_test_assemble_block_from_columns(7, 7):')
    print(result1)
    print('big_test_V_via_A(7, 7):')
    print(result2)
    print('big_test_schur_and_A_and_A0(7, 7):')
    print(result3)


#print(test_join_block_and_column([3, 2, 1], 7, 4, 1, True))
#print(big_test_join_block_and_column(7, 7))

#print(test_assemble_block_from_columns([3, 1, 1], 7, 4, 2, True))
#print(big_test_assemble_block_from_columns(7, 7))

#print(test_V_via_A([3, 2, 2], [4, 1, 3], True))
#print(big_test_V_via_A(7, 7))

#print(test_schur_and_A_and_A0([2, 1], [3, 2, 3], True))
print(big_test_schur_and_A_and_A0(7, 7))

