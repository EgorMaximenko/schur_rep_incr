# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables".
# This the new version, with increasing powers.


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


def test_confluent_vandermonde(ka, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    G = generalized_confluent_vandermonde_matrix([], ka, ys)
    r0 = my_det(G)
    r1 = confluent_vandermonde_det_formula(ys, ka)
    if verbose:
       print('r0 = ', r0)
       print('r1 = ', r1)
    return r0 == r1


def big_test_confluent_vandermonde(nmax, kappa_sum_max):
    print('big_test_confluent_vandermonde')
    print('nmax = %d, kappa_sum_max = %d' % (nmax, kappa_sum_max))
    tests = []
    for n in range(1, nmax + 1):
        kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
        tests += kappa_list
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for ka in tests:
        n = len(ka)
        result = test_confluent_vandermonde(ka, False)
        big_result = big_result and result
        print('ka = ' + str(ka) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    return big_result


#print(test_confluent_vandermonde([2, 1], True))

print(big_test_confluent_vandermonde(5, 10))

