"""
http://aspn.activestate.com/ASPN/Cookbook/Python/Recipe/492216

Iterator algebra implementations of join algorithms: hash join, merge
join, and nested loops join, as well as a variant I dub "bisect join".

Requires Python 2.4.

Author: Jim Baker, jbaker@zyasoft.com

"""

import operator
from rdflib import py3compat

def identity(x):
    """x -> x

    As a predicate, this function is useless, but it provides a
    useful/correct default.

    >>> identity(('apple', 'banana', 'cherry'))
    ('apple', 'banana', 'cherry')
    """
    return x


def inner(X):
    """
    >>> X = [1, 2, 3, 4, 5]
    >>> list(inner(X))
    [1, 2, 3, 4, 5]
    """
    for x in X:
        yield x


#The original hash_join
# throughout, we assume S is the smaller relation of R and S.
def hash_join(R, S, predicate=identity, join=inner, combine=operator.concat):
    hashed = {}
    for s in S:
        hashed.setdefault(predicate(s), []).append(s)
    for r in R:
        for s in join(hashed.get(predicate(r), ())):
            yield combine(r, s)


def nested_loops_join(R, S, predicate=identity, join=inner,
                      combine=operator.concat, theta=operator.eq):
    Sp = [(predicate(s), s) for s in S]
    for r in R:
        rp = predicate(r)
        for s in join(s for sp, s in Sp if theta(rp, sp)):
            yield combine(r, s)


def bisect_join(R, S, predicate=identity, join=inner, combine=operator.concat):
    """
    I have not found discussion of this variant on the sort-merge
    join anywhere.
    """

    from bisect import bisect_left

    def consume(Sp, si, rp):
        """This needs a better name..."""
        length = len(S)
        while si < length:
            sp, s = Sp[si]
            if rp == sp:
                yield s
            else:
                break
            si += 1

    Rp = sorted((predicate(r), r) for r in R)
    Sp = sorted((predicate(s), s) for s in S)

    for rp, r in Rp:
        si = bisect_left(Sp, (rp,))
        for s in join(consume(Sp, si, rp)):
            yield combine(r, s)


def merge_join(R, S, predicate=identity, join=inner, combine=operator.concat):
    """
    For obvious reasons, we depend on the predicate providing a
    sortable relation.

    Compare this presentation using iterator algebra with the much
    more difficult to follow presentation (IMHO) in
    http://en.wikipedia.org/wiki/Sort-Merge_Join
    """

    from itertools import groupby

    def advancer(Xp):
        """A simple wrapper of itertools.groupby, we simply need
        to follow our convention that Xp -> (xp0, x0), (xp1, x1), ...
        """

        for k, g in groupby(Xp, key=operator.itemgetter(0)):
            yield k, list(g)

    R_grouped = advancer(sorted((predicate(r), r) for r in R))
    S_grouped = advancer(sorted((predicate(s), s) for s in S))

    # in the join we need to distinguish rp from rk in the unpack, so
    # just use rk, sk
    rk, R_matched = next(R_grouped) if py3compat.PY3 else R_grouped.next()
    sk, S_matched = next(S_grouped) if py3compat.PY3 else S_grouped.next()

    while R_grouped and S_grouped:
        comparison = cmp(rk, sk)
        if comparison == 0:
            # standard Cartesian join here on the matched tuples, as
            # subsetted by the join method
            for rp, r in R_matched:
                for sp, s in join(S_matched):
                    yield combine(r, s)
            rk, R_matched = next(R_grouped) if py3compat.PY3 else R_grouped.next()
            sk, S_matched = next(S_grouped) if py3compat.PY3 else S_grouped.next()
        elif comparison > 0:
            sk, S_matched = next(S_grouped) if py3compat.PY3 else S_grouped.next()
        else:
            rk, R_matched = next(R_grouped) if py3compat.PY3 else R_grouped.next()

# from FuXi.Rete.IteratorAlgebra import identity
# from FuXi.Rete.IteratorAlgebra import inner
# from FuXi.Rete.IteratorAlgebra import hash_join
# from FuXi.Rete.IteratorAlgebra import nested_loops_join
# from FuXi.Rete.IteratorAlgebra import bisect_join
# from FuXi.Rete.IteratorAlgebra import merge_join
