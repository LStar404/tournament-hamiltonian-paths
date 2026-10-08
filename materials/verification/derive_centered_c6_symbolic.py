"""Exact graph-reduction certificate for the centered permanent's sixth term.

Uses only S_ji=-S_ij, S_ii=0, S_ij**2=1 (i != j), and S 1=0.
"""

from collections import defaultdict
from functools import lru_cache
from itertools import permutations
from math import factorial


def partitions(k):
    out = []
    def rec(i, blocks):
        if i == k:
            if all(len(b) >= 2 for b in blocks):
                out.append(tuple(tuple(b) for b in blocks))
            return
        for a in range(len(blocks)):
            blocks[a].append(i)
            rec(i+1,blocks)
            blocks[a].pop()
        blocks.append([i])
        rec(i+1,blocks)
        blocks.pop()
    rec(0,[])
    return out


def mobius(pi):
    return (-1)**(6-len(pi)) * __import__("math").prod(factorial(len(b)-1)
                                                       for b in pi)


def bipartite_classes():
    ps = partitions(6)
    groups = defaultdict(int)
    for pi in ps:
        row = {x:i for i,b in enumerate(pi) for x in b}
        for sigma in ps:
            col = {x:i for i,b in enumerate(sigma) for x in b}
            r,c = len(pi),len(sigma)
            a = [[0]*c for _ in range(r)]
            for x in range(6):
                a[row[x]][col[x]] += 1
            key = min(tuple(a[i][j] for i in rp for j in cp)
                      for rp in permutations(range(r))
                      for cp in permutations(range(c)))
            groups[(r,c,key)] += mobius(pi)*mobius(sigma)
    return groups


def add_scaled(out, other, scale=1, shift=0):
    for (graph,power), coefficient in other.items():
        out[(graph,power+shift)] += scale*coefficient


@lru_cache(None)
def canonical_simple(v, edges):
    """Return signed canonical graph; antisymmetric automorphisms give zero."""
    best = None
    signs = set()
    for p in permutations(range(v)):
        mapped = []
        sign = 1
        for a,b in edges:
            a,b = p[a],p[b]
            if a > b:
                a,b = b,a
                sign = -sign
            mapped.append((a,b))
        key = tuple(sorted(mapped))
        if best is None or key < best:
            best,signs = key,{sign}
        elif key == best:
            signs.add(sign)
    if len(signs)>1:
        return None,0
    return (v,best),next(iter(signs))


@lru_cache(None)
def reduce_graph(v, raw_edges):
    """Dictionary (canonical simple graph, power of n) -> integer."""
    edges = []
    sign = 1
    for a,b in raw_edges:
        if a == b:
            return {}
        if a > b:
            a,b = b,a
            sign = -sign
        edges.append((a,b))
    edges.sort()
    degree = [0]*v
    for a,b in edges:
        degree[a] += 1
        degree[b] += 1
    if any(d == 1 for d in degree):
        return {}
    isolated = sum(d == 0 for d in degree)
    if isolated:
        used = [i for i,d in enumerate(degree) if d]
        lookup = {x:i for i,x in enumerate(used)}
        smaller = tuple((lookup[a],lookup[b]) for a,b in edges)
        result = defaultdict(int)
        add_scaled(result,reduce_graph(len(used),smaller),sign,isolated)
        return {key:value for key,value in result.items() if value}
    repeated = next((e for i,e in enumerate(edges[:-1]) if e == edges[i+1]),
                    None)
    if repeated is not None:
        a,b = repeated
        rest = list(edges)
        rest.remove(repeated)
        rest.remove(repeated)
        result = defaultdict(int)
        add_scaled(result,reduce_graph(v,tuple(rest)),sign)
        kept = [x for x in range(v) if x != b]
        lookup = {x:i for i,x in enumerate(kept)}
        lookup[b] = lookup[a]
        merged = tuple((lookup[x],lookup[y]) for x,y in rest)
        add_scaled(result,reduce_graph(v-1,merged),-sign)
        return {key:value for key,value in result.items() if value}
    graph, orientation = canonical_simple(v,tuple(edges))
    if graph is None:
        return {}
    return {(graph,0):sign*orientation}


def main():
    groups = bipartite_classes()
    result = defaultdict(int)
    for (r,c,flat), weight in groups.items():
        edges = tuple((i,r+j)
                      for i in range(r) for j in range(c)
                      for _ in range(flat[i*c+j]))
        add_scaled(result,reduce_graph(r+c,edges),weight)
    print("partitions",len(partitions(6)),"graph classes",len(groups))
    empty=(0,())
    cycle4=(4,((0,1),(0,2),(1,3),(2,3)))
    k23=(5,((0,1),(0,2),(0,3),(1,4),(2,4),(3,4)))
    cycle6=(6,((0,1),(0,2),(1,3),(2,4),(3,5),(4,5)))
    expected={
        (empty,1):-45720,(empty,2):82080,(empty,3):-44835,
        (empty,4):9045,(empty,5):-585,(empty,6):15,
        (cycle4,0):6480,(cycle4,1):-2250,(cycle4,2):90,
        (k23,0):480,(cycle6,0):120,
    }
    assert len(partitions(6))==41 and len(groups)==27
    assert {key:value for key,value in result.items() if value}==expected
    for (graph,power),coefficient in sorted(result.items(),key=str):
        if coefficient:
            print("coefficient",coefficient,"n_power",power,"graph",graph)
    print("symbolic coefficient certificate passed")


if __name__ == "__main__":
    main()
