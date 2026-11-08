"""Independent exact checks for the Fano examples; Python 3.10+, standard library."""
from collections import deque
from fractions import Fraction as Q
from functools import cache
from itertools import combinations, product
from math import lcm, prod
import json


def mask(labels):
    return sum(1 << (i - 1) for i in labels)


lines = tuple(map(mask, [(1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6),
                         (2, 5, 7), (3, 4, 7), (3, 5, 6)]))


def fano(x):
    return 1 if any(x & line == line for line in lines) else -1


def sign(x, j):
    return 1 if x >> j & 1 else -1


def labels_of(x, n):
    return [i for i in range(n) if x >> i & 1]


class Flow:
    """Edmonds--Karp with sparse integer residual capacities."""
    def __init__(self, n):
        self.residual = [{} for _ in range(n)]

    def add(self, v, w, cap):
        self.residual[v][w] = cap
        self.residual[w][v] = 0

    def value(self, v, w):
        return self.residual[w][v]

    def solve(self, source, sink):
        total = 0
        while True:
            parent = {source: None}
            queue = deque([source])
            while queue and sink not in parent:
                v = queue.popleft()
                for w, cap in self.residual[v].items():
                    if w not in parent and cap:
                        parent[w] = v
                        queue.append(w)
            if sink not in parent:
                return total
            path = []
            w = sink
            while w != source:
                v = parent[w]
                path.append((v, w))
                w = v
            amount = min(self.residual[v][w] for v, w in path)
            for v, w in path:
                self.residual[v][w] -= amount
                self.residual[w][v] += amount
            total += amount


def section(live):
    n = len(live)
    nv = 2**n
    values = [fano(sum(1 << live[i] for i in labels_of(x, n))) for x in range(nv)]
    b = Q(sum(values), nv)
    essential = [i for i in range(n) if any(values[x] != values[x ^ (1 << i)]
                                             for x in range(nv))]
    a = [Q(1 + b, len(essential)) if i in essential else Q(0) for i in range(n)]
    demands = [values[x] - b - sum(sign(x, j) * a[j] for j in range(n)) for x in range(nv)]
    scale = lcm(*(d.denominator for d in demands))
    ints = [int(scale * d) for d in demands]
    total = sum(d for d in ints if d > 0)
    network = Flow(nv + 2)
    for x, d in enumerate(ints):
        if d < 0:
            network.add(nv, x, -d)
        elif d > 0:
            network.add(x, nv+1, d)
        for j in range(n):
            if x >> j & 1 == 0:
                network.add(x, x | (1 << j), total)
    if network.solve(nv, nv+1) != total:
        raise ValueError(f'Infeasible section {live}')
    witness = {}
    for x in range(nv):
        for j in range(n):
            if x >> j & 1 == 0:
                witness[x, j] = a[j] + Q(network.value(x, x | (1 << j)), scale)
    for x in range(nv):
        assert sum(sign(x, j) * witness[x & ~(1 << j), j] for j in range(n)) == values[x] - b
        assert all(witness[x & ~(1 << j), j] >= witness[0,j] == a[j] for j in range(n))
    return witness


def inner_table(kind):
    n = {'coord': 1, 'and': 2, 'path': 4, 'minus': 0}[kind]
    values, psi = [], []
    for x in range(2**n):
        z = [x >> j & 1 for j in range(n)]
        if kind == 'path':
            winning = any(z[i] and z[i+1] for i in range(3))
            row = (z[1] * (1-z[2]), Q(1,2), Q(1,2), (1-z[1]) * z[2])
        elif kind == 'and':
            winning = all(z)
            row = (z[1], Q(1,2))
        elif kind == 'coord':
            winning = z[0]
            row = (1,)
        else:
            winning = False
            row = ()
        values.append(1 if winning else -1)
        psi.append(row)
    b = Q(sum(values), 2**n)
    a = psi[0]
    assert sum(a) == 1+b and min((*a, -b)) >= 0
    options = [(j, p) for j, p in [(None, -b), *enumerate(a)] if p]
    rows = []
    for x, row in enumerate(psi):
        assert all(row[j] == psi[x ^ (1 << j)][j] for j in range(n))
        assert sum(sign(x,j) * row[j] for j in range(n)) == values[x]-b
        r = b + sum(a[j] * sign(x,j) for j in range(n))
        expected = {'path': lambda: Q(sign(x,1)+sign(x,2), 2),
                    'and': lambda: Q(-1+sign(x,1), 2),
                    'coord': lambda: sign(x,0),
                    'minus': lambda: -1}[kind]()
        assert r == expected and -1 <= r <= 1
        H = [row[j]-a[j] for j in range(n)]
        assert all(h >= 0 and (x != 0 or h == 0) for h in H)
        assert sum(sign(x,j)*H[j] for j in range(n)) == values[x] - r
        rows.append((values[x], r, H))
    return n, b, options, rows


@cache
def outer(t):
    """Multiaffine Fano extension by interpolation."""
    for j, v in enumerate(t):
        if v not in (-1, 1):
            lower = t[:j] + (-1,) + t[j+1:]
            upper = t[:j] + (1,) + t[j+1:]
            return Q(1-v, 2) * outer(lower) + Q(1+v, 2) * outer(upper)
    return fano(sum(1 << j for j in range(7) if t[j] == 1))


def composition(name, kinds, sections):
    blocks, offsets = [], []
    n = 0
    for kind in kinds:
        block = inner_table(kind)
        blocks.append(block)
        offsets.append(n)
        n += block[0]
    terms = []
    for choices in product(*(b[2] for b in blocks)):
        live = tuple(i for i in range(7) if choices[i][0] is not None)
        positions = [offsets[i] + choices[i][0] for i in live]
        weight = prod(p for _, p in choices)
        terms.append((live, positions, weight, sections[live]))
    assert sum(w for _,_,w,_ in terms) == 1
    mean = outer(tuple(b[1] for b in blocks))
    phi, sum_values = [], 0
    for x in range(2**n):
        local = [(x >> ofs) % (2**b[0]) for ofs, b in zip(offsets, blocks)]
        triples = [b[3][v] for b,v in zip(blocks, local)]
        g, r, H = zip(*triples)
        F, G = outer(g), outer(r)
        sum_values += F
        omega, mixture = [0]*n, 0
        for live, positions, w, P in terms:
            bits = [(x >> j) & 1 for j in positions]
            u = sum(bit << i for i,bit in enumerate(bits))
            full = sum(bit << i for i,bit in zip(live, bits))
            mixture += w * fano(full)
            for j, pos in enumerate(positions):
                omega[pos] += w * P[u & ~(1 << j), j]
        assert mixture == G
        assert sum(sign(x,j)*omega[j] for j in range(n)) == G-mean
        R = []
        telescope = 0
        for i in range(7):
            upper, lower = (g[:i] + (s,) + r[i+1:] for s in (1, -1))
            c = Q(outer(upper)-outer(lower), 2)
            assert c >= 0
            telescope += c * (g[i]-r[i])
            R.extend(c*h for h in H[i])
        assert telescope == F-G
        assert all(y >= 0 and (x != 0 or y == 0) for y in R)
        assert sum(sign(x,j)*R[j] for j in range(n)) == F-G
        row = [a+b for a,b in zip(omega, R)]
        assert sum(sign(x,j)*row[j] for j in range(n)) == F-mean
        phi.append(row)
    assert sum_values == mean * 2**n
    for x, row in enumerate(phi):
        for j in range(n):
            assert row[j] >= phi[0][j] and row[j] == phi[x ^ (1<<j)][j]
    return dict(case=name, dimension=n, vertices=2**n, terms=len(terms), mean=str(mean))


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled (without -O or -OO).")
    assert len(set(lines)) == 7 and all(x.bit_count() == 3 for x in lines)
    assert all(sum(line & mask((i,j)) == mask((i,j)) for line in lines) == 1
               for i,j in combinations(range(1,8), 2))
    assert all((a & b).bit_count() == 1 for a,b in combinations(lines, 2))
    sections = {live: section(live) for n in range(8)
                for live in combinations(range(7), n)}
    cases = [
        ('coordinates', ['coord']*7, (7,128,1,'0')),
        ('path, conjunction, coordinates', ['path','and']+['coord']*5, (11,2048,4,'-9/64')),
        ('path, two conjunctions, coordinates', ['path','and','and']+['coord']*4, (12,4096,8,'-9/32')),
        ('conjunction, path, constant, coordinates', ['and','path','minus']+['coord']*4,
         (10,1024,4,'-27/64'))]
    checks = []
    for name,kinds,expected in cases:
        check = composition(name, kinds, sections)
        assert tuple(check[k] for k in ('dimension','vertices','terms','mean')) == expected
        checks.append(check)
    sets = ({1,2,5,6,7}, {3,4,8,9})
    assert sets[0].isdisjoint(sets[1])
    for s, target in zip(sets, (mask([1,2,3]), mask([1,4,5]))):
        x = mask(s)
        path = inner_table('path')[3][x%16][0]
        conjunction = inner_table('and')[3][(x>>4)%4][0]
        outer_pattern = int(path == 1) + (int(conjunction == 1) << 1) + ((x>>6)<<2)
        assert outer_pattern == target and fano(outer_pattern) == 1
    print(json.dumps(dict(sections=len(sections),
                          section_vertices=sum(2**len(live) for live in sections),
                          cases=checks, composition_vertices=sum(c['vertices'] for c in checks),
                          disjoint_winners_verified=True), indent=2))


if __name__ == '__main__':
    main()
