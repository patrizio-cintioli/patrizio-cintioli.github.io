#!/usr/bin/env python3
"""Audit indipendente dei certificati della bozza Cary, 31 ottobre 2026.

Solo libreria standard; aritmetica esatta, nessun solutore LP. Le famiglie
sono ricostruite dalle definizioni. Le 27 entrate di Table 1 sono trascritte
manualmente: sono DATI DEL CERTIFICATO da verificare, non conclusioni assunte.
Tutti gli altri numeri attesi compaiono soltanto nei confronti finali.
Le verifiche restano attive con python -O (non si usa l'istruzione assert).

Uso: python3 verificatore_indipendente.py [percorso_risultati.json]
Il JSON include tutte le 32 equazioni, tutti gli spigoli primali, spettri
completi, verifiche di divergenza della cochain polare e riepilogo dei test.
Il programma controlla certificati finiti; non sostituisce l'audit logico
degli enunciati originali, dei lemmi e delle estensioni in dimensione arbitraria.
"""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
from math import comb, lcm
from pathlib import Path
import json
import sys


CHECKS = Counter()


def require(condition, label):
    CHECKS[label] += 1
    if not condition:
        raise RuntimeError("VERIFICA FALLITA: " + label)


def equal(actual, expected, label):
    require(actual == expected, label + " [uguaglianza]")


def mask(elements):
    return sum(1 << (i - 1) for i in elements)


def elements(a, n):
    return [i + 1 for i in range(n) if a & (1 << i)]


def x(a, i):
    return 1 if a & (1 << i) else -1


def edges(n, i=None):
    directions = range(n) if i is None else [i]
    return ((k, a) for k in directions for a in range(1 << n)
            if not a & (1 << k))


def mean(values):
    return sum(values, Q(0)) / len(values)


def inner(u, v):
    return mean([a * b for a, b in zip(u, v)])


def centered(u):
    m = mean(u)
    return [v - m for v in u]


def derivative(u, n):
    return {(i, a): (u[a | (1 << i)] - u[a]) / 2
            for i, a in edges(n)}


def divergence(phi, n):
    # Incidenza locale ai vertici: implementazione diretta della formula.
    result = []
    for a in range(1 << n):
        value = Q(0)
        for i in range(n):
            bit = 1 << i
            value += phi[i, a ^ bit] if a & bit else -phi[i, a]
        result.append(value)
    return result


def divergence_by_scatter(phi, n):
    # Seconda implementazione: distribuisce ogni flusso ai suoi due estremi.
    result = [Q(0)] * (1 << n)
    for (i, a), value in phi.items():
        result[a] -= value
        result[a | (1 << i)] += value
    return result


def edge_inner(phi, psi, n):
    return sum((phi[e] * psi[e] for e in edges(n)), Q(0)) / (1 << (n - 1))


def singleton_vertex(u, n):
    return [mean([u[a] * x(a, i) for a in range(1 << n)]) for i in range(n)]


def singleton_edge(u, n):
    du = derivative(u, n)
    return [mean([du[e] for e in edges(n, i)]) for i in range(n)]


def monotone(u, n, label):
    for i, a in edges(n):
        require(u[a] <= u[a | (1 << i)], label)


def intersecting(family, label):
    for a in family:
        for b in family:
            require(bool(a & b), label)


def walsh_direct(u):
    # Somma diretta con interi dopo eliminazione dei denominatori.
    den = lcm(*(v.denominator for v in u))
    integers = [int(v * den) for v in u]
    size = len(u)
    output = []
    for s in range(size):
        sign0 = -1 if s.bit_count() % 2 else 1
        total = sum(v * (-1 if (a & s).bit_count() % 2 else 1)
                    for a, v in enumerate(integers))
        output.append(Q(sign0 * total, size * den))
    return output


def walsh_transform(u):
    # Algoritmo butterfly diverso dalla somma diretta dei caratteri.
    out = list(u)
    step = 1
    while step < len(out):
        for base in range(0, len(out), 2 * step):
            for j in range(step):
                a, b = out[base + j], out[base + j + step]
                out[base + j], out[base + j + step] = a + b, a - b
        step *= 2
    return [v * (-1 if s.bit_count() % 2 else 1) / len(out)
            for s, v in enumerate(out)]


def audit_fourier(u, n, label):
    direct, fast = walsh_direct(u), walsh_transform(u)
    for a, b in zip(direct, fast):
        equal(a, b, label + ": Fourier diretto/butterfly")
    equal(sum((v * v for v in fast), Q(0)), inner(u, u), label + ": Parseval")
    equal([fast[1 << i] for i in range(n)], singleton_vertex(u, n),
          label + ": singleton/spettro")
    equal(singleton_vertex(u, n), singleton_edge(u, n),
          label + ": singleton vertici/spigoli")
    return fast


def audit_conventions():
    n = 3
    # Tutte le coppie delle basi canoniche di C^0 e C^1.
    for vertex in range(1 << n):
        u = [Q(a == vertex) for a in range(1 << n)]
        du = derivative(u, n)
        for edge in edges(n):
            phi = {e: Q(e == edge) for e in edges(n)}
            equal(edge_inner(du, phi, n), inner(u, divergence(phi, n)),
                  "aggiunzione su tutte le coppie delle basi n=3")
    n = 5
    u = [Q(((a * a + 7 * a) % 23) - 11, 7) for a in range(1 << n)]
    phi = {(i, a): Q(((19 * a + 11 * i) % 29) - 14, i + 3)
           for i, a in edges(n)}
    equal(edge_inner(derivative(u, n), phi, n), inner(u, divergence(phi, n)),
          "aggiunzione con dati arbitrari a segno variabile")
    equal(divergence(phi, n), divergence_by_scatter(phi, n),
          "due procedure per la divergenza")
    equal(singleton_vertex(u, n), singleton_edge(u, n),
          "normalizzazione singleton su funzione arbitraria")
    for i in range(n):
        xi = [Q(x(a, i)) for a in range(1 << n)]
        equal(divergence(derivative(xi, n), n), xi, "delta d x_i = x_i")
    # Il maggiorante del Lemma 1.1 deve funzionare anche con minimi negativi.
    lam = [Q(sum((i + 1) * x(a, i) for i in range(n)))
           for a in range(1 << n)]
    alpha = singleton_vertex(lam, n)
    minima = [min(phi[e] for e in edges(n, i)) for i in range(n)]
    require(all(t < 0 for t in minima), "test con tutti i minimi negativi")
    require(sum(a * t for a, t in zip(alpha, minima)) <= inner(lam, divergence(phi, n)),
            "Lemma 1.1 controllo a segno variabile")
    return {"basis_pairs_n3": 8 * 12, "signed_test_minima": minima,
            "note": "Le identita generali richiedono anche la dimostrazione matematica."}


def audit_51():
    n = 5
    triples = [(1, 2, 3), (2, 3, 4), (1, 2, 5), (1, 3, 5),
               (2, 3, 5), (1, 4, 5), (2, 4, 5)]
    triple_masks = {mask(t) for t in triples}
    family = {a for a in range(1 << n) if a in triple_masks or a.bit_count() >= 4}
    # Seconda costruzione: unione di T e combinazioni di cardinalita 4 e 5.
    family2 = triple_masks | {mask(t) for k in (4, 5)
                             for t in combinations(range(1, n + 1), k)}
    equal(family, family2, "5.1: due ricostruzioni famiglia")
    f = [Q(2 * (a in family) - 1) for a in range(1 << n)]
    monotone(f, n, "5.1: monotonia di f")
    intersecting(family, "5.1: famiglia intersecante")
    equal(len(family), 13, "5.1: cardinalita")
    equal(mean(f), Q(-3, 16), "5.1: media")
    # Testimone esplicito di non massimalita.
    extra = mask((1, 2, 4))
    require(extra not in family and all(extra & a for a in family),
            "5.1: famiglia non massimale")
    # Trascrizione, per COLONNE, delle sole entrate non nulle di Table 1.
    table = [
        {2: 3, 4: 9, 6: 6, 22: 6, 24: 4, 30: 4},
        {5: 9, 12: 15, 13: 9, 17: 16, 20: 15, 24: 12, 28: 17, 29: 3},
        {16: 4, 18: 5, 19: 7},
        {},
        {0: 1, 1: 7, 3: 12, 5: 15, 6: 5, 8: 7, 9: 13, 10: 9, 11: 15, 13: 12},
    ]
    table_records = []
    for i, col in enumerate(table):
        for a, value in sorted(col.items()):
            require(0 <= a < (1 << n) and not a & (1 << i), "5.1: entrata su spigolo valido")
            require(value > 0, "5.1: entrata h positiva")
            table_records.append({"direction": i + 1, "bottom_mask": a,
                                  "bottom_set": elements(a, n),
                                  "top_mask": a | (1 << i), "16h": value})
    equal(len(table_records), 27, "5.1: numero entrate non nulle")
    t = [Q(v, 16) for v in (3, 1, 4, 3, 1)]
    h = {(i, a): Q(table[i].get(a, 0), 16) for i, a in edges(n)}
    phi = {(i, a): t[i] + h[i, a] for i, a in edges(n)}
    div = divergence(phi, n)
    div_t = divergence({(i, a): t[i] for i, a in edges(n)}, n)
    div_h = divergence(h, n)
    equal(div, divergence_by_scatter(phi, n), "5.1: divergenza due metodi")
    divrows = []
    for a in range(1 << n):
        rhs = f[a] - mean(f)
        equal(div[a], rhs, "5.1: ogni equazione di divergenza")
        divrows.append({"mask": a, "set": elements(a, n), "winning": a in family,
                        "16delta_t": 16 * div_t[a], "16delta_h": 16 * div_h[a],
                        "16delta_phi": 16 * div[a], "16rhs": 16 * rhs,
                        "residual": div[a] - rhs})
    minima = [min(phi[e] for e in edges(n, i)) for i in range(n)]
    argmin = [[a for _, a in edges(n, i) if phi[i, a] == minima[i]] for i in range(n)]
    bottom = [phi[i, 0] for i in range(n)]
    equal(minima, t, "5.1: minimi effettivi")
    equal(bottom[4], Q(2, 16), "5.1: valore inferiore quinta direzione")
    require(bottom[4] > minima[4], "5.1: nonpolarita")
    U = [
        [Q(bool(a & mask((4,)))) for a in range(1 << n)],
        [Q(a & mask((3, 4)) == mask((3, 4))) for a in range(1 << n)],
        [Q(any(a & mask(s) == mask(s) for s in ((1, 2, 4), (1, 3, 4), (3, 4, 5))))
         for a in range(1 << n)],
    ]
    rows = []
    expected_singletons = [[Q(0), Q(0), Q(0), Q(1, 2), Q(0)],
                           [Q(0), Q(0), Q(1, 4), Q(1, 4), Q(0)],
                           [Q(1, 8), Q(1, 16), Q(1, 8), Q(1, 4), Q(1, 16)]]
    expected_cov = [Q(3, 32), Q(7, 64), Q(7, 64)]
    for j, indicator in enumerate(U):
        monotone(indicator, n, "5.1: monotonia U")
        spectrum = audit_fourier(indicator, n, "5.1: U" + str(j))
        singleton = [spectrum[1 << i] for i in range(n)]
        equal(singleton, expected_singletons[j], "5.1: singleton di U")
        win = sum(bool(indicator[a]) and a in family for a in range(1 << n))
        lose = sum(bool(indicator[a]) and a not in family for a in range(1 << n))
        cov = inner(indicator, centered(f))
        equal(cov, ((1 - mean(f)) * win + (-1 - mean(f)) * lose) / (1 << n),
              "5.1: covarianza U due metodi")
        equal(cov, expected_cov[j], "5.1: covarianza U dichiarata")
        rows.append({"j": j, "winning_count": win, "losing_count": lose,
                     "singleton": singleton, "covariance": cov, "spectrum": spectrum})
    lam = [4 * U[0][a] + 8 * U[1][a] + 16 * U[2][a] for a in range(1 << n)]
    monotone(lam, n, "5.1: monotonia lambda")
    lambda_spectrum = audit_fourier(lam, n, "5.1: lambda")
    f_spectrum = audit_fourier(f, n, "5.1: f")
    alpha = singleton_vertex(lam, n)
    equal(alpha, list(map(Q, (2, 1, 4, 8, 1))), "5.1: pesi duali")
    primal = sum(a * b for a, b in zip(alpha, minima))
    dual = inner(lam, centered(f))
    equal(primal, dual, "5.1: certificati primale/duale coincidenti")
    equal(primal, Q(3), "5.1: ottimo dichiarato")
    equal(edge_inner(derivative(lam, n), phi, n), dual, "5.1: aggiunzione certificato")
    complementary = []
    for e in edges(n):
        slack_product = derivative(lam, n)[e] * h[e]
        equal(slack_product, Q(0), "5.1: complementarita su ogni spigolo")
        complementary.append(slack_product)
    all_edges = [{"direction": i + 1, "bottom_mask": a, "phi": phi[i, a],
                  "h": h[i, a], "d_lambda": derivative(lam, n)[i, a]}
                 for i, a in edges(n)]
    return {"n": n, "vertices": 1 << n, "edges": len(phi),
            "family_masks": sorted(family), "family_size": len(family), "mean_f": mean(f),
            "table_entries": table_records, "all_edges": all_edges,
            "divergence_equations": divrows, "minima": minima, "argmin_masks": argmin,
            "bottom_values": bottom, "polar": bottom == minima,
            "dual_upsets": rows, "alpha": alpha, "primal": primal, "dual": dual,
            "f_spectrum": f_spectrum, "lambda_spectrum": lambda_spectrum}, f, phi, lam


def conditional_cochain(q, order):
    """E_future[(q(x_i=+1)-q(x_i=-1))/2] per ogni spigolo.

    Enumera direttamente tutti i possibili futuri, senza usare Fourier o
    divergenza per costruire i valori. Nessuna informazione sui risultati
    attesi entra nella costruzione.
    """
    n = len(order)
    result = {}
    for pos, i in enumerate(order):
        past, future = order[:pos], order[pos + 1:]
        for compact in range(1 << len(past)):
            prefix = sum((1 << j) for k, j in enumerate(past) if compact & (1 << k))
            total = Q(0)
            for tail in range(1 << len(future)):
                a = prefix | sum((1 << j) for k, j in enumerate(future) if tail & (1 << k))
                total += (q[a | (1 << i)] - q[a]) / 2
            value = total / (1 << len(future))
            for tail in range(1 << len(future)):
                a = prefix | sum((1 << j) for k, j in enumerate(future) if tail & (1 << k))
                result[i, a] = value
    return result


def audit_polarity(q, f):
    n = 10
    a = mean(q)
    mean_f = mean(f)
    records = []
    orders = [list(range(n)), list(reversed(range(n))), [0, 5, 1, 6, 2, 7, 3, 8, 4, 9]]
    for order in orders:
        psi = conditional_cochain(q, order)
        for v in psi.values():
            require(v >= 0, "4.2: nonnegativita psi")
        div = divergence(psi, n)
        equal(div, divergence_by_scatter(psi, n), "4.2: divergenza psi due metodi")
        for vertex, value in enumerate(div):
            equal(value, q[vertex] - a, "4.2: ogni divergenza psi")
            telescoping = sum(x(vertex, i) * psi[i, vertex & ~(1 << i)] for i in range(n))
            equal(telescoping, q[vertex] - a, "4.2: identita telescopica ad ogni vertice")
        # Ulteriore controllo del vero incremento delle aspettative condizionate.
        for vertex in range(1 << n):
            previous = a
            for pos, i in enumerate(order):
                fixed_mask = sum(1 << j for j in order[:pos + 1])
                matching = [q[b] for b in range(1 << n) if b & fixed_mask == vertex & fixed_mask]
                current = mean(matching)
                equal(current - previous, x(vertex, i) * psi[i, vertex & ~(1 << i)],
                      "4.2: incremento condizionato diretto")
                previous = current
        Phi = {(i, v): (1 + x(v, n)) * psi[i, v & ((1 << n) - 1)] if i < n else a
               for i, v in edges(n + 1)}
        dPhi = divergence(Phi, n + 1)
        equal(dPhi, divergence_by_scatter(Phi, n + 1), "4.2: divergenza Phi due metodi")
        for v in range(1 << (n + 1)):
            equal(dPhi[v], f[v] - mean_f, "4.2: ogni divergenza Phi")
        minima = [min(Phi[e] for e in edges(n + 1, i)) for i in range(n + 1)]
        bottom = [Phi[i, 0] for i in range(n + 1)]
        equal(bottom, minima, "4.2: polarita in tutte le direzioni")
        records.append({"coordinate_order": [i + 1 for i in order],
                        "psi_edges": len(psi), "psi_vertices_checked": len(div),
                        "Phi_edges": len(Phi), "Phi_vertices_checked": len(dPhi),
                        "Phi_minima": minima, "Phi_bottom": bottom,
                        "all_divergence_residuals_Phi": [dPhi[v] - f[v] + mean_f
                                                        for v in range(len(f))]})
    return records


def audit_54():
    n, z = 11, 10
    b1, b2 = mask(range(1, 6)), mask(range(6, 11))
    H = {s for s in range(1 << 10) if s & b1 == b1 or s & b2 == b2 or s.bit_count() >= 8}
    # Costruzione combinatoria indipendente: per le cardinalita <8 contiamo
    # le estensioni di uno dei due blocchi; da 8 in poi tutte le combinazioni.
    combinatorial_counts = {k: 0 if k < 5 else 2 * comb(5, k - 5) if k < 8 else comb(10, k)
                            for k in range(11)}
    direct_counts = {k: sum(s.bit_count() == k for s in H) for k in range(11)}
    equal(direct_counts, combinatorial_counts, "5.4: distribuzione due metodi")
    equal([direct_counts[k] for k in range(5, 11)], [2, 10, 20, 45, 10, 1],
          "5.4: distribuzione dichiarata")
    q = [Q(s in H) for s in range(1 << 10)]
    family = {s | (1 << z) for s in H}
    f = [Q(2 * (s in family) - 1) for s in range(1 << n)]
    monotone(q, 10, "5.4: monotonia H")
    monotone(f, n, "5.4: monotonia f")
    intersecting(family, "5.4: intersezione F")
    require(all(s & (1 << z) for s in family), "5.4: coordinata comune z")
    extra = 1 << z
    require(extra not in family and all(extra & s for s in family), "5.4: non massimalita")
    equal(len(H), 88, "5.4: cardinalita H")
    equal(len(family), len(H), "5.4: cardinalita F uguale H")
    mu = mean(f)
    variance = inner(centered(f), centered(f))
    equal(mu, Q(-117, 128), "5.4: media")
    equal(variance, 1 - mu * mu, "5.4: varianza due metodi")
    equal(variance, Q(2695, 16384), "5.4: varianza dichiarata")
    # Terzo conteggio delle singleton vecchie: fissa i=1 e conta separatamente
    # presenza/assenza nelle cardinalita 5,6,7, e poi negli strati completi.
    plus = sum(comb(5, k - 5) + (comb(4, k - 6) if k >= 6 else 0)
               for k in range(5, 8)) + sum(comb(9, k - 1) for k in range(8, 11))
    minus = sum(comb(4, k - 5) for k in range(5, 8)) + sum(comb(9, k) for k in range(8, 10))
    equal(plus - minus, sum(x(s, 0) for s in H), "5.4: singleton via conteggio fissata coordinata")
    total_signed = sum((2 * k - 10) * direct_counts[k] for k in range(11))
    equal(total_signed, sum(sum(x(s, i) for i in range(10)) for s in H),
          "5.4: somma segnata strati/vertici")
    equal(total_signed, 460, "5.4: somma segnata dichiarata")
    for i in range(10):
        equal(sum(x(s, i) for s in H), Q(total_signed, 10), "5.4: transitive singleton verificate")
    coeff_f = singleton_vertex(f, n)
    equal(coeff_f, [Q(23, 512)] * 10 + [Q(11, 128)], "5.4: singleton f dichiarate")
    G = [[Q((s & b) == b and bool(s & (1 << z))) for s in range(1 << n)] for b in (b1, b2)]
    for j, gj in enumerate(G):
        require(all(not gj[s] or s in family for s in range(1 << n)), "5.4: G contenuta F")
        equal(mean(gj), Q(1, 64), "5.4: media G")
        expected = [Q(1, 64) if i == z or (b1 if j == 0 else b2) & (1 << i) else Q(0)
                    for i in range(n)]
        equal(singleton_vertex(gj, n), expected, "5.4: singleton G")
        equal(singleton_vertex(gj, n), singleton_edge(gj, n), "5.4: singleton G vertici/spigoli")
    lam = [Q(11, 4) * (G[0][s] + G[1][s]) + Q(1, 512) * sum(x(s, i) for i in range(10))
           for s in range(1 << n)]
    monotone(lam, n, "5.4: monotonia lambda")
    coeff_lambda = singleton_vertex(lam, n)
    equal(coeff_f, coeff_lambda, "5.4: singleton lambda=f")
    covariance = inner(centered(f), centered(lam))
    covariance2 = inner(f, lam) - mu * mean(lam)
    g_covariances = [inner(gj, centered(f)) for gj in G]
    for v in g_covariances:
        equal(v, (1 - mu) / 64, "5.4: covarianza G via inclusione")
        equal(v, Q(245, 8192), "5.4: covarianza G dichiarata")
    covariance3 = Q(11, 4) * sum(g_covariances) + Q(1, 512) * sum(coeff_f[:10])
    equal(covariance, covariance2, "5.4: covarianza due definizioni")
    equal(covariance, covariance3, "5.4: covarianza per decomposizione")
    gap = covariance - variance
    equal(gap, Q(115, 131072), "5.4: gap dichiarato")
    require(gap > 0, "5.4: ostruzione stretta")
    f_spectrum = audit_fourier(f, n, "5.4: f")
    lambda_spectrum = audit_fourier(lam, n, "5.4: lambda")
    equal(sum((f_spectrum[s] * lambda_spectrum[s] for s in range(1, 1 << n)), Q(0)),
          covariance, "5.4: covarianza via spettri completi")
    # Calcolo indipendente dei coefficienti della prova diretta 3.1.
    T_lower_bound = sum(coeff_f[:10])
    saturation_T_coefficient = coeff_f[0] / coeff_f[z]
    saturation_rhs = variance / coeff_f[z]
    G_rhs = g_covariances[0] / singleton_vertex(G[0], n)[z]
    subtraction_T_coefficient = Q(1, 2) - saturation_T_coefficient
    equal(T_lower_bound, Q(115, 256), "3.1: limite inferiore T")
    equal(saturation_T_coefficient, Q(23, 44), "3.1: coefficiente T")
    equal(saturation_rhs, Q(245, 128), "3.1: termine noto saturazione")
    equal(G_rhs, saturation_rhs, "3.1: coincidenza termini noti")
    equal(subtraction_T_coefficient, Q(-1, 44), "3.1: sottrazione")
    require(subtraction_T_coefficient * T_lower_bound < 0, "3.1: contraddizione esatta")
    polarity = audit_polarity(q, f)
    return {"n": n, "vertices": 1 << n, "edges": n * (1 << (n - 1)),
            "H_masks": sorted(H), "H_size": len(H), "size_distribution": direct_counts,
            "size_distribution_combinatorial": combinatorial_counts,
            "fixed_coordinate_plus_count": plus, "fixed_coordinate_minus_count": minus,
            "signed_sum": total_signed, "mean_f": mu, "variance": variance,
            "singleton_f": coeff_f, "singleton_lambda": coeff_lambda,
            "mean_lambda": mean(lam), "covariance_G": g_covariances,
            "covariance": covariance, "gap": gap,
            "f_spectrum": f_spectrum, "lambda_spectrum": lambda_spectrum,
            "direct_maxima_proof": {"T_lower_bound": T_lower_bound,
                                     "saturation_T_coefficient": saturation_T_coefficient,
                                     "saturation_rhs": saturation_rhs,
                                     "G_rhs": G_rhs,
                                     "subtraction_T_coefficient": subtraction_T_coefficient},
            "polarity_checks": polarity}, f, lam


def audit_dummy_extensions(f5, phi5, lam5, f11, lam11):
    output = []
    for n in (6, 7):
        f = [f5[s & 31] for s in range(1 << n)]
        eps = [Q(j + 1, j + 2) for j in range(n - 5)]
        lam = [lam5[s & 31] + sum(eps[i - 5] * x(s, i) for i in range(5, n))
               for s in range(1 << n)]
        phi = {(i, s): phi5[i, s & 31] if i < 5 else Q(0) for i, s in edges(n)}
        equal(divergence(phi, n), centered(f), "4.1: estensione 5.1 divergenza")
        coeff = singleton_vertex(lam, n)
        require(all(c > 0 for c in coeff), "4.1: tutti i pesi restano positivi")
        minima = [min(phi[e] for e in edges(n, i)) for i in range(n)]
        equal(sum(a * b for a, b in zip(coeff, minima)), Q(3), "4.1: estensione primale")
        equal(inner(lam, centered(f)), Q(3), "4.1: estensione duale")
        require(phi[4, 0] > minima[4], "4.1: persistenza nonpolarita")
        monotone(f, n, "4.1: estensione 5.1 monotonia f")
        monotone(lam, n, "4.1: estensione 5.1 monotonia lambda")
        intersecting([s for s in range(1 << n) if f[s] == 1], "4.1: estensione 5.1 intersezione")
        output.append({"example": "5.1", "n": n, "extra_weights": eps,
                       "all_weights": coeff, "primal_and_dual": Q(3)})
    for n in (12, 13):
        f = [f11[s & 2047] for s in range(1 << n)]
        lam = [lam11[s & 2047] for s in range(1 << n)]
        coeff = singleton_vertex(f, n)
        equal(coeff, singleton_vertex(lam, n), "4.1: estensione 5.4 singleton coincidono")
        equal(coeff[11:], [Q(0)] * (n - 11), "4.1: nuove singleton nulle")
        gap = inner(centered(f), centered(lam)) - inner(centered(f), centered(f))
        equal(gap, Q(115, 131072), "4.1: persistenza gap 5.4")
        monotone(f, n, "4.1: estensione 5.4 monotonia f")
        monotone(lam, n, "4.1: estensione 5.4 monotonia lambda")
        intersecting([s for s in range(1 << n) if f[s] == 1], "4.1: estensione 5.4 intersezione")
        output.append({"example": "5.4", "n": n, "extra_singletons": coeff[11:], "gap": gap})
    return output


def json_exact(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): json_exact(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_exact(v) for v in value]
    return value


def main():
    conventions = audit_conventions()
    result51, f5, phi5, lam5 = audit_51()
    result54, f11, lam11 = audit_54()
    dummy = audit_dummy_extensions(f5, phi5, lam5, f11, lam11)
    output = {"status": "PASS", "arithmetic": "fractions.Fraction; no floating point",
              "conventions": conventions, "conjecture_51": result51,
              "conjecture_54": result54, "dummy_extensions_finite_tests": dummy,
              "check_counts": dict(sorted(CHECKS.items())), "total_checks": sum(CHECKS.values())}
    destination = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("risultati_verifica_indipendente.json")
    destination.write_text(json.dumps(json_exact(output), indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("PASS:", sum(CHECKS.values()), "controlli esatti in", len(CHECKS), "categorie")
    print("5.1: 27 entrate valide, 80 spigoli, 32/32 divergenze, minimi", result51["minima"])
    print("5.1: nonpolare; certificato primale = duale =", result51["primal"])
    print("5.4: |H| =", result54["H_size"], "; Var =", result54["variance"],
          "; Cov =", result54["covariance"], "; gap =", result54["gap"])
    print("4.2: 3 ordini controllati; per ordine 1024 divergenze psi e 2048 divergenze Phi.")
    print("Spettri Fourier completi controllati con somma diretta e trasformata butterfly.")
    print("Risultati:", destination.resolve())


if __name__ == "__main__":
    main()
