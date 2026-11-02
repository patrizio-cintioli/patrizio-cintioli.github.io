#!/usr/bin/env python3
"""Audit autonomo esatto dei due certificati nella bozza su Cary.

Python >= 3.10; solo libreria standard. Nessun solver e nessun float.
Esempio:
    python3 verificatore_indipendente_Cary.py --output-dir risultati
    python3 -O verificatore_indipendente_Cary.py --output-dir risultati_O

Le famiglie sono ricostruite dalle loro definizioni. La tabella h e i pesi
sono dati del certificato sottoposto a verifica, non risultati presupposti.
I valori dichiarati nella bozza sono confrontati soltanto dopo il calcolo.
Il controllo dei certificati finiti NON sostituisce le dimostrazioni dei
lemmi universali, l'interpretazione delle congetture o il controllo di v5.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from math import comb
from pathlib import Path
import platform
import sys
from time import perf_counter_ns
from typing import Any

ZERO = Q(0)
ONE = Q(1)
CHECKS: Counter[str] = Counter()
LOG: list[str] = []


def check(condition: bool, name: str) -> None:
    """Un controllo resta attivo anche con python -O."""
    CHECKS[name] += 1
    if not condition:
        raise ArithmeticError(f"CONTROLLO FALLITO: {name}")


def equal(actual: Any, expected: Any, name: str) -> None:
    CHECKS[name] += 1
    if actual != expected:
        raise ArithmeticError(f"CONTROLLO FALLITO: {name}\n"
                              f"ottenuto={actual!r}\natteso={expected!r}")


def say(message: str) -> None:
    LOG.append(message)
    print(message)


def mask(indices: tuple[int, ...] | list[int]) -> int:
    """Indici matematici 1,...,n; il bit meno significativo e' la coordinata 1."""
    return sum(1 << (i - 1) for i in indices)


def elements(a: int, n: int) -> list[int]:
    return [i + 1 for i in range(n) if a & (1 << i)]


def x(a: int, i: int) -> int:
    """i e' un indice Python 0,...,n-1."""
    return 1 if a & (1 << i) else -1


def bases(n: int, i: int):
    return (a for a in range(1 << n) if not (a & (1 << i)))


def mean(values) -> Q:
    values = list(values)
    return sum(values, ZERO) / len(values)


def scalar(u: list[Q], v: list[Q]) -> Q:
    equal(len(u), len(v), "dimensioni prodotto scalare")
    return mean(a * b for a, b in zip(u, v))


def variance(values: list[Q]) -> Q:
    mu = mean(values)
    return mean((v - mu) ** 2 for v in values)


def covariance(u: list[Q], v: list[Q]) -> Q:
    return scalar(u, v) - mean(u) * mean(v)


def singleton_vertex(values: list[Q], n: int) -> list[Q]:
    return [mean(values[a] * x(a, i) for a in range(1 << n))
            for i in range(n)]


def derivative(values: list[Q], n: int) -> list[dict[int, Q]]:
    return [{a: (values[a | (1 << i)] - values[a]) / 2
             for a in bases(n, i)} for i in range(n)]


def singleton_edges(values: list[Q], n: int) -> list[Q]:
    return [mean(component.values()) for component in derivative(values, n)]


def divergence(phi: list[dict[int, Q]], n: int) -> list[Q]:
    # Formulazione per vertice, senza riutilizzare la formula per spigolo.
    result = []
    for a in range(1 << n):
        val = ZERO
        for i in range(n):
            bit = 1 << i
            if a & bit:
                val += phi[i][a ^ bit]
            else:
                val -= phi[i][a]
        result.append(val)
    return result


def divergence_by_scatter(phi: list[dict[int, Q]], n: int) -> list[Q]:
    # Seconda procedura: distribuzione dei flussi sui due estremi.
    result = [ZERO] * (1 << n)
    for i, comp in enumerate(phi):
        for a, value in comp.items():
            result[a] -= value
            result[a | (1 << i)] += value
    return result


def edge_scalar(du: list[dict[int, Q]], phi: list[dict[int, Q]]) -> Q:
    return sum((mean(du[i][a] * phi[i][a] for a in du[i])
                for i in range(len(phi))), ZERO)


def check_cube(values: list[Q], n: int, prefix: str) -> dict:
    equal(len(values), 1 << n, prefix + " numero vertici")
    dv = derivative(values, n)
    for i, comp in enumerate(dv):
        equal(len(comp), 1 << (n - 1), prefix + " numero spigoli direzione")
        for a, value in comp.items():
            check(value >= 0, prefix + " monotonia su ogni spigolo")
    fv = singleton_vertex(values, n)
    fe = [mean(comp.values()) for comp in dv]
    equal(fv, fe, prefix + " Fourier vertici = Fourier spigoli")
    return {"vertices": 1 << n, "edges": n * (1 << (n - 1)),
            "mean": mean(values), "variance": variance(values),
            "singleton_fourier": fv}


def check_intersecting(family: set[int], prefix: str) -> None:
    for a in family:
        for b in family:
            check(bool(a & b), prefix + " intersezione ogni coppia ordinata")


def fourier_all(values: list[Q]) -> list[Q]:
    """Walsh-Hadamard O(n 2^n), convenzione x_i=+1 sul bit 1."""
    a = list(values)
    length = 1
    while length < len(a):
        for start in range(0, len(a), 2 * length):
            for j in range(start, start + length):
                u, v = a[j], a[j + length]
                a[j], a[j + length] = u + v, u - v
        length *= 2
    return [((-1) ** s.bit_count()) * val / len(a)
            for s, val in enumerate(a)]


def check_fourier(values: list[Q], n: int, prefix: str) -> list[Q]:
    coefficients = fourier_all(values)
    equal(coefficients[0], mean(values), prefix + " Fourier costante")
    equal([coefficients[1 << i] for i in range(n)],
          singleton_vertex(values, n), prefix + " trasformata vs singleton diretti")
    equal(sum((v * v for v in coefficients), ZERO),
          mean(v * v for v in values), prefix + " Parseval")
    return coefficients


def check_cochain(phi: list[dict[int, Q]], values: list[Q], n: int,
                  prefix: str) -> dict:
    for i, comp in enumerate(phi):
        equal(set(comp), set(bases(n, i)), prefix + " dominio esatto degli spigoli")
    div = divergence(phi, n)
    equal(div, divergence_by_scatter(phi, n), prefix + " due formule divergenza")
    mu = mean(values)
    for a in range(1 << n):
        equal(div[a], values[a] - mu, prefix + " divergenza per ogni vertice")
    equal(mean(div), ZERO, prefix + " media divergenza zero")
    equal(edge_scalar(derivative(values, n), phi), scalar(values, div),
          prefix + " aggiunzione sul dato f")
    # Identita' E(phi_i)=fhat(i), verificata per ciascuna coordinata.
    equal([mean(comp.values()) for comp in phi], singleton_vertex(values, n),
          prefix + " medie componenti = singleton f")
    mins = [min(comp.values()) for comp in phi]
    maxs = [max(comp.values()) for comp in phi]
    bottom = [comp[0] for comp in phi]
    return {"minima": mins, "maxima": maxs, "bottom": bottom,
            "polar": bottom == mins, "divergence": div}


def verify_51() -> tuple[dict, dict]:
    n = 5
    triples = ((1, 2, 3), (2, 3, 4), (1, 2, 5), (1, 3, 5),
               (2, 3, 5), (1, 4, 5), (2, 4, 5))
    t_masks = {mask(t) for t in triples}
    family = {a for a in range(1 << n) if a in t_masks or a.bit_count() >= 4}
    f = [Q(2 * int(a in family) - 1) for a in range(1 << n)]
    fdata = check_cube(f, n, "5.1 f")
    check_intersecting(family, "5.1 F")
    maximality_witness = mask((1, 2, 4))
    check(maximality_witness not in family and all(maximality_witness & a for a in family),
          "5.1 famiglia non massimale: testimone esplicito")
    # Conteggio combinatorio distinto dall'enumerazione dei vertici.
    equal(len(family), len(triples) + comb(5, 4) + comb(5, 5), "5.1 conteggio combinatorio")
    equal(len(family), 13, "5.1 cardinalita dichiarata")
    equal(mean(f), Q(-3, 16), "5.1 media dichiarata")

    # Trascrizione del certificato da verificare: indici 1,...,5 esterni.
    table = [
        [(2, 3), (4, 9), (6, 6), (22, 6), (24, 4), (30, 4)],
        [(5, 9), (12, 15), (13, 9), (17, 16), (20, 15), (24, 12), (28, 17), (29, 3)],
        [(16, 4), (18, 5), (19, 7)],
        [],
        [(0, 1), (1, 7), (3, 12), (5, 15), (6, 5), (8, 7), (9, 13), (10, 9), (11, 15), (13, 12)],
    ]
    h = [{a: ZERO for a in bases(n, i)} for i in range(n)]
    for i, entries in enumerate(table):
        seen = set()
        for a, numerator in entries:
            check(a not in seen, "5.1 tabella nessun duplicato")
            seen.add(a)
            check(0 <= a < (1 << n) and not (a & (1 << i)),
                  "5.1 tabella ogni entrata e uno spigolo valido")
            check(numerator > 0, "5.1 tabella positivita ogni entrata")
            h[i][a] = Q(numerator, 16)
    equal(sum(len(entries) for entries in table), 27, "5.1 tabella 27 entrate")
    equal(sum(v != 0 for comp in h for v in comp.values()), 27, "5.1 27 entrate effettive")
    t = [Q(num, 16) for num in (3, 1, 4, 3, 1)]
    phi = [{a: t[i] + h[i][a] for a in bases(n, i)} for i in range(n)]
    pdata = check_cochain(phi, f, n, "5.1 primale")
    equal(pdata["minima"], t, "5.1 minimi dichiarati")
    equal(pdata["bottom"][4], Q(2, 16), "5.1 quinta componente al fondo")
    check(not pdata["polar"], "5.1 cochain nonpolare")
    alpha = [Q(v) for v in (2, 1, 4, 8, 1)]
    primal = sum((a * b for a, b in zip(alpha, pdata["minima"])), ZERO)
    equal(primal, Q(3), "5.1 obiettivo primale")

    required = [mask((1, 2, 4)), mask((1, 3, 4)), mask((3, 4, 5))]
    upsets = [
        {a for a in range(32) if a & mask((4,))},
        {a for a in range(32) if a & mask((3, 4)) == mask((3, 4))},
        {a for a in range(32) if any(a & r == r for r in required)},
    ]
    indicators = [[Q(int(a in u)) for a in range(32)] for u in upsets]
    lam = [4 * indicators[0][a] + 8 * indicators[1][a] + 16 * indicators[2][a]
           for a in range(32)]
    ldata = check_cube(lam, n, "5.1 lambda")
    expected = [[Q(0), Q(0), Q(0), Q(1, 2), Q(0)],
                [Q(0), Q(0), Q(1, 4), Q(1, 4), Q(0)],
                [Q(1, 8), Q(1, 16), Q(1, 8), Q(1, 4), Q(1, 16)]]
    us = []
    for j, (u, indicator) in enumerate(zip(upsets, indicators)):
        check_cube(indicator, n, "5.1 U" + str(j))
        fv = singleton_vertex(indicator, n)
        equal(fv, expected[j], "5.1 coefficienti U" + str(j))
        us.append({"size": len(u), "winning_vertices": len(u & family),
                   "losing_vertices": len(u - family), "singleton_fourier": fv,
                   "covariance_with_f": covariance(indicator, f)})
    equal(ldata["singleton_fourier"], alpha, "5.1 Fourier lambda = alpha")
    equal([u["covariance_with_f"] for u in us],
          [Q(3, 32), Q(7, 64), Q(7, 64)], "5.1 covarianze upsets dichiarate")
    bound = covariance(lam, f)
    equal(bound, primal, "5.1 certificati primale duale coincidono")
    equal(bound, edge_scalar(derivative(lam, n), phi), "5.1 aggiunzione per lambda")
    dl = derivative(lam, n)
    for i in range(n):
        for a in bases(n, i):
            equal(dl[i][a] * h[i][a], ZERO, "5.1 complementarita su ogni spigolo")
    # Un certificato duale globale e' dato da d(lambda)>=0 e singleton=alpha.
    # L'implicazione per OGNI cochain e' il Lemma 1.1, non una scansione numerica.
    ff, fl = check_fourier(f, n, "5.1 f"), check_fourier(lam, n, "5.1 lambda")
    equal(sum((ff[s] * fl[s] for s in range(1, 32)), ZERO), bound,
          "5.1 covarianza Fourier completa")
    t_cochain = [{a: t[i] for a in bases(n, i)} for i in range(n)]
    div_t, div_h = divergence(t_cochain, n), divergence(h, n)
    for a in range(32):
        equal(div_t[a] + div_h[a], pdata["divergence"][a], "5.1 decomposizione delta t + delta h")
    vertices = [{"mask": a, "subset": elements(a, n), "f": f[a],
                 "delta_t": div_t[a], "delta_h": div_h[a],
                 "divergence": pdata["divergence"][a], "target": f[a] - mean(f),
                 "lambda": lam[a]} for a in range(32)]
    report = {"family_masks": sorted(family), "f": fdata, "h_nonzero_entries": table,
              "not_maximal_intersecting_witness_mask": maximality_witness,
              "primal": pdata, "weights": alpha, "objective": primal,
              "dual": ldata, "upsets": us, "dual_bound": bound,
              "all_32_vertex_equations": vertices,
              "all_fourier_f": ff, "all_fourier_lambda": fl,
              "certificate_verified": True}
    data = {"f": f, "phi": phi, "lambda": lam, "alpha": alpha}
    return report, data


def verify_54() -> tuple[dict, dict]:
    n, nz = 11, 10
    b1, b2, zbit = mask((1, 2, 3, 4, 5)), mask((6, 7, 8, 9, 10)), 1 << nz
    hfamily = {s for s in range(1 << 10)
               if (s & b1 == b1) or (s & b2 == b2) or s.bit_count() >= 8}
    family = {s | zbit for s in hfamily}
    f = [Q(2 * int(a in family) - 1) for a in range(1 << n)]
    fdata = check_cube(f, n, "5.4 f")
    check_intersecting(family, "5.4 F")
    check(zbit not in family and all(zbit & a for a in family),
          "5.4 famiglia non massimale: singleton z")
    histogram = {j: sum(s.bit_count() == j for s in hfamily) for j in range(11)}
    # Formula distinta: livelli 5,6,7 disgiunti per blocco; da 8 tutti i sottoinsiemi.
    combinatorial = {j: 0 if j < 5 else (2 * comb(5, j - 5) if j < 8 else comb(10, j))
                     for j in range(11)}
    equal(histogram, combinatorial, "5.4 istogramma vs formula combinatoria")
    equal(histogram, {0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 2, 6: 10, 7: 20, 8: 45, 9: 10, 10: 1},
          "5.4 istogramma dichiarato")
    equal(len(hfamily), 88, "5.4 cardinalita H")
    equal(len(family), 88, "5.4 cardinalita F")
    equal(mean(f), Q(-117, 128), "5.4 media dichiarata")
    var = variance(f)
    equal(var, Q(2695, 16384), "5.4 varianza dichiarata")
    equal(var, ONE - mean(f) ** 2, "5.4 varianza boolean tramite media")
    signed_total = sum((2 * s.bit_count() - 10) for s in hfamily)
    equal(signed_total, sum((2 * j - 10) * count for j, count in combinatorial.items()),
          "5.4 somma segnata via livelli")
    equal(signed_total, 460, "5.4 somma segnata dichiarata")
    individual_signed = [sum(x(s, i) for s in hfamily) for i in range(10)]
    equal(individual_signed, [46] * 10, "5.4 tutte le somme singleton H")
    alpha = singleton_vertex(f, n)
    equal(alpha, [Q(23, 512)] * 10 + [Q(11, 128)], "5.4 singleton dichiarati")
    gs = [{a for a in range(1 << n) if a & (b | zbit) == (b | zbit)} for b in (b1, b2)]
    for g in gs:
        check(g <= family, "5.4 G contenuta in F")
        equal(len(g), 1 << 5, "5.4 cardinalita G")
    indicators = [[Q(int(a in g)) for a in range(1 << n)] for g in gs]
    lam = [Q(11, 4) * (indicators[0][a] + indicators[1][a])
           + Q(1, 512) * sum(x(a, i) for i in range(10)) for a in range(1 << n)]
    ldata = check_cube(lam, n, "5.4 lambda")
    equal(ldata["singleton_fourier"], alpha, "5.4 singleton lambda = f")
    gdata = []
    for j, (indicator, b) in enumerate(zip(indicators, (b1, b2))):
        coefficients = singleton_vertex(indicator, n)
        equal(coefficients, [Q(1, 64) if (b | zbit) & (1 << i) else ZERO
                             for i in range(n)], "5.4 Fourier G" + str(j + 1))
        equal(coefficients, singleton_edges(indicator, n), "5.4 G Fourier = spigoli")
        cov = covariance(indicator, f)
        equal(cov, Q(245, 8192), "5.4 covarianza G dichiarata")
        equal(cov, (ONE - mean(f)) * Q(len(gs[j]), 1 << n), "5.4 covarianza G per inclusione")
        gdata.append({"singleton_fourier": coefficients, "covariance_with_f": cov})
    cov = covariance(f, lam)
    by_parts = Q(11, 4) * sum((g["covariance_with_f"] for g in gdata), ZERO)
    by_parts += Q(1, 512) * sum(alpha[:10], ZERO)
    equal(cov, by_parts, "5.4 covarianza diretta vs formula decomposizione")
    gap = cov - var
    equal(gap, Q(115, 131072), "5.4 divario dichiarato")
    check(gap > 0, "5.4 ostruzione stretta verificata")
    ff, fl = check_fourier(f, n, "5.4 f"), check_fourier(lam, n, "5.4 lambda")
    equal(sum((ff[s] * fl[s] for s in range(1, 1 << n)), ZERO), cov,
          "5.4 covarianza Fourier completa")

    # Seconda prova: queste sono conseguenze NECESSARIE delle equazioni di
    # divergenza e saturazione. Nessun valore di M e' scelto o presupposto.
    min_t = sum(alpha[:10], ZERO)
    coefficient_t = alpha[0] / alpha[10]
    equality_rhs = var / alpha[10]
    g_rhs = gdata[0]["covariance_with_f"] * 64
    equal(min_t, Q(115, 256), "5.4 seconda prova T minimo")
    equal(coefficient_t, Q(23, 44), "5.4 seconda prova coefficiente T")
    equal(equality_rhs, Q(245, 128), "5.4 seconda prova termine noto")
    equal(g_rhs, equality_rhs, "5.4 seconda prova medesimo termine noto")
    subtract_coefficient = Q(1, 2) - coefficient_t
    equal(subtract_coefficient, Q(-1, 44), "5.4 seconda prova sottrazione")
    check(subtract_coefficient * min_t < 0, "5.4 seconda prova incompatibilita T")
    second = {"T_lower_bound": min_t, "saturation_coefficient_T": coefficient_t,
              "saturation_right_hand_side": equality_rhs,
              "averaged_G_coefficient_T": Q(1, 2), "averaged_G_right_hand_side": g_rhs,
              "subtracted_coefficient_T": subtract_coefficient,
              "impossible_left_hand_side_upper_bound": subtract_coefficient * min_t}

    # Proposizione 4.2: cochain delle aspettative condizionate, costruita
    # dalla funzione q, senza soluzione di sistemi lineari.
    q = [Q(int(a in hfamily)) for a in range(1 << 10)]
    aq = mean(q)
    psi_prefix = []
    for i in range(10):
        comp = {}
        for p in range(1 << i):
            diffs = []
            for tail in range(1 << (9 - i)):
                base = p | (tail << (i + 1))
                diffs.append((q[base | (1 << i)] - q[base]) / 2)
            comp[p] = mean(diffs)
        psi_prefix.append(comp)
    psi = [{a: psi_prefix[i][a & ((1 << i) - 1)] for a in bases(10, i)}
           for i in range(10)]
    for comp in psi:
        for value in comp.values():
            check(value >= 0, "4.2 psi nonnegativa ogni spigolo")
    psidata = check_cochain(psi, q, 10, "4.2 psi")
    # Verifica separata dei passi di martingala E[q|prefisso i+1]-E[q|prefisso i].
    conditional = []
    for k in range(11):
        conditional.append({p: mean(q[p | (tail << k)] for tail in range(1 << (10 - k)))
                            for p in range(1 << k)})
    for a in range(1 << 10):
        telescope = ZERO
        for i in range(10):
            p_old = a & ((1 << i) - 1)
            p_new = a & ((1 << (i + 1)) - 1)
            increment = conditional[i + 1][p_new] - conditional[i][p_old]
            equal(increment, x(a, i) * psi_prefix[i][p_old],
                  "4.2 identita singolo incremento condizionale")
            telescope += increment
        equal(telescope, q[a] - aq, "4.2 telescopio per ogni vertice")
    phi = [{a: (1 + x(a, 10)) * psi[i][a & 1023] for a in bases(11, i)}
           for i in range(10)]
    phi.append({a: aq for a in bases(11, 10)})
    phidata = check_cochain(phi, f, 11, "4.2 Phi")
    check(phidata["polar"], "4.2 cochain Phi polare")
    equal(phidata["minima"], [ZERO] * 10 + [aq], "4.2 minimi Phi")
    violation = []
    df = derivative(f, n)
    for i in range(n):
        for a in bases(n, i):
            if df[i][a] == 1 and phi[i][a] != phidata["maxima"][i]:
                violation.append({"direction": i + 1, "base_mask": a,
                                  "value": phi[i][a], "directional_maximum": phidata["maxima"][i]})
    check(bool(violation), "4.2 Phi polare non satura tutti gli spigoli pivotal")
    proposition = {"a": aq, "psi_minima": psidata["minima"],
                   "psi_values_by_prefix": psi_prefix,
                   "conditional_expectations_by_prefix_length": conditional,
                   "psi_maxima": psidata["maxima"], "Phi_minima": phidata["minima"],
                   "Phi_maxima": phidata["maxima"], "Phi_bottom": phidata["bottom"],
                   "Phi_polar": phidata["polar"],
                   "divergence_equations_verified": 2048,
                   "conditional_increments_verified": 10240,
                   "saturation_failure_count": len(violation),
                   "first_saturation_failure": violation[0]}
    report = {"H_histogram_enumeration": histogram, "H_histogram_combinatorial": combinatorial,
              "H_size": len(hfamily), "F_size": len(family), "H_signed_size_sum": signed_total,
              "not_maximal_intersecting_witness_mask": zbit,
              "H_signed_coordinate_sums": individual_signed,
              "f": fdata, "lambda": ldata, "G_data": gdata,
              "covariance": cov, "variance": var, "strict_gap": gap,
              "second_proof_constraints": second, "proposition_4_2": proposition,
              "certificate_verified": True}
    data = {"f": f, "lambda": lam, "phi": phi, "gap": gap}
    return report, data


def verify_dummy(data51: dict, data54: dict) -> dict:
    # Un caso aggiunto verifica le formule; la validita' per ogni n e' analitica.
    n = 6
    f = [data51["f"][a & 31] for a in range(64)]
    phi = [{a: data51["phi"][i][a & 31] for a in bases(n, i)} for i in range(5)]
    phi.append({a: ZERO for a in bases(n, 5)})
    epsilon = Q(1, 3)
    lam = [data51["lambda"][a & 31] + epsilon * x(a, 5) for a in range(64)]
    ld = check_cube(lam, n, "4.1 dummy 5.1 lambda")
    pd = check_cochain(phi, f, n, "4.1 dummy 5.1 phi")
    weights = data51["alpha"] + [epsilon]
    equal(ld["singleton_fourier"], weights, "4.1 dummy pesi estesi")
    check(all(a > 0 for a in weights), "4.1 dummy tutti i pesi strettamente positivi")
    objective = sum((a * b for a, b in zip(weights, pd["minima"])), ZERO)
    equal(objective, Q(3), "4.1 dummy obiettivo primale")
    equal(covariance(f, lam), objective, "4.1 dummy obiettivo duale")
    check(not pd["polar"], "4.1 dummy nonpolarita persiste")
    f12 = [data54["f"][a & 2047] for a in range(4096)]
    l12 = [data54["lambda"][a & 2047] for a in range(4096)]
    fd12, ld12 = check_cube(f12, 12, "4.1 dummy 5.4 f"), check_cube(l12, 12, "4.1 dummy 5.4 lambda")
    equal(fd12["singleton_fourier"], ld12["singleton_fourier"], "4.1 dummy 5.4 singleton coincidono")
    equal(fd12["singleton_fourier"][-1], ZERO, "4.1 dummy singleton nuovo zero")
    gap12 = covariance(f12, l12) - variance(f12)
    equal(gap12, data54["gap"], "4.1 dummy 5.4 divario invariato")
    return {"5_1_dimension": 6, "5_1_new_weight": epsilon, "5_1_objective": objective,
            "5_1_nonpolar": not pd["polar"], "5_4_dimension": 12,
            "5_4_new_singleton": fd12["singleton_fourier"][-1], "5_4_gap": gap12,
            "scope": "Controllati n=6 e n=12; l'estensione a tutte le dimensioni richiede la dimostrazione."}


def json_safe(obj: Any) -> Any:
    if isinstance(obj, Q):
        return str(obj)
    if isinstance(obj, dict):
        return {str(k): json_safe(v) for k, v in obj.items()}
    if isinstance(obj, (tuple, list)):
        return [json_safe(v) for v in obj]
    return obj


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    started_ns = perf_counter_ns()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path.cwd())
    parser.add_argument("--source-tex", type=Path)
    parser.add_argument("--source-pdf", type=Path)
    parser.add_argument("--source-cary", type=Path)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    say("AUDIT COMPUTAZIONALE INDIPENDENTE CARY -- ARITMETICA RAZIONALE ESATTA")
    say("Nessun float, solver o risultato di un audit precedente e' utilizzato.")
    r51, d51 = verify_51()
    say("5.1: 32 vertici, 80 spigoli; 27 entrate valide; tutte le divergenze corrette.")
    say("5.1: minimi = " + str(r51["primal"]["minima"]))
    say("5.1: valori al fondo = " + str(r51["primal"]["bottom"]))
    say("5.1: certificati primale/duale = " + str(r51["objective"]) + "; cochain nonpolare.")
    say("5.1: tutte le 32 equazioni di divergenza (maschera : delta phi = f-mu):")
    for row in r51["all_32_vertex_equations"]:
        say(f"  {row['mask']:2d} : {str(row['divergence']):>6s} = {row['target']}")
    r54, d54 = verify_54()
    say("5.4: 2048 vertici, 11264 spigoli; |H|=|F|=" + str(r54["H_size"]) + ".")
    say("5.4: istogramma H = " + str(r54["H_histogram_enumeration"]))
    say("5.4: singleton f = " + str(r54["f"]["singleton_fourier"]))
    say("5.4: Var(f)=" + str(r54["variance"]) + "; Cov(f,lambda)=" + str(r54["covariance"]) +
        "; divario=" + str(r54["strict_gap"]) + ".")
    say("5.4: seconda prova: T >= 115/256 e (-1/44)T >= 0, incompatibili.")
    say("4.2: costruita e verificata la cochain condizionale polare su tutti gli spigoli.")
    say("4.2: minimi Phi = " + str(r54["proposition_4_2"]["Phi_minima"]))
    say("4.2: primo difetto di saturazione di questa Phi = " + str(r54["proposition_4_2"]["first_saturation_failure"]))
    rdummy = verify_dummy(d51, d54)
    say("4.1: controlli finiti dell'aggiunta di una variabile fittizia superati (n=6 e n=12).")
    elapsed_ns = perf_counter_ns() - started_ns
    provenance = {"python_version": platform.python_version(), "script_sha256": sha256(Path(__file__)),
                  "python_optimization_level": sys.flags.optimize, "elapsed_nanoseconds": elapsed_ns}
    for label, path in (("source_tex", args.source_tex), ("source_pdf", args.source_pdf),
                        ("source_cary_v5", args.source_cary)):
        if path is not None:
            provenance[label] = {"filename": path.name, "size_bytes": path.stat().st_size,
                                 "sha256": sha256(path)}
    report = {"status": "ALL_CHECKS_PASSED", "arithmetic": "fractions.Fraction; no floating point",
              "limitations": "Certificati finiti verificati. Lemmi universali, fonte v5 e quantificatori richiedono audit matematico separato.",
              "provenance": provenance, "conjecture_5_1": r51, "conjecture_5_4": r54,
              "dummy_variables": rdummy, "check_executions": sum(CHECKS.values()),
              "check_categories": dict(sorted(CHECKS.items()))}
    say("ESITO: tutti i controlli superati (" + str(sum(CHECKS.values())) + " esecuzioni esplicite).")
    say("Tempo controlli: " + str(elapsed_ns) + " nanosecondi; ottimizzazione Python=" + str(sys.flags.optimize) + ".")
    say("SHA-256 del programma: " + provenance["script_sha256"])
    say("Il verdetto matematico generale richiede i lemmi e il confronto con Cary v5.")
    json_path = args.output_dir / "risultati_verifica_Cary.json"
    log_path = args.output_dir / "esecuzione_verificatore_Cary.txt"
    json_path.write_text(json.dumps(json_safe(report), ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    log_path.write_text("\n".join(LOG) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
