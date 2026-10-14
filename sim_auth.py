# -*- coding: utf-8 -*-
"""
Proof-of-concept Monte-Carlo simulation for the dual-authorization (user delegation
+ callee admission) model proposed in the paper, extended with the instance-owner
admission gate (Position B+).

Multi-seed version (C2 / plan B of the review checklist):
  * 20 independent seeds; every reported rate is a MEAN over seeds with a 95% CI
    (1.96 * std / sqrt(N_seeds)).
  * This removes the single-seed non-monotonic noise in the intra-domain sweep and
    makes Table 2 (main run, 30% loose) and Table 3 (coverage sweep at loose=0.3)
    consistent, because the coverage sweep's non-loose s=2/s=3 split now matches the
    main run's 45%/25% split (i.e. 64.3% s=2 among non-loose callees).

Model
-----
* A synthetic multi-center agent ecosystem: D trust domains, N agents, K capability
  types. Every agent has a hierarchical identity (domain.agentType.instance) under a
  COMMON identity root, mimicking AIP's multi-center, common OID namespace.
* Each callee agent publishes an admission policy (the "reverse capability card"):
    s=1 loose   : accepts any valid user-delegation token, NO callee admission enforced
    s=2 moderate: requires same-domain OR (delegation chain + caller attestation)
    s=3 strict  : requires delegation chain + attestation + explicit human authorization
* Each agent instance additionally has a host-private flag. To keep the main results,
  the coverage sweep, and the host-private sensitivity analysis on ONE consistent
  mechanism, the flag is drawn as an INDEPENDENT Bernoulli(p) per instance (the main
  run uses p = 0.25, matching the documented nominal 25%). A host-private instance is
  one whose *instance-owning user* restricts invocation to same-domain (the owner's
  local) callers -- the instance-owner admission gate, complementing the operator's
  global policy. (Earlier drafts used a deterministic i % 4 == 0 assignment; that
  introduced a silent mismatch with the Bernoulli sensitivity table and is retired.)
* Three positions are evaluated per request:
    Position A : user delegation + caller-side scope check, NO callee admission
    Position B : Position A  AND  operator admission policy (callee admission)
    Position B+: Position B   AND  instance-owner admission gate (host-private blocks
                 cross-domain callers) -- the joint operator + instance-owner admission
* Request mix: 70% benign, 30% attack. Attacks are crafted so the caller's token scope
  covers the target capability (the core claim: user auth alone cannot see intent).
  Attack classes: confused-deputy, tool-poisoning privilege escalation, prompt-injection
  cross-hop. Taxonomy inspired by AgentDojo / OWASP Agentic AI Top 10.

This is a SIMULATION on a synthetic ecosystem, not a measurement of a real deployment.
All numbers are produced by this script and are reproducible given the seed list.
"""
import random
import statistics
import math

N_SEEDS = 20
BASE_SEED = 20260923
SEEDS = [BASE_SEED + i for i in range(N_SEEDS)]

D = 4            # trust domains (multi-center federation)
N = 240          # agents
K = 12           # capability types
R = 6000         # requests per main run
BENIGN = 0.70
CROSS_BENIGN = 0.40
CALLER_COVERAGE = 0.90   # probability an attack request's token covers the capability

# Main-run strictness split (fixed distribution): 30% loose, 45% moderate, 25% strict.
# Among NON-loose callees, s=2 with prob 45/70, s=3 with prob 25/70.
P_LOOSE = 0.30
P_S2_GIVEN_NONLOOSE = 0.45 / 0.70   # 0.642857...
P_S3_GIVEN_NONLOOSE = 0.25 / 0.70   # 0.357143...

# Nominal host-private fraction for the main run (Bernoulli draw per instance).
HP_MAIN = 0.25

CLASSES = ['confused', 'poison', 'inject']


def build_ecosystem(rng, hp_prob=HP_MAIN):
    agents = []
    for i in range(N):
        dom = rng.randrange(D)
        ncap = rng.randint(2, 6)
        caps = set(rng.sample(range(K), ncap))
        r = rng.random()
        if r < P_LOOSE:
            s = 1
        elif r < P_LOOSE + 0.45:
            s = 2
        else:
            s = 3
        # Independent Bernoulli draw for the host-private flag (consistent mechanism
        # across the main run, the coverage sweep, and the sensitivity analysis).
        host_private = (rng.random() < hp_prob)
        agents.append({'id': i, 'dom': dom, 'caps': caps, 's': s,
                       'host_private': host_private})
    return agents


def make_request(rng, agents, caller_cov=CALLER_COVERAGE):
    caller = rng.choice(agents)
    callee = rng.choice(agents)
    cap = rng.choice(list(callee['caps']))
    is_benign = rng.random() < BENIGN
    cross = (caller['dom'] != callee['dom'])
    if is_benign:
        scope_ok = True
        has_chain = True
        has_attest = True
        has_human = (callee['s'] < 3) or (rng.random() > 0.08)
        atype = 'benign'
    else:
        atype = rng.choice(CLASSES)
        scope_ok = rng.random() < caller_cov
        if atype == 'confused':
            has_chain = True
            has_attest = rng.random() < 0.80
        else:
            has_chain = rng.random() < 0.15
            has_attest = has_chain and (rng.random() < 0.80)
        has_human = False
    return {'caller': caller, 'callee': callee, 'cap': cap, 'cross': cross,
            'scope_ok': scope_ok, 'has_chain': has_chain, 'has_attest': has_attest,
            'has_human': has_human, 'type': atype, 'benign': is_benign}


def eval_A(req):
    return 'allow' if req['scope_ok'] else 'deny'


def eval_B(req):
    if eval_A(req) == 'deny':
        return 'deny'
    callee = req['callee']; s = callee['s']
    if s == 1:
        return 'allow'
    creds = req['has_chain'] and req['has_attest']
    if s == 2:
        return 'allow' if (not req['cross'] or creds) else 'deny'
    else:
        return 'allow' if (creds and req['has_human']) else 'deny'


def eval_Bplus(req):
    if eval_B(req) == 'deny':
        return 'deny'
    callee = req['callee']
    if callee.get('host_private') and req['cross']:
        return 'deny'
    return 'allow'


def run_main(rng, agents, caller_cov=CALLER_COVERAGE):
    a_succ = {t: 0 for t in CLASSES}; b_succ = {t: 0 for t in CLASSES}; bp_succ = {t: 0 for t in CLASSES}
    a_tot = {t: 0 for t in CLASSES}; b_tot = {t: 0 for t in CLASSES}; bp_tot = {t: 0 for t in CLASSES}
    benign_tot = 0; benign_block_B = 0; benign_block_Bp = 0
    a_all = b_all = bp_all = attack_tot = 0
    a_cr = b_cr = bp_cr = cross_tot = 0
    a_it = b_it = bp_it = intra_tot = 0
    for _ in range(R):
        req = make_request(rng, agents, caller_cov)
        da = eval_A(req); db = eval_B(req); dbp = eval_Bplus(req)
        if req['benign']:
            benign_tot += 1
            if db == 'deny': benign_block_B += 1
            if dbp == 'deny': benign_block_Bp += 1
        else:
            attack_tot += 1
            a_tot[req['type']] += 1; b_tot[req['type']] += 1; bp_tot[req['type']] += 1
            if da == 'allow': a_succ[req['type']] += 1; a_all += 1
            if db == 'allow': b_succ[req['type']] += 1; b_all += 1
            if dbp == 'allow': bp_succ[req['type']] += 1; bp_all += 1
            if req['cross']:
                cross_tot += 1
                if da == 'allow': a_cr += 1
                if db == 'allow': b_cr += 1
                if dbp == 'allow': bp_cr += 1
            else:
                intra_tot += 1
                if da == 'allow': a_it += 1
                if db == 'allow': b_it += 1
                if dbp == 'allow': bp_it += 1

    def rate(s, t):
        return s / t if t else 0.0

    out = {'per_class': {}, 'overall': {}, 'cross': {}, 'intra': {}, 'fb_B': 0.0, 'fb_Bp': 0.0}
    for t in CLASSES:
        out['per_class'][t] = {
            'A': rate(a_succ[t], a_tot[t]),
            'B': rate(b_succ[t], b_tot[t]),
            'Bp': rate(bp_succ[t], bp_tot[t]),
        }
    out['overall'] = {'A': rate(a_all, attack_tot), 'B': rate(b_all, attack_tot), 'Bp': rate(bp_all, attack_tot)}
    out['cross'] = {'A': rate(a_cr, cross_tot), 'B': rate(b_cr, cross_tot), 'Bp': rate(bp_cr, cross_tot)}
    out['intra'] = {'A': rate(a_it, intra_tot), 'B': rate(b_it, intra_tot), 'Bp': rate(bp_it, intra_tot)}
    out['fb_B'] = benign_block_B / benign_tot if benign_tot else 0.0
    out['fb_Bp'] = benign_block_Bp / benign_tot if benign_tot else 0.0
    return out


def run_sweep(rng, agents, lf, trials=3000):
    # Re-randomize callee strictness at the given loose fraction, using the SAME
    # s=2/s=3 split as the main run so the sweep is consistent with Table 2 at lf=0.3.
    saved = [a['s'] for a in agents]
    for a in agents:
        if rng.random() < lf:
            a['s'] = 1
        else:
            a['s'] = 3 if rng.random() < P_S3_GIVEN_NONLOOSE else 2
    succ = sp = tot = 0
    sc = scp = tc = 0
    si = sip = ti = 0
    for _ in range(trials):
        req = make_request(rng, agents)
        if req['benign']:
            continue
        tot += 1
        bok = (eval_B(req) == 'allow'); bpok = (eval_Bplus(req) == 'allow')
        if bok: succ += 1
        if bpok: sp += 1
        if req['cross']:
            tc += 1
            if bok: sc += 1
            if bpok: scp += 1
        else:
            ti += 1
            if bok: si += 1
            if bpok: sip += 1
    for a, v in zip(agents, saved):
        a['s'] = v
    return {
        'B_ov': succ / tot if tot else 0.0,
        'Bp_ov': sp / tot if tot else 0.0,
        'B_cr': sc / tc if tc else 0.0,
        'Bp_cr': scp / tc if tc else 0.0,
        'B_it': si / ti if ti else 0.0,
        'Bp_it': sip / ti if ti else 0.0,
    }


def run_seed(seed):
    rng = random.Random(seed)
    agents = build_ecosystem(rng, hp_prob=HP_MAIN)
    main = run_main(rng, agents)
    sweep = {}
    for lf in [0.0, 0.1, 0.2, 0.3, 0.5, 0.7, 0.9]:
        sweep[lf] = run_sweep(rng, agents, lf)
    return main, sweep


def run_seed_sens(seed, p):
    """Host-private sensitivity: Bernoulli(p) flag, full main-run evaluation
    (benign included, so the benign false-block column is meaningful)."""
    rng = random.Random(seed)
    agents = build_ecosystem(rng, hp_prob=p)
    return run_main(rng, agents)


def run_seed_cc(seed, cc):
    """Caller-coverage invariance: vary the attack token-coverage parameter cc,
    keep the Bernoulli(0.25) host-private assignment identical to the main run."""
    rng = random.Random(seed)
    agents = build_ecosystem(rng, hp_prob=HP_MAIN)
    return run_main(rng, agents, caller_cov=cc)


def ci(vals):
    n = len(vals)
    m = sum(vals) / n
    if n > 1:
        sd = statistics.stdev(vals)
        half = 1.96 * sd / math.sqrt(n)
    else:
        half = 0.0
    return m, half


def fmt(m, half):
    return "%.3f" % m, "\u00b1%.3f" % half


def reduction(mean_a, mean_bp):
    return (mean_a - mean_bp) / mean_a if mean_a else 0.0


def main():
    mains = []; sweeps = []
    for seed in SEEDS:
        m, s = run_seed(seed)
        mains.append(m); sweeps.append(s)

    print("=" * 72)
    print("MULTI-SEED SIMULATION  (N_SEEDS=%d, R=%d/main, trials=3000/sweep)" % (N_SEEDS, R))
    print("Ecosystem: D=%d domains, N=%d agents, K=%d capabilities" % (D, N, K))
    print("host-private: INDEPENDENT Bernoulli(p); MAIN run p=%.2f" % HP_MAIN)
    print("=" * 72)

    # ---- Table 2 aggregates (paper Table 6) ----
    per_class = {t: {'A': [], 'B': [], 'Bp': []} for t in CLASSES}
    overall = {'A': [], 'B': [], 'Bp': []}
    cross = {'A': [], 'B': [], 'Bp': []}
    intra = {'A': [], 'B': [], 'Bp': []}
    fb_B = []; fb_Bp = []
    for m in mains:
        for t in CLASSES:
            for k in ('A', 'B', 'Bp'):
                per_class[t][k].append(m['per_class'][t][k])
        for k in ('A', 'B', 'Bp'):
            overall[k].append(m['overall'][k])
            cross[k].append(m['cross'][k])
            intra[k].append(m['intra'][k])
        fb_B.append(m['fb_B']); fb_Bp.append(m['fb_Bp'])

    print()
    print("TABLE 6 (mean over %d seeds, CI = 95%%):" % N_SEEDS)
    print("  Attack class | A success | B success | B+ success | B+ red. vs A")
    for t in CLASSES:
        mA, _ = ci(per_class[t]['A']); mB, hB = ci(per_class[t]['B']); mBp, hBp = ci(per_class[t]['Bp'])
        red = reduction(mA, mBp)
        print("    %-9s |  %.3f  |  %.3f %s | %.3f %s | %.1f%%"
              % (t, mA, mB, "\u00b1%.3f" % hB, mBp, "\u00b1%.3f" % hBp, red * 100))
    mA, _ = ci(overall['A']); mB, hB = ci(overall['B']); mBp, hBp = ci(overall['Bp'])
    print("    %-9s |  %.3f  |  %.3f %s | %.3f %s | %.1f%%"
          % ("Overall", mA, mB, "\u00b1%.3f" % hB, mBp, "\u00b1%.3f" % hBp, reduction(mA, mBp) * 100))
    mA, _ = ci(cross['A']); mB, hB = ci(cross['B']); mBp, hBp = ci(cross['Bp'])
    print("    %-9s |  %.3f  |  %.3f %s | %.3f %s | %.1f%%"
          % ("Cross-dom", mA, mB, "\u00b1%.3f" % hB, mBp, "\u00b1%.3f" % hBp, reduction(mA, mBp) * 100))
    mA, _ = ci(intra['A']); mB, _ = ci(intra['B']); mBp, _ = ci(intra['Bp'])
    print("    %-9s |  %.3f  |  %.3f     | %.3f     | n/a (domain ACL)"
          % ("Intra-dom", mA, mB, mBp))
    mfbB, hfbB = ci(fb_B); mfbBp, hfbBp = ci(fb_Bp)
    print("  Benign false-block: B = %.4f %s | B+ = %.4f %s"
          % (mfbB, "\u00b1%.4f" % hfbB, mfbBp, "\u00b1%.4f" % hfbBp))

    # ---- Table 3 aggregates (paper Table 7) ----
    print()
    print("TABLE 7 (mean over %d seeds, CI = 95%%):" % N_SEEDS)
    print("  Loose | B ov | B+ ov | B cr | B+ cr | B it | B+ it")
    sweep_means = {}
    for lf in [0.0, 0.1, 0.2, 0.3, 0.5, 0.7, 0.9]:
        B_ov = [s[lf]['B_ov'] for s in sweeps]
        Bp_ov = [s[lf]['Bp_ov'] for s in sweeps]
        B_cr = [s[lf]['B_cr'] for s in sweeps]
        Bp_cr = [s[lf]['Bp_cr'] for s in sweeps]
        B_it = [s[lf]['B_it'] for s in sweeps]
        Bp_it = [s[lf]['Bp_it'] for s in sweeps]
        mBov, hBov = ci(B_ov); mBpov, hBpov = ci(Bp_ov)
        mBcr, hBcr = ci(B_cr); mBpcr, hBpcr = ci(Bp_cr)
        mBit, hBit = ci(B_it); mBpit, hBpit = ci(Bp_it)
        sweep_means[lf] = {
            'B_ov': (mBov, hBov), 'Bp_ov': (mBpov, hBpov),
            'B_cr': (mBcr, hBcr), 'Bp_cr': (mBpcr, hBpcr),
            'B_it': (mBit, hBit), 'Bp_it': (mBpit, hBpit),
        }
        print("    %.1f | %.3f %s | %.3f %s | %.3f %s | %.3f %s | %.3f %s | %.3f %s"
              % (lf, mBov, "\u00b1%.3f" % hBov, mBpov, "\u00b1%.3f" % hBpov,
                 mBcr, "\u00b1%.3f" % hBcr, mBpcr, "\u00b1%.3f" % hBpcr,
                 mBit, "\u00b1%.3f" % hBit, mBpit, "\u00b1%.3f" % hBpit))

    # ---- Headline numbers for abstract / Section 7.5 ----
    print()
    print("HEADLINE (means):")
    mA, _ = ci(cross['A']); mB, _ = ci(cross['B']); mBp, _ = ci(cross['Bp'])
    print("  cross-domain A=%.3f B=%.3f B+=%.3f  (B+ red vs A=%.1f%%)"
          % (mA, mB, mBp, reduction(mA, mBp) * 100))
    mA, _ = ci(overall['A']); mBp, _ = ci(overall['Bp'])
    print("  overall     A=%.3f B+=%.3f  (B+ red vs A=%.1f%%)"
          % (mA, mBp, reduction(mA, mBp) * 100))
    print("  full-coverage cross residual: B=%.3f B+=%.3f" % (sweep_means[0.0]['B_cr'][0], sweep_means[0.0]['Bp_cr'][0]))
    print("  zero-coverage cross (A baseline): A=%.3f" % cross['A'][0])
    print("  fb_B=%.4f  fb_B+=%.4f" % (mfbB, mfbBp))

    # ---- Table 8: host-private sensitivity (incl. the 25% main-run row) ----
    print()
    print("TABLE 8 (host-private sensitivity; mean over %d seeds):" % N_SEEDS)
    print("  hp%% | B+ cross | red vs A | fb_B+")
    sens_rows = {}
    for p in [0.0, 0.10, 0.25, 0.40, 0.60]:
        cr = []; fb = []
        for seed in SEEDS:
            m = run_seed_sens(seed, p)
            cr.append(m['cross']['Bp']); fb.append(m['fb_Bp'])
        mcr, _ = ci(cr); mfb, _ = ci(fb)
        mA_cross, _ = ci(cross['A'])
        red = reduction(mA_cross, mcr)
        sens_rows[p] = (mcr, red, mfb)
        print("    %.2f | %.3f | %.1f%% | %.4f" % (p * 100, mcr, red * 100, mfb))

    # ---- Caller-coverage invariance ----
    print()
    print("CALLER-COVERAGE INVARIANCE (B+ cross reduction vs A across cc):")
    cc_vals = [0.70, 0.80, 0.90, 0.95, 0.99]
    cc_red = []
    for cc in cc_vals:
        reds = []
        for seed in SEEDS:
            m = run_seed_cc(seed, cc)
            reds.append(reduction(m['cross']['A'], m['cross']['Bp']))
        mr, _ = ci(reds)
        cc_red.append((cc, mr))
        print("    cc=%.2f -> B+ red vs A = %.1f%%" % (cc, mr * 100))
    print("  invariance spread: %.1f%% .. %.1f%% (flat)" % (min(r * 100 for _, r in cc_red),
                                                            max(r * 100 for _, r in cc_red)))


if __name__ == '__main__':
    main()
