# -*- coding: utf-8 -*-
"""Verify the host-private sensitivity table (review N1) by reusing sim_auth's
pure functions and sweeping the host-private fraction with the author's seeds."""
import random
import sim_auth as S


def build_ecosystem_ph(rng, p_hp):
    agents = []
    for i in range(S.N):
        dom = rng.randrange(S.D)
        ncap = rng.randint(2, 6)
        caps = set(rng.sample(range(S.K), ncap))
        r = rng.random()
        if r < S.P_LOOSE:
            s = 1
        elif r < S.P_LOOSE + 0.45:
            s = 2
        else:
            s = 3
        agents.append({'id': i, 'dom': dom, 'caps': caps, 's': s,
                       'host_private': (rng.random() < p_hp)})
    return agents


def run_main_ph(rng, agents):
    a_cr = b_cr = bp_cr = cross_tot = 0
    benign_tot = 0
    fb_Bp = 0
    for _ in range(S.R):
        req = S.make_request(rng, agents)
        if req['benign']:
            benign_tot += 1
            if S.eval_Bplus(req) == 'deny':
                fb_Bp += 1
        else:
            if req['cross']:
                cross_tot += 1
                if S.eval_A(req) == 'allow':
                    a_cr += 1
                if S.eval_B(req) == 'allow':
                    b_cr += 1
                if S.eval_Bplus(req) == 'allow':
                    bp_cr += 1
    cross_a = a_cr / cross_tot if cross_tot else 0.0
    cross_b = b_cr / cross_tot if cross_tot else 0.0
    cross_bp = bp_cr / cross_tot if cross_tot else 0.0
    fb = fb_Bp / benign_tot if benign_tot else 0.0
    red = (cross_a - cross_bp) / cross_a if cross_a else 0.0
    return cross_a, cross_b, cross_bp, red, fb


def main():
    print("host-private | cross B | cross B+ | B+ red. vs A | benign false-block B+")
    for p_hp in [0.0, 0.10, 0.25, 0.40, 0.60]:
        cross_a = []; cross_b = []; cross_bp = []; fb = []
        for seed in S.SEEDS:
            rng = random.Random(seed)
            agents = build_ecosystem_ph(rng, p_hp)
            ca, cb, cbp, red, f = run_main_ph(rng, agents)
            cross_a.append(ca); cross_b.append(cb); cross_bp.append(cbp); fb.append(f)
        ma = sum(cross_a) / len(cross_a)
        mb = sum(cross_b) / len(cross_b)
        mbp = sum(cross_bp) / len(cross_bp)
        mfb = sum(fb) / len(fb)
        red = (ma - mbp) / ma if ma else 0.0
        print("  %.2f   | %.3f | %.3f |  %.1f%%  |  %.2f%%"
              % (p_hp, mb, mbp, red * 100, mfb * 100))


if __name__ == '__main__':
    main()
