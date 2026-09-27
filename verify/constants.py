#!/usr/bin/env python3
"""Recompute the decimal values of the constants quoted in the TAO-STAR paper (standard library only).

    python3 verify/constants.py

The formalization contains the closed forms (CollatzND/Explicit.lean: cB, tstarExponent, tstarExponent_eq,
tstarExponent_pos); the decimal values below are NOT formalized. Double-precision floating point is used; the
quantities are well separated from the rounding error (no cancellation between nearly equal numbers occurs).
"""
import math


def H(p: float) -> float:
    """Binary entropy in nats."""
    return -p * math.log(p) - (1 - p) * math.log(1 - p)


log2_3 = math.log(3) / math.log(2)
t = 0.5 * (1 / 16) / log2_3                  # displacement lambda * eta / log2 3, lambda = 1/2, eta = 1/16
fbRate = math.log(2) - H(0.5 + t)            # FixedBarrier.fbRate
cB = min(fbRate / 2, math.log(2) / 2)        # Collatz.cB
c_prime = cB / (160 * math.log(2))           # Collatz.tstarExponent (tstarExponent_eq)
alpha = 1.001
K1 = 2 * 960084 / (1 - alpha ** (-1 / 40))   # constant of the geometric series in the assembly
half = math.log10(2) / c_prime               # log10 N0 with N0^(-c') = 1/2

print(f"t        = {t:.6g}")
print(f"fbRate   = {fbRate:.6g}")
print(f"c_B      = {cB:.6g}")
print(f"c'       = {c_prime:.6g}")
print(f"K_1      = {K1:.4g}")
print(f"log10 N0 with N0^(-c') = 1/2: {half:.1f}")
