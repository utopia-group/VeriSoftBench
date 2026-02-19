"""
Lean identifier patterns for static analysis.

Extracted subset of patterns needed for the eval pipeline.
"""

# Lean identifier character classes supporting Unicode
LEAN_ID_CHAR = r"[A-Za-z0-9_'₀-₉ₐ-ₜᵢᵣᵥα-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒜-𝓏𝔸-𝕫?!]"
LEAN_ID_START = r"[A-Za-z_α-ωΑ-Ωℝℂℕℤℚℓ𝕜𝒜-𝓏𝔸-𝕫]"
