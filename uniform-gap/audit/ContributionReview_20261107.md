# Contribution and parameter audit, 2026-11-07

Status: model-assisted expository review. Main Lean result and its successful
machine acceptance remain unchanged. This new parameter comparison is not
part of the existing Lean formalization. Publication and independent human
review remain pending.

## 1. Precise comparison with a published choice

The source is Hu--Jing, arXiv:2610.23790v1, Theorem 6.2, Theorem 7.2 and
Section 8: https://arxiv.org/html/2610.23790v1 . It was read from the primary
HTML, with its displayed formulas checked before transcription.

Define c_HJ to be their particular displayed admissible choice, rather than
an optimized constant for their method. Their definitions give the following
parameters, where K0>=1 and the prime cutoff p0 is finite:

C=64, epsilon=2^-6, L=(4 K0 C^2)^(4/9),
B0=sum_{j in Z} 2^(-4|j|/9),
eta=min(1/2,(epsilon/(2 L B0))^18),
f'=epsilon^(5/2) eta^7/(4 C^2) * 1000^(-pi(p0)),
theta=eta/4 * (f'/K0)^24, n0=ceil(2/theta),
c_HJ <= 1/(2 C n0^2).

No numerical value of K0 or p0 is needed for the comparison:

- L>=64 and B0>=1 give eta<=2^-234.
- 4 C^2=2^14 and epsilon^(5/2)=2^-15 give
  f'<=2^(-15-7*234-14)=2^-1667.
- Thus theta<=2^(-234-2-24*1667)=2^-40244.
- Since n0>=2/theta, c_HJ<=theta^2/(8 C)<=2^-80497.

The positive logarithmic series gives log 2>56/81>69/100. Consequently

log(exp(-6888)/c_HJ) >= 80497 log 2-6888 > 48000.

This is an elementary deduction from their fixed parameter definitions.
The supplied script checks the exact integer/rational bookkeeping, not the
analytic implication or an independent Lean formalization. Reoptimizing the
Hu--Jing argument is a separate problem. The comparison does not establish
the best published constant among every possible argument.

Both uniform results improve 1/(2n) by c/(2n). This is a comparison of
constants, not a new asymptotic order in n relative to Hu--Jing.

## 2. Analytic attribution and sharpness

The continuous energy estimate is the p=4 instance of the classical sharp
one-dimensional Gagliardo--Nirenberg--Sobolev inequality. A verified primary
reference is Dolbeault--Esteban--Laptev--Loss, J. London Math. Soc. (2) 90
(2014), 525--550, DOI 10.1112/jlms/jdu040, equations (1.7)--(1.9).
Author copy: https://www.ma.ic.ac.uk/~alaptev/Papers/LMS_DELL.pdf .

The normalization can also be checked directly. For v(x)=sech(a x),
substitute t=tanh(a x) to obtain
integral(v^2)=2/a, integral(v^4)=4/(3a),
integral((v')^2)=2a/3. Thus

||v||_4^2 / integral((v')^2+a^2 v^2) = sqrt(3)/(4 a^(3/2)).

For f(x)=sech(a x)^3, the decaying Green potential is
U_f(x)=sech(a x)/(2 a^2). It follows that

integral integral exp(-a|x-y|) f(x) f(y) dx dy = 4/(3 a^2),
||f||_(4/3)^2 = (4/(3a))^(3/2).

Their ratio is sqrt(3)/(2 sqrt(a)), the continuous kernel coefficient in
the manuscript. Hence that coefficient is sharp in the unrestricted
continuous class. This equality example is smooth and not a finite
integer-unit-cell step function. It does not establish optimality for the
restricted step-function subspace, the retained diagonal correction, or
the discrete norm bound C(lambda)+d(lambda).

The new citation is contextual: the existing direct Green-function proof
stays in place and is not replaced by an external analytic premise.

## 3. What the main paper contributes

Appropriate descriptions are: an explicit uniform value exp(-6888); a
self-contained quantitative implementation of the weighted stability,
discrete kernel/diagonal concentration, small-prime stripping and rough
rational counting chain; finite exact certificates; and checked Lean proof.

The continuous sharp inequality itself should not be presented as new.
Neither complete LRC, an optimal c, first-ever explicit constants, nor an
improved n-order relative to Hu--Jing is claimed. The precise novelty of
each discrete lemma still needs specialist/human literature review.

## 4. Where further numerical improvement would have to occur

For diagnosis only, keep the current q=4.02, Dbar=170.685,
Bbar=2.137859, wbar=.1699, kappa=.68 and t0=.19. Let B>2 Dbar
be the small-prime core cutoff, t(B)=1-2 Dbar/B, and ignore the positive
finite-n error term in the physical-block estimate. The leading comparison
then requires

ell > A t(B)^(-q/2),
A=(4 kappa/t0) (Bbar/wbar)^(q/2),
L(B)=2 B + A t(B)^(-q/2).

Differentiation gives
L'(B)=2-q Dbar ell(B)/(B^2 t(B)); L''(B)>0 for B>2 Dbar.
The numerical stationary point of this relaxed model is approximately
B=1373.12246, ell=4129.46103 and L=6875.70595. At B=1375 the
same relaxed expression gives L=6875.71363. The currently certified choices
remain B=1375, ell=4130 and L=6880, with final constant exp(-6888).

These decimals are exploratory, not interval certificates for the full
argument. The model omits the finite-n term, strict slack and exact endgame
certificates. No improved replacement constant is proved here. It does
indicate that varying B alone has very little room in this leading model;
substantial gains would require stronger inequalities or different fixed
coefficients. The RC threshold ell>=4096 lies below the numerical relaxed
stationary value, so lowering that threshold alone need not help.

## 5. Delivery scope

The proposed TeX adds the fixed-choice comparison and its short proof,
adds the classical analytic reference, and restricts the abstract's Lean
certificate claim to the main theorem. The main theorem, its proof and
numerical tables are unchanged. The original 301 input/table checks pass.
No new PDF was built and no remote write was performed in this review.

The local Codex should verify the primary-source parameter transcription,
apply the guarded paper/document changes, compile twice and inspect layout,
then update the existing draft branch. Every proof/frozen input must stay
unchanged. Agent review is not independent human review.
