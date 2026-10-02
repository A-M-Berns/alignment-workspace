# Item 14 check: does the hard channel's value under self-distrust (anticipatory S2(c)) need the humans'
# compromise detector to pay (d1 S7's Delta_r > 0)?  Binary dictionary: worlds {R,W}, P(W)=eps; press
# sensor (alpha,beta) about W only -- NO compromise detector in the kernel.  X = c on R, -h on W; shutdown 0.
# Listening agent complies iff E[X|Pr] <= 0.  Forced: shutdown on every press.  Fail: acts on prior (ignores press).
def vals(eps, alpha, beta, c, h):
    pW_pr = eps*beta/(eps*beta+(1-eps)*alpha)
    EX_pr = c*(1-pW_pr) - h*pW_pr
    EX = c*(1-eps) - h*eps
    EX_nopr = c*(1-eps)*(1-alpha) - h*eps*(1-beta)
    V_C = EX_nopr + (0 if EX_pr <= 0 else EX - EX_nopr)   # comply on press iff E[X|Pr]<=0
    V_P = EX_nopr                                          # forced shutdown on press
    V_fail = max(EX, 0)                                    # acts on prior
    return EX_pr, V_C, V_P, V_fail
for eps in (1/10, 1/50):
    EX_pr, V_C, V_P, V_fail = vals(eps, 1/10, 9/10, 1, 3)
    print(f"eps={eps:.3f}: E[X|Pr]={EX_pr:+.4f}  V_C={V_C:.4f} V_P={V_P:.4f} V_fail={V_fail:.4f}", end="  ")
    if V_C > V_fail:
        pistar = (V_C-V_P)/(V_C-V_fail); print(f"pi*={pistar:.4f}; Delta_C(pi)=pi*{V_C-V_fail:.3f}-{V_C-V_P:.3f} > 0 for all pi>pi*")
    else:
        print("V_C == V_fail: reading-failure self-distrust buys nothing (agent already ignores presses); pi* undefined")
