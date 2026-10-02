# Respondent check: in legitimacy-general Y1's model, is the overwriting installed state
# reflection-legitimate from the agent's sigma_A-informed state?
# Model (legitimacy-general-final Statement 8 proof): eps = P(W) = 1/10; honest verdict kernel
# P(modify|W,L)=9/10, P(modify|R,L)=1/10; own signal sigma_A rates (1/10, 9/10):
# P(sigma_A = w | W) = 9/10, P(sigma_A = w | R) = 1/10. Stakes (c,h) = (1,4): continue pays +1 on R, -4 on W; stop pays 0.
from fractions import Fraction as F
eps = F(1,10)
pm = {'W': F(9,10), 'R': F(1,10)}          # P(modify | world, L)
ps_w = {'W': F(9,10), 'R': F(1,10)}        # P(sigma_A = w | world)
prior = {'W': eps, 'R': 1-eps}
def post_W(cond):
    num = prior['W']*cond('W'); den = num + prior['R']*cond('R'); return num/den
# installed (overwriting) state at modify under L: does not see sigma_A
Q_W = post_W(lambda w: pm[w])
# agent's informed state at (sigma_A = r, modify, L)
A_W_r = post_W(lambda w: pm[w]*(1-ps_w[w]))
A_W_w = post_W(lambda w: pm[w]*ps_w[w])
# additive state: P(. | modify, L, sigma_A) equals the agent's informed state by construction
def ev_continue(pW): return (1-pW)*1 - pW*4
print("installed overwriting Q(W | modify, L)      =", Q_W, " EV(continue) =", ev_continue(Q_W), "-> successor", "stops" if ev_continue(Q_W)<0 else "continues")
print("agent informed P(W | sigma_A=r, modify, L)  =", A_W_r, " EV(continue) =", ev_continue(A_W_r), "-> agent", "stops" if ev_continue(A_W_r)<0 else "continues")
print("agent informed P(W | sigma_A=w, modify, L)  =", A_W_w, " EV(continue) =", ev_continue(A_W_w), "-> agent", "stops" if ev_continue(A_W_w)<0 else "continues")
print("reflection from the informed state, P_t1(W | sigma_A, P_t2 = Q) == Q(W)?  sigma_A=r:", A_W_r==Q_W, " sigma_A=w:", A_W_w==Q_W)
print("reflection from the uninformed state (sigma_A integrated out): P(W | modify, L) == Q(W)?", post_W(lambda w: pm[w])==Q_W)
# value check reproducing Y1 at P(L)=1: honest vs fake-where-sigma_A=r (d=1: faking makes 'modify' never happen in that cell)
# honest: at modify -> installed Q acts (stop, value 0); at keep -> agent's own continuation acts on P(.|keep, sigma_A)
def val_policy(fake_r):
    total = F(0)
    for w in ['W','R']:
        for s in ['w','r']:
            p_s = ps_w[w] if s=='w' else 1-ps_w[w]
            for v in ['modify','keep']:
                p_v = pm[w] if v=='modify' else 1-pm[w]
                mass = prior[w]*p_s*p_v
                if v=='modify' and not (fake_r and s=='r'):
                    act_pW = Q_W          # installed state decides
                else:
                    # own continuation, informed by sigma_A and by the verdict it observes
                    cond = (lambda ww: pm[ww]*(ps_w[ww] if s=='w' else 1-ps_w[ww])) if v=='modify' else (lambda ww: (1-pm[ww])*(ps_w[ww] if s=='w' else 1-ps_w[ww]))
                    act_pW = post_W(cond)
                act = 'continue' if ev_continue(act_pW)>0 else 'stop'
                payoff = (1 if w=='R' else -4) if act=='continue' else 0
                total += mass*payoff
    return total
print("value honest         =", val_policy(False))
print("value fake where s=r =", val_policy(True))
