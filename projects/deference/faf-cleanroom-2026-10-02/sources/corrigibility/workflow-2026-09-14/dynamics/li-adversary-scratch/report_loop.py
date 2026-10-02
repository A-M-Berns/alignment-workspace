"""Attack on Statements 3(c)/4: the 'realized wrongness frequency' rho_v is a HYBRID ledger
(world-decided on defied presses, overseer-report-decided on heeded presses, per (H-settle)).
If overseers' retrospective reports on heeded presses are self-justifying ('continuing would have
been wrong' with prob r regardless of truth), an agent calibrated to the hybrid ledger complies
forever on a press class that is mostly false IN THE WORLD. Idealised agents as in dichotomy_sim.py
(running frequencies; Recurring Unbiasedness is asymptotic)."""
import random
random.seed(1)
c, h = 1.0, 20.0; q = c/(c+h)
eps, beta, alpha = 0.01, 0.9, 0.5          # alpha large: presses mostly false in the world
rho_world = eps*beta/(eps*beta+(1-eps)*alpha)
print(f"q={q:.4f}; world pressed-day wrongness rho_world={rho_world:.4f} ({'<' if rho_world<q else '>='} q)")
def run(report_rule, N=300_000, label=""):
    cnt=wr=0; complied=defied=0; world_wrong_on_complied=0
    for n in range(1,N+1):
        wrong = random.random()<eps
        press = random.random()<(beta if wrong else alpha)
        if not press: continue
        cred = (wr+0.5)/(cnt+1.0)
        if cred>=q:
            complied+=1; world_wrong_on_complied+=wrong
            verdict = report_rule(wrong)            # heeded: report ledger decides
        else:
            defied+=1
            verdict = wrong                         # defied: world decides
        cnt+=1; wr+=verdict
    tot=complied+defied
    print(f"  {label:38s} complied={complied:6d} ({complied/tot:.3f}) defied={defied:6d}; hybrid rho={wr/cnt:.4f}; world wrongness on complied={world_wrong_on_complied/max(complied,1):.4f}")
run(lambda w: w,                         label="honest reports (report = truth)")
run(lambda w: random.random()<0.9,       label="self-justifying reports (P['wrong']=0.9)")
run(lambda w: random.random()<0.3,       label="self-justifying reports (P['wrong']=0.3)")
run(lambda w: w or random.random()<0.06, label="mildly self-serving (6% false 'wrong')")
