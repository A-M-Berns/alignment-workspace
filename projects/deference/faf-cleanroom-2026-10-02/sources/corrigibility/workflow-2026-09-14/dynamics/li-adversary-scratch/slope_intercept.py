"""Attack on Statement 5's headline: the slope r(f,p) exceeds the odds p/(1-p) for every f>0,
and the intercept K_f = log C / log(1+f(1/p-1)) diverges as f -> 0 even with C fixed.
Also: for a FIXED f the theorem tolerates persistent miscalibration up to wrongness r/(1+r) on defied days."""
import math
p=0.05; odds=p/(1-p); C=2.0
print(f"p={p}: odds p/(1-p)={odds:.4f}")
for f in [0.5,0.1,0.01,0.001,0.0001]:
    r=math.log(1/(1-f))/math.log(1+f*(1/p-1)); K=math.log(C)/math.log(1+f*(1/p-1))
    print(f"  f={f:<7} slope r={r:.4f} (excess over odds {100*(r/odds-1):5.1f}%)  tolerated defied-day wrongness r/(1+r)={r/(1+r):.4f} vs p={p}   K_f(C=2)={K:8.1f}")
