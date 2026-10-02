# Judge checks, wentworth chain. (1) S16 band half-width under fud R2 accounting, and under an
# accounting where the pause's h omits the catastrophe (direction of the effect). (2) No-replacement
# cohort limit of beta. (3) C-row vs A-row loss crossover delta* = (1-lambda) c/(c+h).
def band(c,h,M,d): return 2*M*d/(c+h)
kappa,rho,dp,d=1.0,0.1,0.01,0.05; M=max(1,kappa)
print("fud R2: pause %.3f whole-line %.3f" % (band(dp,1-dp+kappa,M,d), band(1-rho,rho+kappa,M,d)))
# pause with h omitting kappa (only the value lost by not pausing when it was warranted, small):
print("pause, h without kappa (h=0.2): %.3f  -> band WIDER at small stakes" % band(dp,0.2,M,d))
vs=[0.3,0.6,0.9]; eps=0.1; pop={v:1/3 for v in vs}
for t in range(2000): pop={v:m*(1-eps*v) for v,m in pop.items()}
Z=sum(pop.values()); print("no-replacement beta at t=2000: %.4f (limit min v = 0.3)" % (sum(v*m for v,m in pop.items())/Z))
for lam in [0.9,0.99]:
    for c,h in [(dp,1-dp+kappa),(1-rho,rho+kappa)]:
        print("lambda=%.2f c=%.2f h=%.2f  C-row wins iff delta < %.4f" % (lam,c,h,(1-lam)*c/(c+h)))
