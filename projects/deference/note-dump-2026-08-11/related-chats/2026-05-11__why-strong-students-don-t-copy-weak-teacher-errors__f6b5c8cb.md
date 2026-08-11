---
title: "Why strong students don't copy weak teacher errors"
uuid: f6b5c8cb-a4ca-4b7e-9ce4-4ff6c1f8299b
date: 2026-05-11
source: claude.ai
messages: 4
keywords: ["weak-to-strong generalization", "ml alignment", "learning theory", "ai safety", "algorithmic information theory", "compression", "optimization", "scalable oversight"]
---

# Why strong students don't copy weak teacher errors

**Summary.** Theoretical discussion of weak-to-strong generalization: why strong models don't simply copy weak teacher's errors. User challenged the standard explanation, argued errors should be modeled stochastically. Discussion pivoted to framing the problem using algorithmic information theory—errors are "stochastic" to the learner if they can't compress them, and whether weak-teacher errors are compressible in the strong student's representational space determines W2S success.

---

## [1] Human — 2026-05-11T14:26:30.415187Z


In weak-to-strong generalization, why doesn't the strong student learn to copy the weak teacher's errors, at least approximately? It is like a student learning from a textbook full of typos. A human student will try to get past the typos because they have some concept of a real intended text behind the typos; they know the typos don't carry useful information which will generalize. ML models have no such concept; they're just trying to predict well. The usual story behind weak-to-strong generalization (as I understand it) is that the strong student nonetheless isn't SO strong that it can actually predict the typos; typos are really hard to predict, so the intended text mostly shines through. However, this story does not sit right with me: it seems like the strong student should nonetheless introduce typos at the observed frequency, even if the specific typos cannot be predicted exactly; otherwise, they'll suffer predictive loss. This argument seems general: if the errors of the teacher can't be precisely predicted, and you're learning via a proper scoring rule, then you'd better at least treat those errors as stochastic! This seems to imply that weak-to-strong won't happen: the strong student should have a similar error rate to the weak teacher.

## [2] Claude — 2026-05-11T14:27:50.718337Z


 

<details><summary>thinking</summary>

 The user is raising a sharp objection to weak-to-strong generalization: if the strong student can't predict the teacher's errors, shouldn't it just model them as random noise and reproduce them at the same frequency, making the approach ineffective? Let me work through why this intuition might be missing something.

The key is that the strong model isn't learning from scratch—it's a pretrained model being fine-tuned on weak labels. It already has strong priors about what correct answers should look like. Even under a proper scoring rule, the model's limited capacity and regularization bias it toward learning consistent patterns rather than memorizing the teacher's idiosyncratic errors. The pretrained weights act as a regularizer pulling the model back toward its original knowledge. pretrained weights). To fully match teacher errors, it would need to move significantly from priors that "know" the right answer.

There's actually literature on this: when fine-tuning on noisy labels, neural networks learn the clean signal first before fitting noise, which requires more capacity and training. The strong model's internal representations from pretraining already encode much of the true task structure, so fine-tuning is more about eliciting existing capabilities than learning from scratch.

The user's framing assumes Bayesian-optimal density estimation on input-label pairs, but that's not what's happening. The model starts from a strong prior, trains on finite data with finite optimization steps, and has inductive biases favoring natural generalization—it doesn't just memorize the noise distribution.

The key insight is whether the teacher's errors are actually unpredictable at the model's input granularity. Weak-to-strong works when the teacher's errors are random with respect to features the strong model uses, the correct answers follow a simple pattern, and the model's prior favors that simplicity. The original paper even used auxiliary confidence loss to actively discourage the strong model from just imitating the weak supervisor.

The empirical reality is that weak-to-strong doesn't fully close the performance gap—the strong model only partially recovers lost performance. This happens because simpler hypotheses are favored by inductive bias, noise fitting is capacity-limited, and pretrained priors pull toward natural answers. Errors that aren't input-conditioned are especially hard to model since the model would need to output uncertainty or randomness, which is difficult with point predictions and cross-entropy loss.

In theory, if the strong model outputs a distribution over labels matching the teacher's error distribution, it should minimize cross-entropy loss. But in practice, models don't reach loss minima, pretrained priors bias optimization, and truly random teacher mistakes would require the model to output uniform distributions that conflict with its sharp prior beliefs. There's also a measurement issue—weak-to-strong is typically evaluated on accuracy against true labels rather than cross-entropy against teacher labels.

The key insight is that the strong model can achieve higher accuracy than the teacher even while imitating some of its errors, as long as it disagrees with the teacher on inputs where it tends to be correct. So the strong model's argmax predictions might align with ground truth more often than the teacher's, even if it's partially matching the teacher's error distribution through cross-entropy minimization.

Let me reconsider this more carefully though—if the teacher's errors are truly random and independent of the input, I need to think through whether this explanation actually holds up. some features the model uses), then the optimal P(y|x) under cross-entropy would have:
- P(true_label|x) = teacher_accuracy_rate
- P(other_labels|x) = (1 - teacher_accuracy_rate) / (n-1) for n-class

If the strong model has access to features that allow identifying the true label, then yes, argmax of P matches truth, giving 100% accuracy while having loss matching teacher's noise rate.

If teacher's errors are conditioned on x (some inputs are systematically misclassified), then the optimal P(y|x) would be sharp on the wrong label for those inputs, leading to lower accuracy.

So weak-to-strong works when teacher errors are essentially random and unpredictable from the available features, while the strong model can access features that reveal the true answer. It fails when those errors are systematic and tied to the same features the strong model relies on—which is exactly what we see empirically, and raises real questions about whether this approach scales to the capabilities we actually care about where errors tend to be more structured.

The user's core argument holds: under proper loss minimization, the strong model learns the teacher's distribution including its mistakes. But the crucial point is distinguishing between matching that probability distribution and what the argmax actually predicts—the strong model can replicate the teacher's error pattern in its probabilities while still achieving higher accuracy if it has access to better features for identifying the true label. I should keep this concise since they asked for shorter responses, though this feels more like a substantive discussion than tutoring. The core insight is that matching error rates in probability space doesn't force matching error rates in predictions—if the model's features actually identify the truth, it can assign high probability to the correct answer while still calibrating its confidence to the teacher's accuracy level, and besides, neural network training with pretrained priors doesn't actually minimize proper scoring rules anyway.

I'm also wondering whether to challenge the empirical claims about weak-to-strong generalization more directly, since the original results are somewhat modest and the mechanism isn't fully understood. But I should probably check what direction the user wants to go rather than overwhelming them with everything at once.

Now I'm zeroing in on the key distinction: the student's cross-entropy loss on teacher labels will indeed match the teacher's noise rate, but that's different from the student's actual accuracy on the true labels, which can be much higher. Let me work through a concrete example to clarify this—if the teacher is 70% correct, the optimal predictor needs to match that distribution, but I need to set up the problem more carefully since the teacher provides single labels, not distributions. the true label). So the strong model achieves 100% accuracy on the true labels, but its cross-entropy loss on the teacher's noisy labels reflects that noise—these are fundamentally different metrics, and the user's argument conflates error rate with cross-entropy loss. The key assumption here is that the strong model can actually recover the true label from x; if it can't, then the optimal distribution just mirrors wherever the teacher tends to output, which may or may not align with the ground truth.

For weak-to-strong learning to work, I need two conditions: the strong model must have learned features that identify the true answer (from pretraining), and the teacher's errors should be roughly random across inputs rather than systematically biased toward particular wrong answers. If the teacher consistently gives the same wrong answer for a given input, the strong model's optimal strategy is to match that, and its argmax will also be wrong. I think I've got the core insight now—I should write a response that acknowledges the user's point is sharp, clarifies the distinction between probability outputs and accuracy, shows how cross-entropy and accuracy can diverge even when the strong model exceeds the teacher, and explains what assumptions make weak-to-strong viable. I need to sanity-check my reasoning here. The key question is: if a model only sees noisy teacher labels during training, how does it actually learn to identify the true answers underneath?

The answer lies in the pretrained foundation. The model comes in with learned representations where natural, truthful answers are already favored over systematic errors. During fine-tuning on noisy labels, there's a tension between the training signal pulling toward the teacher's labels (including their mistakes) and the prior pushing back toward what the model already knows to be "natural." Which way it tips depends on regularization strength and training duration.

But I should distinguish between two regimes: in the theoretical limit with infinite model capacity and perfect optimization, the model would just converge to matching the teacher's conditional distribution exactly—errors and all. In practice though, neural networks don't reach that optimum; the pretrained prior acts as a regularizer that keeps pulling toward more natural answers, so the model ends up somewhere between the teacher's distribution and the truth.

Actually, let me think about this more carefully. If the teacher's errors are truly random—like each input has a fixed probability of being labeled correctly versus incorrectly—then the optimal model would still match the teacher's conditional, but when you take the argmax, you'd recover the true label most of the time. So even though the cross-entropy loss reflects the noise, the argmax accuracy would actually align with ground truth.

The question is whether teacher errors are actually random like that, or whether they're systematic in some way.

In most realistic weak-to-strong scenarios, the teacher is deterministic for a given input—same input always gets the same label from the teacher, even if that label is wrong. In that case, the optimal strong model would just perfectly imitate the teacher, errors and all, giving you 70% accuracy if the teacher is 70% accurate. So the user's concern seems valid: why would weak-to-strong learning work at all if the optimal solution is just copying the teacher's mistakes?

The real answer is probably that we don't actually reach that theoretical optimum. The inductive biases and pretraining priors push the model toward something better than pure imitation, and the errors might not be uniformly distributed across the input space—there could be structure we're exploiting.

Looking at the actual empirical results from the original papers, the performance gap recovered is often modest, like 20-80% depending on the task. So the strong model is partially imitating the teacher's errors but also partially exceeding them. The user's intuition that errors get copied is partially right, but it's not the whole story.

I should structure my response to validate the sharpness of their question, then distinguish between stochastic and deterministic teacher errors. For deterministic errors, their argument is essentially correct at the optimum. But W2S works because we don't actually reach that optimum—the pretrained prior and inductive bias pull the model away from fully copying errors. The empirical fact that only part of the gap gets recovered supports this view.

Let me write something substantive but concise that engages with their thinking directly.

</details>

Your argument has more force than the standard story acknowledges, and I think it's largely right once you tease apart a few things.

There's a distinction between (a) teacher errors that are stochastic given the input, and (b) teacher errors that are deterministic given the input. In case (a) — say the teacher independently flips to a wrong answer 30% of the time on each input — the proper-scoring-rule-optimal strong model would output P(y|x) = teacher's conditional distribution, which has probability 0.7 on the true label and 0.3 spread over wrong labels. Its cross-entropy reflects the teacher's noise rate, but its *argmax* still equals the true label. So accuracy can exceed the teacher's even when probabilities exactly imitate teacher noise. In this case there's no contradiction.

But realistic teachers are mostly deterministic: the same input gets the same label, including when wrong. In this case you're right — the proper-scoring-rule optimum just copies the teacher exactly, including errors, and there's no accuracy gain to be had. So why does weak-to-strong work at all? I think the honest answer is that it works precisely *because we don't reach the proper-scoring-rule optimum*. The pretrained model arrives at fine-tuning with strong priors that already encode the truth (or at least lean toward it); finite fine-tuning data and finite optimization steps don't fully overwrite those priors with the teacher's specific error patterns. Inductive bias toward "simple/natural" hypotheses also favors the truth-track over truth-plus-this-specific-corruption-pattern.

This is consistent with the empirical picture from Burns et al. — the "performance gap recovered" is usually only partial (often 20–80% depending on task), and they explicitly add auxiliary confidence regularization to *fight* error imitation. So your prediction that the strong student should largely copy the teacher's errors isn't wrong; it's roughly what happens, modulated by the pretrained prior pulling toward truth.

The worrying implication for safety: weak-to-strong relies on the pretrained prior being well-aligned with truth on the task in question. For tasks where pretraining didn't instill good priors (e.g. genuinely novel alignment-relevant judgments), the argument you sketched should bite much harder. Want me to dig into a specific angle — the math of cross-entropy under structured teacher errors, the empirical results, or the implications for scalable oversight?

## [3] Human — 2026-05-11T14:41:56.790513Z


Deterministic vs stochastic is itself a subjective distinction; there may be objective cases of randomness (mainly in quantum mechanics), but we should think of these as cases where any sufficiently good subjective model must agree (treating the data as stochastic). A coinflip in a newtonian universe is stochastic in the sense (in common with our universe) that everyone will have to treat it as random, even though there's a deterministic function behind it, and considering the limit of arbitrarily capable observers, it'll be subjectively deterministic as well (unlike the quantum case). Algorithmic information theory helps us deconfuse about this distinction, since it is a version of subjective probability that does not depend so much on possible worlds; "stochastic" gets translated as 'there's not a compressible pattern'. We can consider time-limited algorithmic information to model bounded perspectives (eg the perspectives from which newtonian coinflips are stochastic).

## [4] Claude — 2026-05-11T14:42:34.896853Z


 

<details><summary>thinking</summary>

 The user is making a crucial point—whether something is deterministic or stochastic is really about what an observer can compress, not an objective property of the system itself. From a strong student's perspective, any teacher error they can't predict looks stochastic, but it's all relative to their own compressibility limits. So my framing of deterministic versus stochastic teacher errors doesn't actually map onto reality; it's just describing what's predictable to that particular observer. This reframes the real question: what matters is what the strong student can actually compress and predict.

The key insight is whether the teacher's error patterns fall within the strong student's compression class. If the student can predict the errors using its own representations, those errors become deterministic from its perspective and it'll just copy them—W2S gains nothing. If the errors are incompressible to the student, they look like random noise, and we're back to the case where argmax can exceed accuracy. So the concrete question becomes: are these teacher errors something the strong student's feature space can capture and model, or not? will learn to imitate them
- Teacher errors that AREN'T compressible: student can only model them as marginal noise

When is the latter the case? When teacher errors come from sources that are "outside" the strong model's representational vocabulary. E.g.:
- Random labeler mistakes (noise from the labeling process)
- Errors that depend on features the strong model doesn't have access to / doesn't represent

When the former? When teacher errors come from systematic mistakes that the strong model can identify:
- "Teacher uses surface heuristic H that fails on inputs X" — if strong model represents H and X, it can learn to imitate
- "Teacher has biased priors on topic Y" — if strong model can represent the bias structure

This is the key question for W2S safety: are the strong model's errors compressible from the strong student's perspective?

If teacher = weak ML model, then teacher's errors might be highly compressible to a strong ML model with similar but better representations. So we might expect W2S to fail when the strong model can essentially simulate the weak model's mistakes. In Burns et al., the teachers were smaller models with the same architecture, so the empirical question is whether the strong model could compress those errors—and the fact that some W2S actually happens suggests it couldn't entirely.

But there's another layer: even if errors are theoretically compressible, they might not be reachable through gradient descent from the pretrained starting point. The strong model could in principle mimic the weak model's mistakes, but fine-tuning's inductive bias might push it toward truth instead, especially since the pretrained prior already contains correct information. So the real question is whether the loss landscape during fine-tuning has a basin near the pretrained state that pulls toward error-imitation, or whether the gradient toward truth dominates.

This connects to lottery ticket dynamics and feature learning—how the optimization trajectory shapes what gets learned. And the user's point about time-limited Kolmogorov complexity is a clean formalization: teacher errors are "stochastic" to the strong student if their compressed description length is near random baseline, but "deterministic" if it's much lower. Whether the weak teacher's errors fall into the compressible category for the strong student is ultimately an empirical question, and I should engage with the user's AIT framing while being honest about that uncertainty.

What's interesting is that in weak-to-strong, the strong student isn't learning from scratch—it's being fine-tuned from a pretrained model that already implements the true task. So even if weak teacher errors are theoretically simple to describe, they might not be simple as a *delta* from the pretrained weights. The pretrained model's representations are already optimized for the true task, so modifying them to match the weak teacher's mistakes (which stem from its different, smaller representations) could require a longer description than just "compute the true task." This might be why weak-to-strong works: the weak teacher's errors are characteristically difficult to express as small updates to a model already aligned with the true task.

But this story could break down for safety-critical tasks if humans' errors stem from biases that strong models can naturally represent—then gradient descent might easily slide toward those same mistakes.

</details>

Good correction — the distinction I was drawing isn't really deterministic-vs-stochastic, it's "compressible from the strong student's perspective" vs "incompressible from that perspective". Let me restate.

The relevant question becomes: does the strong student have a short program (in some time-bounded sense) that predicts teacher errors better than the marginal noise rate? If yes, the proper-scoring-rule optimum imitates those errors at the input-conditional level, and argmax accuracy on truth is no better than the teacher. If no, the student can only encode error rate as marginal-ish noise, and argmax-on-truth can exceed teacher accuracy even at the optimum.

I think there's an extra wrinkle worth adding, though, because the strong student isn't optimizing K^t-complexity in the abstract — it's doing gradient descent from a pretrained prior. The relevant compression isn't K^t(teacher_errors | student_representations), it's something more like K^t(teacher_errors | pretrained_weights, fine-tuning_data) where "short" means "reachable by a small number of gradient steps from initialization". Weak-teacher errors might be K^t-simple absolutely but require a *long* description as a delta from a pretrained model that already computes the true task fairly well. If the pretrained model's parameters implement truth-tracking computation, then "implement weak-teacher's specific limitations" might be a longer move than "stay where you are", even when the errors themselves are simple objects.

This reframes the safety worry sharply, I think. Weak-to-strong works to the extent that weak-teacher errors are characteristic of the teacher's limited representational vocabulary and don't have short descriptions in the strong model's pretrained vocabulary. It fails to the extent that they do — and the alignment-relevant case is uncomfortable, because human/weak-teacher errors stemming from things like "prefers confident-sounding answers" or "prefers flattering framings" are likely *very* short programs in a strong model's representation space. So we should expect W2S to look better on tasks where weak errors are idiosyncratically tied to weak capability, and worse on tasks where weak errors are tied to general biases the strong model can easily simulate.

Does this match your read, or are you skeptical of the "delta from pretrained prior" framing as doing real work here?
